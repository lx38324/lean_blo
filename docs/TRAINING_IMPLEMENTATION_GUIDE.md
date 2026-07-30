# OUSVR-BLO 训练实现交接说明

本文面向负责训练代码、优化器接线、日志与实验执行的工程角色。目标不是复述全部证明，而是说明：实现必须暴露哪些量、哪些分支必须严格执行、哪些工程改动会使当前定理失效，以及如何判断一条训练轨道是否与已验证的 Lean 理论一致。

## 1. 先确认理论覆盖的对象

当前理论分析的是一个 restricted/local fixed-penalty surrogate：

$$
P(z)=F(z)+\lambda\bigl(h(z)-v(z)\bigr),
\qquad z=(x,y).
$$

其中：

- $x$ 是上层变量，例如 data/task mixing weights、curriculum variables、routing hyperparameters；
- $y$ 是主训练变量，例如 LoRA、adapter、prompt 或 small-head 参数；
- $\xi$ 是用于近似 lower response 的 value anchor；
- $h$ 是一个在分析阶段内固定的局部 lower surrogate；
- $v$ 是该 restricted/local surrogate 的 represented value function。

当前定理不覆盖原始非凸下层问题的全局最优性，也不覆盖一般 projected main-variable update。

## 2. 四个不可违反的实现约束

### 2.1 一个分析阶段内固定目标

在一个理论 horizon 内，以下对象应保持固定：

$$
\lambda,\qquad h,\qquad v,\qquad \bar\xi.
$$

若使用 proximal surrogate

$$
h_\rho(x,\xi;\bar\xi)
=
\mathcal L_{\mathrm{train}}(x,\xi)
+
\frac\rho2\|\xi-\bar\xi\|^2,
$$

则 reference $\bar\xi$ 不应每轮改变。可以按 stage 或 epoch 刷新，但每次刷新都应视为新分析阶段；否则需要显式加入 objective-drift error，当前主定理不会自动吸收这种变化。

### 2.2 主变量更新必须与欧氏更新一致

当前 trajectory theorem 使用：

$$
z_{t+1}-z_t=-\eta(G_t+E_t).
$$

因此可接受的实现包括：

- 对无约束参数直接做欧氏更新；
- 用 logits 等无约束参数化表示 simplex 权重，再在 logits 上更新；
- 任何与上述更新恒等的重参数化。

若直接执行

$$
z_{t+1}=\Pi_{\mathcal Z}\bigl(z_t-\eta\widetilde G_t\bigr),
$$

当前 theorem 不能被引用为 projected-gradient theorem。此时必须另行证明 gradient-mapping 版本。

### 2.3 lower response 位于约束边界时不能使用零梯度语义

proximal instantiation 使用 represented response stationarity：

$$
G_{\rho,x}(\xi^\star(x))=0.
$$

若实际 lower response 通过 trust-region projection 获得，且 optimum 可能落在边界，则应使用 projected residual 或 normal-cone condition；不能把边界解直接当作 unconstrained stationary response。

低成本做法是在理论对应的实验设置中保证 represented response 位于 trust region 内部。否则只能使用已经适配 projected residual 的安全证书部分，不能直接引用零梯度 envelope/strong-monotonicity 结论。

### 2.4 stochastic 结论只在期望接口成立时使用

随机率要求 centered moment 和 bounded second moment：

$$
\mathbb E_t\langle G_t+E_t,W_t\rangle=0,
\qquad
\mathbb E_t\|W_t\|^2\le\sigma_t^2.
$$

训练代码本身不会因为使用 mini-batch 就自动满足这些条件。需要说明 sampler、conditioning history、unbiasedness 或可控 bias。若只能确认噪声有界但不居中，应把交叉项或 bias 放入 certificate-error budget，而不是直接套用零交叉项随机率。

## 3. 每轮必须产生的对象

在第 $t$ 轮，代码应产生两个 lower-response candidates：

$$
\xi_{t+1}^{B}=\text{safe base response},
$$

$$
\xi_{t+1}^{P}=\text{learned proposal}.
$$

至少需要计算或记录：

```text
R_t              previous response residual
Rbase_t          residual of the base response
Rprop_t          residual of the learned proposal
eHatBase_t       computable proxy error for the base response
eHatProp_t       computable proxy error for the proposal
DeltaHat_t       requested nominal proxy improvement
tauR_t           residual acceptance tolerance
tauE_t           proxy-comparison tolerance
rhoBase_t        calibration radius for the base proxy
rhoProp_t        calibration radius for the proposal
epsBase_t        base contraction slack
```

理论中的 true errors

$$
e_t^B=\|g_t^v-g_t^B\|^2,
\qquad
e_t^P=\|g_t^v-g_t^P\|^2
$$

通常不能在大模型训练中直接计算。它们可以在小模型校准实验中估计，但生产训练的 acceptance rule 只能依赖可计算 proxy 与事先论证的 calibration radius。

## 4. 唯一允许的 accept/fallback 逻辑

定义 uncertainty-adjusted margin：

$$
M_t
=
\widehat\Delta_t
-\tau_t^e
-\rho_t^P
-\rho_t^B.
$$

proposal 只有同时通过以下三项测试时才可被计为 certified proposal：

$$
R_t^P\le R_t^B+\tau_t^R,
$$

$$
\widehat e_t^P
\le
\widehat e_t^B-\widehat\Delta_t+\tau_t^e,
$$

$$
M_t\ge0.
$$

代码级伪代码：

```python
margin = delta_hat - tau_e - rho_prop - rho_base
accepted = (
    r_prop <= r_base + tau_r
    and ehat_prop <= ehat_base - delta_hat + tau_e
    and margin >= 0.0
)

if accepted:
    xi_online = xi_prop
    gamma = margin
else:
    xi_online = xi_base
    gamma = 0.0
```

不允许出现以下变体：

- proposal 失败后仍保留正的 `gamma`；
- 只通过 proxy test、不通过 residual test，却仍进入主更新；
- 将负 margin 截断为零后仍接受 proposal；
- 用 proposal residual 反向替代 base residual；
- 把未扣除 calibration uncertainty 的 `delta_hat` 直接记作理论 gain。

## 5. residual envelope 的实现

定义：

$$
Q_t:=R_t^B+\tau_t^R,
$$

$$
\varepsilon_t:=\varepsilon_t^B+\tau_t^R.
$$

base update 应满足可检查的 contraction：

$$
R_t^B\le(1-\theta)R_t+\varepsilon_t^B.
$$

selector 随后保证：

$$
R_t^B\le Q_t,
\qquad
R_t^O\le Q_t,
$$

$$
Q_t\le(1-\theta)R_t+\varepsilon_t.
$$

工程上建议每轮记录：

```text
base_contraction_lhs = Rbase_t
base_contraction_rhs = (1-theta) * R_t + epsBase_t
envelope_Q           = Rbase_t + tauR_t
selected_residual    = Ronline_t
envelope_slack       = envelope_Q - selected_residual
```

若 base contraction 仅在平均意义上成立，应使用 Cesàro 或 expectation-level theorem，而不是 pointwise deterministic theorem。

## 6. residual 的推荐选择

### 6.1 无约束 proximal response

推荐：

$$
R_\rho(x,\xi)
=
\|G_{\rho,x}(\xi)\|^2,
$$

$$
G_{\rho,x}(\xi)
=
g_x(\xi)+\rho(\xi-\bar\xi_x).
$$

在局部 $\kappa$-hypomonotonicity 和 $\rho>\kappa$ 下，Lean 已验证：

$$
\|\nabla v(x)-\nabla_xh(x,\xi)\|^2
\le
\frac{L^2}{(\rho-\kappa)^2}R_\rho(x,\xi).
$$

对应稳定 theorem：

```text
OUSVRBLO.ICMLTheoryPackage.proximal_response_error_certificate
```

### 6.2 有约束 response

可采用 projected-gradient residual：

$$
R_{\mathrm{pg}}(x,\xi)
=
\left\|
\xi-\Pi_{\mathcal Y}\bigl(\xi-\gamma\nabla_\xi h(x,\xi)\bigr)
\right\|^2.
$$

但当前 proximal zero-gradient instantiation 不自动覆盖该选择。需要单独校准 response-distance/error bound；实现文档中必须标注使用的是 projected certificate，而不是 unconstrained stationary certificate。

## 7. 主更新方向必须与理论分解一致

理论 exact fixed-penalty gradient 为：

$$
G_t
=
\nabla F_t
+
\lambda\bigl(\nabla h_t-\operatorname{embed}(g_t^v)\bigr).
$$

selected response 诱导的 approximate direction 为：

$$
G_t+E_t
=
\nabla F_t
+
\lambda\bigl(\nabla h_t-\operatorname{embed}(g_t^O)\bigr).
$$

其中：

$$
E_t
=
\lambda\operatorname{embed}(g_t^v-g_t^O).
$$

实现应直接构造右侧的 selected-response direction。`g_t^v` 是证明中的 latent exact value-gradient，不要求生产代码计算；但代码中的 `g_online` 必须确实是被 selector 选中的 response 所诱导的 gradient，不能在 selector 后再次替换成其他 EMA 或 stale gradient。

## 8. proxy calibration 的工程含义

若 proxy gradient 满足：

$$
\|g_t^{\mathrm{proxy}}-g_t^v\|\le\delta_t,
$$

且 candidate 满足：

$$
\|g_t^c-g_t^v\|\le B_t^c,
$$

则可取：

$$
\rho_t^c
=
\delta_t(2B_t^c+\delta_t).
$$

这给出：

$$
\left|
\|g_t^c-g_t^{\mathrm{proxy}}\|^2
-
\|g_t^c-g_t^v\|^2
\right|
\le\rho_t^c.
$$

训练团队必须说明 $\delta_t$ 和 $B_t^c$ 的来源，例如：

- 小模型或周期性高精度 response solve 的校准；
- ensemble disagreement upper bound；
- clipped gradient radius；
- history-dependent confidence interval；
- held-out calibration batch。

若没有可辩护的 calibration radius，只能报告 heuristic proxy improvement，不能将其称为 certified $\Gamma_t$。

## 9. 推荐训练循环

```python
for t in range(T):
    # 1. Safe base response
    xi_base = base_lower_update(x, xi_prev)
    r_base = residual(x, xi_base)
    eps_base = max(0.0, r_base - (1.0 - theta) * r_prev)

    # 2. Learned proposal
    xi_prop = proposal_model(x, y, xi_prev, history)
    r_prop = residual(x, xi_prop)

    # 3. Upper-gradient proxy statistics
    g_base = grad_x_lower_surrogate(x, xi_base)
    g_prop = grad_x_lower_surrogate(x, xi_prop)
    ehat_base = proxy_error(g_base, proxy_value_gradient)
    ehat_prop = proxy_error(g_prop, proxy_value_gradient)

    # 4. Certified selector
    margin = delta_hat - tau_e - rho_prop - rho_base
    accepted = (
        r_prop <= r_base + tau_r
        and ehat_prop <= ehat_base - delta_hat + tau_e
        and margin >= 0.0
    )
    xi_online = xi_prop if accepted else xi_base
    gamma = margin if accepted else 0.0

    # 5. Certificate quantities
    q = r_base + tau_r
    eps = eps_base + tau_r
    r_online = r_prop if accepted else r_base

    assert gamma >= -numerical_tolerance
    assert r_online <= q + numerical_tolerance

    # 6. Selected-response fixed-penalty direction
    g_online = grad_x_lower_surrogate(x, xi_online)
    direction = selected_fixed_penalty_direction(
        x=x, y=y, g_online=g_online, penalty=lambda_value
    )

    # 7. Euclidean/reparameterized main update
    z = z - eta * direction
    x, y = unpack(z)
    xi_prev = xi_online
    r_prev = residual(x, xi_prev)
```

数值容差只属于实现层。理论 claim 中应把相应 tolerance 显式并入 $\tau_t^R$、$\tau_t^e$ 或其他 error budget，不能仅靠浮点 `assert` 忽略。

## 10. 最小日志协议

每轮至少保存：

```text
iteration
accepted
R_prev
R_base
R_prop
R_online
Q
eps_base
tau_R
eps_total
ehat_base
ehat_prop
delta_hat
tau_E
rho_base
rho_prop
Gamma
objective_value
gradient_or_direction_norm_sq
residual_drift_slack
```

额外建议保存：

```text
base optimizer steps
proposal inference cost
proxy computation cost
fallback reason
stage/reference id
lambda, rho, theta, eta
mini-batch seed and sampler state
```

这组日志足以审计：proposal 是否安全、gain 是否真实扣除了 uncertainty、base 是否提供 fallback contraction，以及理论 horizon 是否在同一个固定 surrogate 上运行。

## 11. 代码级单元测试

至少应覆盖：

1. **fallback identity**：拒绝时 `xi_online == xi_base` 且 `Gamma == 0`；
2. **accepted residual safety**：接受时 `Rprop <= Rbase + tauR`；
3. **margin accounting**：`Gamma == deltaHat - tauE - rhoProp - rhoBase`；
4. **envelope safety**：`Ronline <= Q`；
5. **base contraction**：`Rbase <= (1-theta)Rprev + epsBase`；
6. **fixed stage**：同一 stage 内 reference、penalty 和 surrogate id 不改变；
7. **selected gradient identity**：更新使用的 response gradient 来自 `xi_online`；
8. **no hidden projection**：主更新若发生 projection，测试必须显式标记 theorem mismatch；
9. **stochastic audit**：记录估计的 cross moment 与 second moment；
10. **numerical tolerance ownership**：所有 tolerance 都映射到一个理论 error budget。

## 12. 根据实现完成度选择可声明的 theorem

### 仅实现 residual safeguard

可使用：

```text
OUSVRBLO.ICMLTheoryPackage.fallback_safe_finite_horizon
```

若另有 `TrajectoryGradientCertificate` 对应的数学说明，可使用：

```text
OUSVRBLO.ICMLTheoryPackage.fallback_safe_objective_gradient_finite_horizon
```

### 实现 residual + calibrated proxy certificate

可进一步使用：

```text
OUSVRBLO.ICMLTheoryPackage.certified_gain_average
OUSVRBLO.ICMLTheoryPackage.certified_gain_same_iterate
OUSVRBLO.ICMLTheoryPackage.positive_gain_strictly_tightens
```

### 使用 proximal lower response

若满足局部 hypomonotonicity、$\rho>\kappa$、response stationarity 与 response-gradient Lipschitzness，可使用：

```text
OUSVRBLO.ICMLTheoryPackage.proximal_response_error_certificate
OUSVRBLO.ICMLTheoryPackage.proximal_baseline_sequence_certificate
```

### 使用 stochastic mini-batch update

只有在 expected one-step interfaces 被单独论证时，可使用：

```text
OUSVRBLO.ICMLTheoryPackage.stochastic_expected_finite_horizon
OUSVRBLO.ICMLTheoryPackage.stochastic_expected_gain_adjusted_average
OUSVRBLO.ICMLTheoryPackage.stochastic_variance_rate
```

## 13. 实现团队的最终 Go/No-Go 清单

在声称“实现与当前理论一致”之前，全部回答应为“是”：

```text
[ ] 一个分析阶段内 P、lambda、reference 固定
[ ] 主变量更新是欧氏更新或等价无约束重参数化
[ ] base response 提供可记录的 contraction certificate
[ ] proposal 失败后严格 fallback 到 base response
[ ] Q 使用 Rbase + tauR，而不是只使用 selected residual
[ ] Gamma 已扣除 tauE、rhoProp、rhoBase
[ ] Gamma 在 fallback 时为零
[ ] 更新方向使用 selector 最终选择的 response gradient
[ ] proxy calibration radius 有明确来源
[ ] 所有数值 tolerance 均进入理论 error budget
[ ] stochastic claim 具有 centered-moment/expected-interface 说明
[ ] 没有将 local fixed-penalty stationarity 写成原始 BLO KKT convergence
```

任一项不满足时，应降低 claim，或在方法中加入相应修正。