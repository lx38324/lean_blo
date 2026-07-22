# OUSVR-BLO 理论审查指南

本文面向负责数学审稿、形式化审计、内部理论验收或 rebuttal 支持的角色。目标是提供一条可重复的检查路径：先确认 claim 边界，再审查 primitive assumptions，随后检查 selector、系数、telescoping、proximal instantiation 与 stochastic extension，最后核对论文表述是否超过 Lean 实际覆盖范围。

## 1. 建议先给出的审查结论

当前理论适合作为方法型 ICML 投稿的 supporting theory。核心结论是：

> 对 restricted/local fixed-penalty value-function surrogate，任意 learned response proposal 经过显式 residual 与 calibrated proxy certificate 后，可以安全接入更新；accepted uncertainty-adjusted gain 作为真实非负有利项进入 selected trajectory 的 Lyapunov budget。

当前理论不证明：

```text
general nonconvex BLO convergence
original BLO KKT convergence
global lower-level optimality
counterfactual online trajectory dominance over the baseline trajectory
projected main-variable stationarity
concrete mini-batch filtration correctness
iterate convergence to a unique point
```

理论审查的首要任务不是重新证明所有代数，而是阻止上述边界在论文中被放大。

## 2. 稳定 theorem 入口

所有 paper-facing theorem 应从以下命名空间引用：

```text
OUSVRBLO.ICMLTheoryPackage
```

当前稳定声明：

```text
fallback_safe_finite_horizon
fallback_safe_objective_gradient_finite_horizon

certified_gain_average
certified_gain_same_iterate
certified_gain_objective_gradient_same_iterate
positive_gain_strictly_tightens

proximal_response_error_certificate
proximal_baseline_sequence_certificate

stochastic_expected_finite_horizon
stochastic_expected_gain_adjusted_average
stochastic_expected_same_iterate
stochastic_positive_gain_strictly_tightens
stochastic_variance_rate
```

审稿时应引用这些 stable wrappers，而不是依赖底层结构名称。底层 theorem 可用于核对 proof path，但不应成为论文唯一映射入口。

## 3. 四项主结果

### 3.1 Fallback-safe finite-horizon theorem

定义：

$$
\Psi_t=P_t+\alpha R_t,
\qquad
\alpha=\frac{\eta\lambda^2C_R}{\theta}.
$$

精确预算：

$$
\boxed{
\begin{aligned}
&\frac\eta4\sum_{t<T}\|G_t\|^2
+C_\Gamma\sum_{t<T}\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\\
&\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
\end{aligned}}
$$

其中：

$$
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2,
$$

$$
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2.
$$

objective-gradient 版本必须额外提供：

$$
G_t=\nabla P(z_t).
$$

对应：

```text
ICMLTheoryPackage.fallback_safe_objective_gradient_finite_horizon
```

若论文只引用 vector-level theorem，却把 $G_t$ 称为 objective gradient，应判定为语义错误。

### 3.2 Gain-adjusted selected-trajectory theorem

定义：

$$
J_t:=\|G_t\|^2+\lambda^2C_RR_t,
$$

$$
\mathcal B_T^{\mathrm{gain}}
:=
\mathcal B_T-C_\Gamma\sum_{t<T}\Gamma_t.
$$

Lean 验证：

$$
\frac\eta4\sum_{t<T}J_t
\le
\mathcal B_T^{\mathrm{gain}},
$$

$$
\frac1T\sum_{t<T}J_t
\le
\frac{4\mathcal B_T^{\mathrm{gain}}}{\eta T},
$$

以及 same-horizon existence bound。

还验证：

$$
\mathcal B_T^{\mathrm{gain}}\le\mathcal B_T,
$$

若

$$
\sum_{t<T}\Gamma_t>0,
$$

则：

$$
\mathcal B_T^{\mathrm{gain}}<\mathcal B_T.
$$

允许的解释：

> positive accumulated certified gain strictly tightens the upper bound for the selected trajectory.

禁止的解释：

> the learned trajectory is theoretically faster than the counterfactual baseline trajectory.

后者需要两条轨道的耦合比较，当前 theorem 不提供。

### 3.3 Proximal local-response instantiation

定义 proximal lower-gradient map：

$$
G_{\rho,x}(\xi)
=
g_x(\xi)+\rho(\xi-\bar\xi_x).
$$

假设：

$$
\langle g_x(u)-g_x(w),u-w\rangle
\ge
-\kappa\|u-w\|^2,
$$

$$
\rho>\kappa,
$$

$$
G_{\rho,x}(\xi^\star(x))=0,
$$

以及：

$$
\|\nabla_xh(x,\xi)-\nabla_xh(x,\xi^\star(x))\|
\le
L\|\xi-\xi^\star(x)\|.
$$

Lean 验证：

$$
\boxed{
\|\nabla v(x)-\nabla_xh(x,\xi)\|^2
\le
\frac{L^2}{(\rho-\kappa)^2}
\|G_{\rho,x}(\xi)\|^2.}
$$

应检查论文是否准确写成“principal response-error interface 的具体化”，而不是“全部主定理 assumptions 的完整具体化”。该 theorem 不自动给出 objective smoothness、base contraction、residual drift 或 proxy calibration。

### 3.4 Stochastic expectation-level theorem

随机层先检查 scalar centered moment：

$$
\mathbb E_t\langle U_t,W_t\rangle=0,
\qquad
\mathbb E_t\|W_t\|^2\le\sigma_t^2,
$$

从而：

$$
\mathbb E_t\|U_t+W_t\|^2
\le
\|U_t\|^2+\sigma_t^2.
$$

expected Lyapunov coefficient：

$$
C_\sigma
=
\frac{L_P\eta^2}{2}+\alpha A_\eta.
$$

有限时间预算：

$$
\boxed{
\begin{aligned}
&\frac\eta4\sum_{t<T}\mathbb E\|G_t\|^2
+C_\Gamma\sum_{t<T}\mathbb E\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}\mathbb ER_t
\\
&\le
\mathbb E\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\mathbb E\varepsilon_t
+C_b\sum_{t<T}\mathbb Eb_t
+C_d\sum_{t<T}\mathbb Ed_t
+C_\sigma\sum_{t<T}\sigma_t^2.
\end{aligned}}
$$

在 manuscript 参数下：

$$
\frac{4C_\sigma}{\eta}
=
\eta\left(
2L_P
+\frac{\sqrt2\lambda C_R}{\theta}
+\frac{2\lambda^2C_RL_R}{\theta}\eta
\right).
$$

因此零 certificate bias、uniform variance 情况下：

$$
O\!\left(\frac1{\eta T}+\eta\sigma^2\right).
$$

审查时必须确认论文使用以下限定语：

> under expected one-step interfaces induced by conditionally centered perturbations with bounded second moments.

当前 Lean 不包含具体概率空间、filtration、sampler measurability 或 high-probability theorem。

## 4. Primitive assumptions 与 derived facts

### 4.1 算法或证书输入

顶层 deterministic trajectory API 真正存储：

```text
proposal/base residual and proxy statistics
nonnegative tolerances, calibration radii and error budgets
safe base contraction
actual trajectory update identity
objective smoothness before update substitution
contractive map extracting the upper-variable displacement
selected-response residual smoothness
squared residual-gradient control
objective lower boundedness
step-size and small-step conditions
```

### 4.2 Lean 自动推导

以下不应再次被论文列为独立假设：

```text
accept/fallback branch
Ronline
eOnline
Gamma
Q = Rbase + tauR
eps = epsBase + tauR
Rbase <= Q
Ronline <= Q
Q <= (1-theta)R + eps
0 <= Gamma <= eBase
eOnline <= CR*Q + b - Gamma
0 <= CR*Q + b - Gamma
post-substitution objective descent
upper-block displacement bound
canonical Young scale and step norm
final gain-aware residual recursion
all advertised Lyapunov coefficient inequalities
```

若稿件把这些 derived facts 写成 assumptions，会弱化 theorem；若稿件完全不说明它们的来源，则会掩盖 selector 的贡献。

## 5. selector 审查

proposal acceptance 必须是三条件合取：

$$
R_t^P\le R_t^B+\tau_t^R,
$$

$$
\widehat e_t^P
\le
\widehat e_t^B-\widehat\Delta_t+\tau_t^e,
$$

$$
\widehat\Delta_t-\tau_t^e-\rho_t^P-\rho_t^B\ge0.
$$

定义：

$$
\Gamma_t
=
\begin{cases}
\widehat\Delta_t-\tau_t^e-\rho_t^P-\rho_t^B,
&\text{accepted},\\
0,&\text{fallback}.
\end{cases}
$$

审查清单：

```text
[ ] fallback round 的 Gamma 是否严格为 0
[ ] accepted round 是否同时通过 residual test
[ ] DeltaHat 是否扣除了 tauE、rhoProp、rhoBase
[ ] 是否错误地对负 margin 做 max(0, margin) 后仍接受 proposal
[ ] 是否把 nominal proxy improvement 称为 true gain
```

## 6. residual envelope 审查

当前证明不用单一 $\widehat R_t$ 同时代表 base 和 selected residual，而是定义：

$$
Q_t=R_t^B+\tau_t^R.
$$

必须核对：

$$
R_t^B\le Q_t,
\qquad
R_t^O\le Q_t.
$$

base contraction：

$$
R_t^B\le(1-\theta)R_t+\varepsilon_t^B
$$

给出：

$$
Q_t\le(1-\theta)R_t+\varepsilon_t^B+\tau_t^R.
$$

若稿件重新使用：

$$
e_t^B\le C_RR_t^O+b_t
$$

而没有额外反向 residual bound，应判定证明链不闭合。

## 7. 梯度语义审查

Lean 区分：

1. 满足 smoothness inequality 的 descent vector $G_t$；
2. 实际 objective gradient $\nabla P(z_t)$。

只有在提供：

```text
TrajectoryGradientCertificate
```

后才有：

$$
G_t=\nabla P(z_t).
$$

固定罚目标的梯度分解为：

$$
G_t
=
\nabla F_t
+\lambda\bigl(\nabla h_t-\operatorname{embed}(g_t^v)\bigr).
$$

selected error：

$$
E_t
=
\lambda\operatorname{embed}(g_t^v-g_t^O).
$$

所以：

$$
G_t+E_t
=
\nabla F_t
+\lambda\bigl(\nabla h_t-\operatorname{embed}(g_t^O)\bigr).
$$

若论文定义的实际更新方向与该分解不一致，不能引用当前 trajectory theorem。

## 8. 系数审查

核心参数：

$$
\mu=\frac1{\sqrt2\lambda},
$$

$$
A_\eta
=
\frac{\eta}{2\sqrt2\lambda}
+\frac{L_R\eta^2}{2},
$$

$$
\beta_\eta
=
\sqrt2\lambda\eta+\lambda^2L_R\eta^2.
$$

small-step condition：

$$
C_R\beta_\eta\le\frac\theta4.
$$

由此应推出：

$$
2\alpha A_\eta\le\frac\eta4,
$$

$$
\Delta_R\ge\frac{\eta\lambda^2C_R}{4},
$$

$$
C_\varepsilon
=
\eta\lambda^2C_R\left(\frac34+\frac1\theta\right),
$$

$$
C_b=\frac34\eta\lambda^2,
\qquad
C_d=\frac{\eta\lambda^2C_R}{\theta}.
$$

审查时重点查找：

- 漏掉的 $\lambda^2$；
- drift 中 gain 项的系数是否是 $2A_\eta\lambda^2$；
- stochastic coefficient 是否为 $L_P\eta^2/2+\alpha A_\eta$；
- residual average bound 除数是否含 $\lambda^2C_R$；
- gradient-norm tolerance 是否使用 $\epsilon^2$，对应 $O(\epsilon^{-2})$。

## 9. perturbation regimes 审查

### 9.1 Summable perturbations

若：

$$
\sum_t\varepsilon_t<\infty,
\quad
\sum_tb_t<\infty,
\quad
\sum_td_t<\infty,
$$

则可声明：

$$
\sum_t\|G_t\|^2<\infty,
\qquad
\sum_tR_t<\infty,
$$

从而：

$$
\|G_t\|\to0,
\qquad
R_t\to0.
$$

这仍不推出 $z_t$ 收敛到唯一点。

### 9.2 Cesàro-vanishing perturbations

若各误差的时间平均趋于零，只能声明：

$$
\frac1T\sum_{t<T}\|G_t\|^2\to0,
\qquad
\frac1T\sum_{t<T}R_t\to0.
$$

不能升级为 pointwise convergence。

### 9.3 Persistent bounded perturbations

若：

$$
C_\varepsilon\varepsilon_t+C_bb_t+C_dd_t\le\bar\delta,
$$

结论是 neighborhood：

$$
\frac1T\sum_{t<T}J_t
\le
\frac{4(\Psi_0-P_\star)}{\eta T}
+\frac{4\bar\delta}{\eta}.
$$

固定 mini-batch noise 或固定 acceptance tolerance 不能被写成零误差收敛。

## 10. local / constrained response 边界

当前 branch-envelope 和 proximal zero-gradient theorem 最适合：

- unconstrained response；或
- trust-region 内部解。

若 response 位于约束边界，一般只有：

$$
-G_{\rho,x}(\xi^\star)
\in
N_{\mathcal Y}(\xi^\star),
$$

而不是：

$$
G_{\rho,x}(\xi^\star)=0.
$$

审稿时应确认：

```text
[ ] 实际方法是否使用 response projection
[ ] 若使用，论文是否假设 represented response 为 interior
[ ] 若不在 interior，是否错误引用 unconstrained proximal theorem
```

## 11. 固定目标与 reference refresh

Lyapunov 证明要求一个 horizon 内的 $P$ 固定。若 proximal reference $\bar\xi$ 每轮变化，则：

$$
P_{t+1}\ne P_t\text{ 对应的同一个函数值序列}.
$$

这种 objective drift 不能仅凭 residual drift error $d_t$ 自动控制。审查应要求：

- reference 在 stage 内固定；或
- 单独加入 objective drift budget；或
- 降低 claim，仅把 theorem 用于每个 fixed-reference stage。

## 12. proxy calibration 审查

若使用 vector proxy sufficient condition：

$$
\|g^{\mathrm{proxy}}-g^v\|\le\delta,
$$

$$
\|g^c-g^v\|\le B,
$$

则：

$$
\rho^c=\delta(2B+\delta).
$$

审稿人应追问：

```text
[ ] delta 如何获得
[ ] B 是否是理论上界还是观测值
[ ] calibration 是否与 acceptance batch 独立或至少条件有效
[ ] rhoProp 与 rhoBase 是否允许不同
[ ] tauE 是否也被扣除
```

没有 calibration argument 时，$\Gamma_t$ 只能被称为 heuristic score，不能被称为 certified true-error gain。

## 13. Lean 重现与信任检查

标准验证命令：

```bash
bash scripts/verify.sh
```

它执行：

```text
locked lake build
placeholder proof scan
Markdown and theorem-export synchronization
Lean build-log diagnostic scan
```

依赖由 `lake-manifest.json` 锁定。形式化审查还应记录：

```text
lean-toolchain
mathlib revision
Git commit SHA
GitHub Actions run id
number of errors/warnings/unsolved goals
```

可选增强审计：对 stable theorem 运行：

```lean
#print axioms OUSVRBLO.ICMLTheoryPackage.fallback_safe_finite_horizon
```

以及其余 stable exports。该步骤可进一步区分项目自身无 `axiom` 关键字与依赖库中使用的经典公理。

## 14. 允许与禁止的 claim

### 允许

```text
fallback-safe restricted/local fixed-penalty stationarity
certificate-selected response safety
uncertainty-adjusted gain enters the Lyapunov budget
positive accumulated gain strictly tightens the selected-trajectory upper bound
proximal local response instantiates the key response-error certificate
expected stochastic rate O(1/(eta*T) + eta*sigma^2) under expected interfaces
machine-checked coefficient-sensitive proof chain
```

### 禁止或需额外 theorem

```text
solves general nonconvex BLO
converges to original BLO KKT points
learned trajectory dominates the baseline trajectory
concrete LLM mini-batch sampler is verified in Lean
projected main-variable update is covered
arbitrary local response equals the global lower value minimizer
iterates converge to a unique stationary point
```

## 15. 与已有工作的定位

理论贡献不应仅表述为“learned optimizer 有 fallback，因此收敛”。更准确的差异化是：

$$
\text{value-anchor-specific residual envelope}
+
\text{upper-gradient-aware calibrated certificate}
+
\text{selected-trajectory gain accounting}
+
\text{Lean-checked coefficient propagation}.
$$

审查相关工作时，应区分：

1. generic learned-optimizer guard；
2. general nonconvex BLO/KKT theory；
3. 本项目的 local fixed-penalty value-anchor safeguard。

本项目不能在一般性上与 general nonconvex BLO theory 竞争；其价值在于方法专用的 certificate chain 和形式化可靠性。

## 16. 最终审查表

### 数学闭合

```text
[ ] baseline/selected residual 通过 Q_t 正确统一
[ ] Gamma_t 已扣除全部 uncertainty 与 tolerance
[ ] gain-aware error scale 非负
[ ] gain 同时进入 objective descent 与 residual drift
[ ] 所有 Lyapunov 系数由 small-step condition 推导
[ ] terminal Lyapunov lower bound 使用正确
```

### 语义闭合

```text
[ ] objective-gradient theorem 具有 TrajectoryGradientCertificate
[ ] fixed-penalty objective 在 horizon 内固定
[ ] selected response gradient 确实进入实际更新方向
[ ] local response 未被称为原始全局 minimizer
[ ] projected/boundary response 没有误用零梯度 theorem
```

### 随机闭合

```text
[ ] expected one-step interfaces 被明确列为 assumptions
[ ] centered cross moment 与 variance bound 被说明
[ ] 固定 bias/noise 没有被声称 pointwise 收敛到零
[ ] O(T^-1/2) 结论包含 eta=O(T^-1/2) 与 small-step 限制
```

### 形式化与可复现

```text
[ ] 论文 theorem 与 ICMLTheoryPackage stable exports 对齐
[ ] scripts/verify.sh 通过
[ ] 无 Lean errors、warnings、unsolved goals、sorry/admit/axiom declarations
[ ] commit、toolchain、mathlib revision 与 CI run 均记录
```

全部通过时，可给出结论：

> 当前理论可以作为方法型 ICML 投稿的理论部分；剩余风险主要属于具体模型常数校准、算法—理论对齐和实证有效性，而不是主证明链本身。