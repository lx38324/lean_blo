# OUSVR-BLO 理论审查指南

本文面向数学审稿、形式化审计、内部理论验收和 rebuttal 支持角色。审查目标是确认四件事：主 claim 没有超过 restricted/local fixed-penalty 范围；primitive assumptions 与 derived facts 没有混淆；论文公式与 Lean theorem 一一对应；实现描述没有违反固定目标、非投影更新和 expectation-level stochastic 边界。

## 1. 建议的总评

当前理论适合作为方法型 ICML 投稿的 supporting theory。核心结论是：

> 对 restricted/local fixed-penalty value-function surrogate，任意 learned response proposal 经过显式 residual 与 calibrated proxy certificate 后可以安全接入更新；accepted uncertainty-adjusted gain 作为真实非负有利项进入 selected trajectory 的 Lyapunov budget。

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

## 2. 稳定 theorem 入口

所有 paper-facing theorem 应从以下命名空间引用：

```text
OUSVRBLO.ICMLTheoryPackage
```

完整稳定声明如下：

```text
ICMLTheoryPackage.fallback_safe_finite_horizon
ICMLTheoryPackage.fallback_safe_objective_gradient_finite_horizon

ICMLTheoryPackage.certified_gain_average
ICMLTheoryPackage.certified_gain_same_iterate
ICMLTheoryPackage.certified_gain_objective_gradient_same_iterate
ICMLTheoryPackage.positive_gain_strictly_tightens

ICMLTheoryPackage.proximal_response_error_certificate
ICMLTheoryPackage.proximal_baseline_sequence_certificate

ICMLTheoryPackage.stochastic_expected_finite_horizon
ICMLTheoryPackage.stochastic_expected_gain_adjusted_average
ICMLTheoryPackage.stochastic_expected_same_iterate
ICMLTheoryPackage.stochastic_positive_gain_strictly_tightens
ICMLTheoryPackage.stochastic_variance_rate
```

底层 theorem 可用于追踪 proof path，但论文 coverage table 应优先引用这些 stable wrappers。

## 3. Theorem 1：fallback-safe finite-horizon budget

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
\frac{\eta\lambda^2}{2}+2\alpha A_\eta\lambda^2,
$$

$$
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2.
$$

必须区分：

- `fallback_safe_finite_horizon`：对 trajectory descent vector $G_t$ 的预算；
- `fallback_safe_objective_gradient_finite_horizon`：额外要求 `TrajectoryGradientCertificate`，从而 $G_t=\nabla P(z_t)$。

若稿件只使用前者，却将 $G_t$ 直接称为 objective gradient，应判定为语义错误。

## 4. Theorem 2：gain-adjusted selected-trajectory rate

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

同时：

$$
\mathcal B_T^{\mathrm{gain}}\le\mathcal B_T,
$$

若

$$
\sum_{t<T}\Gamma_t>0,
$$

则

$$
\mathcal B_T^{\mathrm{gain}}<\mathcal B_T.
$$

允许的解释：

> Positive accumulated certified gain strictly tightens the upper bound for the selected trajectory.

禁止的解释：

> The learned trajectory is theoretically faster than the counterfactual baseline trajectory.

当前 theorem 没有构造两条 counterfactual trajectories 的耦合比较。

## 5. Theorem 3：proximal local-response instantiation

定义：

$$
G_{\rho,x}(\xi)
=
g_x(\xi)+\rho(\xi-\bar\xi_x).
$$

假设：

$$
\langle g_x(u)-g_x(w),u-w\rangle
\ge-\kappa\|u-w\|^2,
$$

$$
\rho>\kappa,
$$

$$
G_{\rho,x}(\xi^\star(x))=0,
$$

以及

$$
\|\nabla_xh(x,\xi)-\nabla_xh(x,\xi^\star(x))\|
\le L\|\xi-\xi^\star(x)\|.
$$

Lean 验证：

$$
\boxed{
\|\nabla v(x)-\nabla_xh(x,\xi)\|^2
\le
\frac{L^2}{(\rho-\kappa)^2}
\|G_{\rho,x}(\xi)\|^2.}
$$

应将其表述为 principal response-error interface 的具体化，而不是全部主定理 assumptions 的完整具体化。它不自动证明 objective smoothness、base contraction、residual drift 或 proxy calibration。

## 6. Theorem 4：stochastic expectation-level theorem

centered moment 输入：

$$
\mathbb E_t\langle U_t,W_t\rangle=0,
\qquad
\mathbb E_t\|W_t\|^2\le\sigma_t^2.
$$

因此：

$$
\mathbb E_t\|U_t+W_t\|^2
\le\|U_t\|^2+\sigma_t^2.
$$

定义：

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

必须使用限定语：

> Under expected one-step interfaces induced by conditionally centered perturbations with bounded second moments.

当前 Lean 不形式化具体 probability space、filtration、sampler measurability 或 high-probability theorem。

## 7. Primitive assumptions 与 derived facts

### 7.1 顶层真正存储的输入

```text
proposal/base residual and proxy statistics
nonnegative tolerances, calibration radii and error budgets
safe base contraction
actual trajectory update identity
objective smoothness before update substitution
contractive upper-variable block map
selected-response residual smoothness
squared residual-gradient control
objective lower boundedness
step-size and small-step conditions
```

### 7.2 Lean 自动推导的对象

以下不应再次作为独立 assumptions：

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

## 8. selector 与 residual envelope 审查

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
\widehat\Delta_t-\tau_t^e-\rho_t^P-\rho_t^B,&\text{accepted},\\
0,&\text{fallback}.
\end{cases}
$$

共同 residual envelope：

$$
Q_t=R_t^B+\tau_t^R.
$$

因此：

$$
R_t^B\le Q_t,
\qquad
R_t^O\le Q_t,
$$

$$
Q_t\le(1-\theta)R_t+\varepsilon_t^B+\tau_t^R.
$$

审查红旗：

```text
fallback round 仍保留正 Gamma
只通过 proxy test 就接受 proposal
负 margin 截断为 0 后仍接受 proposal
DeltaHat 未扣除 tauE、rhoProp、rhoBase
用 selected residual 反向替代 base residual
```

## 9. 梯度语义审查

fixed-penalty gradient：

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

若实际更新方向不是 selector 最终选择的 response gradient 所诱导的方向，不能引用当前 trajectory theorem。

## 10. 系数审查

核心参数：

$$
\mu=\frac1{\sqrt2\lambda},
$$

$$
A_\eta
=
\frac{\eta}{2\sqrt2\lambda}+\frac{L_R\eta^2}{2},
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

它应推出：

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

重点查找：

```text
missing lambda^2 factors
wrong 2*Aeta*lambda^2 gain coefficient in residual drift
wrong Csigma = LP*eta^2/2 + alpha*Aeta
residual average denominator missing lambda^2*CR
epsilon-stationarity stated with O(epsilon^-1) instead of O(epsilon^-2)
```

## 11. perturbation regimes

### Summable

若

$$
\sum_t\varepsilon_t<\infty,
\quad
\sum_tb_t<\infty,
\quad
\sum_td_t<\infty,
$$

则可声明：

$$
\|G_t\|\to0,
\qquad
R_t\to0.
$$

这不推出 $z_t$ 收敛到唯一点。

### Cesàro-vanishing

若误差时间平均趋于零，只能声明：

$$
\frac1T\sum_{t<T}\|G_t\|^2\to0,
\qquad
\frac1T\sum_{t<T}R_t\to0.
$$

不能升级为 pointwise convergence。

### Persistent bounded

若

$$
C_\varepsilon\varepsilon_t+C_b b_t+C_d d_t\le\bar\delta,
$$

则结论是 neighborhood：

$$
\frac1T\sum_{t<T}J_t
\le
\frac{4(\Psi_0-P_\star)}{\eta T}
+\frac{4\bar\delta}{\eta}.
$$

固定 mini-batch noise 或固定 tolerance 不能被写成零误差收敛。

## 12. local / constrained response 边界

当前 proximal zero-gradient theorem 最适合 unconstrained response 或 trust-region interior solution。若解位于边界，一般只有：

$$
-G_{\rho,x}(\xi^\star)
\in N_{\mathcal Y}(\xi^\star),
$$

而不是：

$$
G_{\rho,x}(\xi^\star)=0.
$$

审查应确认实际方法是否使用 response projection；若使用，稿件是否明确 interior assumption 或另行给出 projected/normal-cone certificate。

## 13. 固定目标与 reference refresh

Lyapunov 证明要求一个 horizon 内的 $P$ 固定。若 proximal reference $\bar\xi$ 每轮变化，则 objective 本身也变化。审查应要求：

- reference 在 stage 内固定；或
- 单独加入 objective-drift budget；或
- theorem 仅用于每个 fixed-reference stage。

仅把 reference refresh 写入 residual drift error $d_t$ 不足以自动控制 objective drift。

## 14. proxy calibration 审查

若使用 vector proxy sufficient condition：

$$
\|g^{\mathrm{proxy}}-g^v\|\le\delta,
\qquad
\|g^c-g^v\|\le B,
$$

则可取：

$$
\rho^c=\delta(2B+\delta).
$$

应追问：

```text
delta 的来源
B 是理论上界还是观测值
calibration 是否在 acceptance 条件下仍有效
rhoProp 与 rhoBase 是否分别校准
tauE 是否已被扣除
```

没有 calibration argument 时，$\Gamma_t$ 只能被称为 heuristic score，不能被称为 certified true-error gain。

## 15. Lean 重现与信任检查

标准命令：

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

审查记录应包含：

```text
Git commit SHA
lean-toolchain
mathlib revision
GitHub Actions run id
errors, warnings and unsolved-goal counts
```

可选增强：对 stable theorem 执行 `#print axioms`，区分项目自身无自定义公理与依赖库中使用的经典公理。

## 16. 允许与禁止的 claim

### 允许

```text
fallback-safe restricted/local fixed-penalty stationarity
certificate-selected response safety
uncertainty-adjusted gain enters the Lyapunov budget
positive accumulated gain strictly tightens the selected-trajectory upper bound
proximal local response instantiates the key response-error certificate
expected rate O(1/(eta*T) + eta*sigma^2) under expected interfaces
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

## 17. 与已有工作的定位

理论贡献不应只表述为“learned optimizer 有 fallback，因此收敛”。更准确的差异化是：

$$
\text{value-anchor-specific residual envelope}
+
\text{upper-gradient-aware calibrated certificate}
+
\text{selected-trajectory gain accounting}
+
\text{Lean-checked coefficient propagation}.
$$

应区分 generic learned-optimizer guard、general nonconvex BLO/KKT theory，以及本项目的 local fixed-penalty value-anchor safeguard。

## 18. 最终审查表

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
[ ] selected response gradient 进入实际更新方向
[ ] local response 未被称为原始全局 minimizer
[ ] projected/boundary response 没有误用零梯度 theorem
```

### 随机闭合

```text
[ ] expected one-step interfaces 被明确列为 assumptions
[ ] centered cross moment 与 variance bound 被说明
[ ] 固定 bias/noise 没有被声称 pointwise 收敛到零
[ ] O(T^-1/2) 包含 eta=O(T^-1/2) 与 small-step 限制
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