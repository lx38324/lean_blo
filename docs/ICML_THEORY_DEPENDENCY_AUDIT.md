# ICML method-theory dependency audit

This note audits the four paper-facing theoretical results intended for a
method-and-experiments ICML submission. It separates primitive assumptions,
certificate-generated quantities, analytic consequences, and conclusions. The
purpose is to prevent a paper statement from silently treating a derived fact as
an assumption or overstating what the Lean development verifies.

The stable Lean citation surface is:

```text
OUSVRBLO.ICMLTheoryPackage
```

implemented in `OUSVRBLO/ICMLTheoryPackage.lean`.

## 1. Result map

| Paper-facing result | Stable Lean declaration | Underlying checked theorem |
|---|---|---|
| Fallback-safe finite-horizon budget | `ICMLTheoryPackage.fallback_safe_finite_horizon` | `TrajectoryCertifiedProposalGainSystem.cumulative_budget` |
| Gain-adjusted average certificate | `ICMLTheoryPackage.certified_gain_average` | `CertifiedGainStepSystem.joint_average_bound_with_gain` |
| Gain-adjusted same-iterate certificate | `ICMLTheoryPackage.certified_gain_same_iterate` | `TrajectoryCertifiedProposalGainSystem.exists_joint_certificate_with_gain` |
| Objective-gradient gain-adjusted certificate | `ICMLTheoryPackage.certified_gain_objective_gradient_same_iterate` | `TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_joint_certificate_with_gain` |
| Strict tightening under positive accumulated gain | `ICMLTheoryPackage.positive_gain_strictly_tightens` | `CertifiedGainStepSystem.gainAdjustedRhs_lt_accumulatedRhs_of_positive_gain` |
| Proximal response error certificate | `ICMLTheoryPackage.proximal_response_error_certificate` | `ProximalRestrictedValueModel.r2` |
| Proximal sequence baseline certificate | `ICMLTheoryPackage.proximal_baseline_sequence_certificate` | `RestrictedValueProposalData.baseline_error_bound_of_proximal` |
| Expected stochastic finite-horizon budget | `ICMLTheoryPackage.stochastic_expected_finite_horizon` | `StochasticExpectedGainSystem.cumulative_budget` |
| Expected gain-adjusted average rate | `ICMLTheoryPackage.stochastic_expected_gain_adjusted_average` | `StochasticExpectedGainSystem.joint_average_bound_with_gain` |
| Explicit stochastic variance rate | `ICMLTheoryPackage.stochastic_variance_rate` | `StochasticExpectedGainSystem.joint_average_bound_of_variance_only_manuscript` |

## 2. Theorem 1: fallback-safe deterministic stationarity

### Primitive algorithm and certificate inputs

The trajectory-facing theorem stores:

1. proposal/base residual and proxy statistics;
2. nonnegative residuals, tolerances, calibration radii, and error budgets;
3. safe base contraction;
4. actual deterministic trajectory displacement;
5. local objective smoothness before substituting the update;
6. a contractive map extracting the upper-variable displacement;
7. selected-response residual smoothness;
8. a squared residual-gradient bound;
9. lower boundedness of the represented fixed-penalty objective;
10. the objective and residual small-step conditions.

The relevant structure is:

```text
TrajectoryCertifiedProposalGainSystem
```

### Derived rather than assumed

Lean derives all of the following:

```text
accept / fallback decision
Ronline
Gamma
Q = Rbase + tauR
eps = epsBase + tauR
Rbase <= Q
Ronline <= Q
Q <= (1-theta) * R + eps
eOnline <= CR * Q + b - Gamma
0 <= CR * Q + b - Gamma
post-substitution objective descent
upper-block displacement bound
gain-aware residual recursion
all final Lyapunov coefficient inequalities
```

In particular, the public theorem does not assume the final inequalities

```text
two_alpha_Aeta_le
residual_drop_coeff
eps_coeff_bound
b_coeff_bound
```

as independent facts. They are generated from the parameter package and the
single small-step condition.

### Conclusion

For every horizon `T`, Lean checks

$$
\frac{\eta}{4}\sum_{t<T}\|G_t\|^2
+C_\Gamma\sum_{t<T}\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\le \mathcal B_T.
$$

The theorem is proposal-agnostic before certification: the learned updater may
produce an arbitrary candidate, but only the selected response enters the
trajectory.

## 3. Theorem 2: certified gain tightens the selected-trajectory bound

Define

$$
J_t:=\|G_t\|^2+\lambda^2C_RR_t
$$

and

$$
\mathcal B_T^{\rm gain}
:=
\mathcal B_T-C_\Gamma\sum_{t<T}\Gamma_t.
$$

Lean verifies

$$
\frac{\eta}{4}\sum_{t<T}J_t
\le
\mathcal B_T^{\rm gain},
$$

hence

$$
\frac1T\sum_{t<T}J_t
\le
\frac{4\mathcal B_T^{\rm gain}}{\eta T},
$$

and a same-horizon existence result.

The dependency is exactly the deterministic budget plus nonnegativity of the
selected gain. No additional analytic assumption is introduced.

Lean also verifies

$$
\mathcal B_T^{\rm gain}\le\mathcal B_T,
$$

and, if

$$
\sum_{t<T}\Gamma_t>0,
$$

then

$$
\mathcal B_T^{\rm gain}<\mathcal B_T.
$$

This is a strict tightening of the upper bound for the selected trajectory. It
is not a comparison between two counterfactual trajectories and must not be
presented as online-versus-baseline trajectory dominance.

## 4. Theorem 3: proximal local-response instantiation

The proximal model assumes a represented restricted value-gradient interface and
an unregularized lower-gradient map `g_x` satisfying local hypomonotonicity:

$$
\langle g_x(u)-g_x(w),u-w\rangle
\ge -\kappa\|u-w\|^2.
$$

For

$$
G_{\rho,x}(\xi)
=
g_x(\xi)+\rho(\xi-\bar\xi_x),
$$

assume

$$
\rho>\kappa,
$$

stationarity of the represented response,

$$
G_{\rho,x}(\xi^\star(x))=0,
$$

and response-Lipschitzness of the upper/value partial gradient:

$$
\|\nabla_xh(x,\xi)-\nabla_xh(x,\xi^\star(x))\|
\le L\|\xi-\xi^\star(x)\|.
$$

Lean derives strong monotonicity with modulus

$$
\mu=\rho-\kappa>0,
$$

uniqueness of the stationary response, and the computable residual certificate

$$
\boxed{
\|\nabla v(x)-\nabla_xh(x,\xi)\|^2
\le
\frac{L^2}{(\rho-\kappa)^2}
\|G_{\rho,x}(\xi)\|^2.
}
$$

Thus the principal response-error coefficient can be instantiated as

$$
C_E=\frac{L^2}{(\rho-\kappa)^2}.
$$

This theorem closes the response-error interface only. It does not by itself
prove objective smoothness, base contraction, residual drift, or stochastic
sampling properties for a concrete neural model.

## 5. Theorem 4: stochastic expectation-level stationarity

### Centered moment input

At the scalar conditional-moment level, the stochastic development assumes a
decomposition

$$
\mathbb E_t\|U_t+W_t\|^2
=
\|U_t\|^2
+2\mathbb E_t\langle U_t,W_t\rangle
+\mathbb E_t\|W_t\|^2,
$$

with

$$
\mathbb E_t\langle U_t,W_t\rangle=0,
\qquad
\mathbb E_t\|W_t\|^2\le\sigma_t^2.
$$

Lean checks the resulting second-moment inequality.

### Expected one-step interfaces

The expectation-level theorem then takes the standard expected objective and
residual one-step inequalities with additional terms

$$
\frac{L_P\eta^2}{2}\sigma_t^2
$$

and

$$
A_\eta\sigma_t^2.
$$

The Lyapunov variance coefficient is derived as

$$
C_\sigma
=
\frac{L_P\eta^2}{2}+\alpha A_\eta.
$$

### Conclusion

Lean verifies

$$
\begin{aligned}
&\frac{\eta}{4}\sum_{t<T}\mathbb E\|G_t\|^2
+C_\Gamma\sum_{t<T}\mathbb E\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}\mathbb ER_t
\\
&\le
\mathbb E\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\mathbb E\varepsilon_t
+C_b\sum_{t<T}\mathbb Eb_t
+C_d\sum_{t<T}\mathbb Ed_t
+C_\sigma\sum_{t<T}\sigma_t^2.
\end{aligned}
$$

For zero certificate bias, uniformly bounded variance, and the manuscript
coefficient

$$
A_\eta
=
\frac{\eta}{2\sqrt2\lambda}
+
\frac{L_R\eta^2}{2},
$$

Lean checks

$$
\frac{4C_\sigma}{\eta}
=
\eta
\left(
2L_P
+
\frac{\sqrt2\lambda C_R}{\theta}
+
\frac{2\lambda^2C_RL_R}{\theta}\eta
\right).
$$

Therefore the expected joint stationarity/residual rate has the explicit form

$$
O\!\left(\frac1{\eta T}+\eta\sigma^2\right)
$$

when the bracketed coefficient is bounded.

### Boundary of the stochastic formalization

Lean checks expectation-level scalar algebra and a centered moment sufficient
condition. It does not formalize:

1. a concrete probability space and filtration for an LLM training loop;
2. measurability of a neural network sampler;
3. unbiasedness of a particular mini-batch implementation;
4. high-probability concentration;
5. projected stochastic main-variable updates.

These remain model-specific sufficient conditions and must be stated as such.

## 6. Assumption ownership

For paper presentation, assumptions should be grouped by ownership.

### Algorithm-certified assumptions

These are checked or enforced by the method-facing certificate:

```text
proposal residual test
proxy comparison test
nonnegative calibrated margin
fallback to base response
selected residual envelope
```

### Local analytic assumptions

These must be justified for the represented surrogate and trajectory region:

```text
objective smoothness and lower boundedness
base residual contraction
residual smoothness
residual-gradient control
restricted response regularity
```

### Stochastic assumptions

These must be justified by the sampling model:

```text
centered cross moment
bounded second moment
expected one-step objective inequality
expected one-step residual inequality
```

This separation is important: the safeguard certifies acceptance properties, but
it does not certify all local smoothness or stochastic sampling premises.

## 7. Recommended main-text theorem order

For a method-oriented submission, the main text should use the following order:

1. fallback-safe deterministic theorem;
2. gain-adjusted corollary and strict-tightening statement;
3. proximal local-response instantiation;
4. stochastic expected corollary.

The full coefficient derivation, Cesaro/summability variants, pointwise
consequences, and Lean coverage table can remain in the appendix.

## 8. Claims that remain excluded

The current package does not prove:

```text
global nonconvex lower-level optimality
original BLO KKT convergence
global or set-valued Danskin theory
counterfactual online-versus-baseline trajectory dominance
projected main-variable stationarity
a concrete neural mini-batch filtration model
convergence of z_t to a unique point
```

The defensible paper-facing claim is restricted/local fixed-penalty stationarity
with certificate-generated fallback safety, a gain-adjusted selected-trajectory
bound, a proximal response instantiation, and an expectation-level stochastic
variance budget.
