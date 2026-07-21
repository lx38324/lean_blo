# Formalization scope

This repository formalizes a certificate-facing theorem stack for a safeguarded
online value-anchor method over a restricted/local fixed-penalty value surrogate.

The stable paper-facing exports are in:

```text
OUSVRBLO.ICMLTheoryPackage
```

The detailed assumption audit is in
`docs/ICML_THEORY_DEPENDENCY_AUDIT.md`.

## 1. Deterministic selected-response theorem

At round `t`, the proof-level selector accepts a proposal exactly when

```text
Rprop_t <= Rbase_t + tauR_t
and ehatProp_t <= ehatBase_t - DeltaHat_t + tauE_t
and 0 <= DeltaHat_t - tauE_t - rhoProp_t - rhoBase_t.
```

It defines

```text
Ronline_t = if accepted then Rprop_t else Rbase_t
Gamma_t   = if accepted
              then DeltaHat_t - tauE_t - rhoProp_t - rhoBase_t
              else 0.
```

The base response and residual tolerance generate

```text
Q_t   = Rbase_t + tauR_t
eps_t = epsBase_t + tauR_t.
```

Lean derives

```text
Rbase_t <= Q_t
Ronline_t <= Q_t
Q_t <= (1-theta) * R_t + eps_t
0 <= Gamma_t <= eBase_t
eOnline_t <= CR * Q_t + b_t - Gamma_t
0 <= CR * Q_t + b_t - Gamma_t.
```

For the selected value-gradient error embedded into the ambient update space,
Lean checks the exact identity

```text
||Err_t||^2 = lambda^2 * eOnline_t.
```

Under the actual deterministic update, objective smoothness before substitution,
selected-response residual smoothness, residual-gradient control, and

```text
CR * beta <= theta / 4,
```

Lean proves

```text
eta/4 * sum ||G_t||^2
  + Cgain * sum Gamma_t
  + eta * lambda^2 * CR / 4 * sum R_t
  <= initial Lyapunov gap + accumulated certificate errors,
```

where

```text
Cgain = eta * lambda^2 / 2 + 2 * alpha * Aeta * lambda^2,
eta * lambda^2 / 2 <= Cgain <= 3/4 * eta * lambda^2.
```

## 2. Derived rather than assumed

The highest-level deterministic API is

```text
TrajectoryCertifiedProposalGainSystem.
```

It stores:

```text
proposal/base residual and proxy statistics
nonnegative tolerances and error budgets
safe base contraction
actual trajectory displacement
objective smoothness before update substitution
contractive upper-variable block map
selected-response residual smoothness
squared residual-gradient control
objective lower boundedness
step-size and small-step conditions
```

It derives rather than assumes:

```text
accept/fallback decision
selected residual and selected gain
zero gain on fallback
residual envelope Q
combined contraction error eps
feasibility of the gain-aware error scale
canonical Young scale and step norm
upper-block displacement control
post-substitution objective descent
final gain-aware residual recursion
all Lyapunov coefficient inequalities
finite-horizon and rate conclusions
```

In particular, the public theorem does not accept the final coefficient bounds as
independent fields.

## 3. Gain-adjusted rate

Define

```text
J_t = ||G_t||^2 + lambda^2 * CR * R_t.
```

Lean verifies

```text
eta/4 * sum J_t
  <= accumulatedRhs(T) - Cgain * sum Gamma_t,
```

and therefore an average and same-horizon existence bound with the same
right-hand side.

It also verifies

```text
gainAdjustedRhs(T) <= accumulatedRhs(T),
```

with strict inequality whenever

```text
0 < sum_{t<T} Gamma_t.
```

This is selected-trajectory tightening, not counterfactual online-versus-baseline
trajectory dominance.

Principal declarations:

```text
CertifiedGainStepSystem.joint_average_bound_with_gain
CertifiedGainStepSystem.exists_joint_certificate_with_gain
CertifiedGainStepSystem.gainAdjustedRhs_lt_accumulatedRhs_of_positive_gain
TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_joint_certificate_with_gain
```

## 4. Restricted response and proximal instantiation

Lean checks:

```text
represented restricted minimizer and value
uniqueness under positive quadratic growth
local differentiable stationary-branch envelope identity
response-distance and objective-gap error bounds
strong-monotonicity response certificates
proximal domination of local hypomonotonicity
contractive fixed-point/projected-response residual certificates
```

The concrete proximal local-response model assumes

```text
rho > curvature
local hypomonotonicity
stationarity of the represented response
response-Lipschitz upper/value partial gradients.
```

For

```text
R_rho(x,xi) = ||g_x(xi) + rho * (xi-reference_x)||^2,
```

Lean proves

```text
||gradV(x) - gradXH(x,xi)||^2
  <= L^2 / (rho-curvature)^2 * R_rho(x,xi).
```

Principal declarations:

```text
ProximalRestrictedValueModel.eq_response_of_stationary
ProximalRestrictedValueModel.r2
RestrictedValueProposalData.baseline_error_bound_of_proximal
RestrictedValueProposalData.baseline_error_bound_of_proximal_common_scale
```

## 5. Gradient semantics

`ValueGradientProposalData` defines true base/proposal errors from represented
value-gradient vectors. The selector chooses `gradOnline_t`, and Lean verifies

```text
eOnline_t = ||gradV_t - gradOnline_t||^2.
```

For an isometric ambient embedding,

```text
Err_t = lambda * embed (gradV_t - gradOnline_t)
```

satisfies

```text
||Err_t||^2 = lambda^2 * eOnline_t.
```

The fixed-penalty component theorem checks that gradients of

```text
outer + lambda * (lower - value)
```

compose into

```text
gradOuter + lambda * (gradLower - gradValue).
```

The coupling theorem then proves

```text
G_t + Err_t
  = gradOuter_t + lambda * (gradLower_t - embed gradOnline_t).
```

Thus the actual update direction replaces the exact value-gradient component by
the certificate-selected response gradient.

## 6. Deterministic consequence regimes

Lean distinguishes three regimes.

### Summable perturbations

```text
same-iterate O(1/T) rate
||G_t|| -> 0
R_t -> 0
Gamma_t -> 0
```

If `G_t` is certified as the actual objective gradient, then

```text
||gradient objective (z_t)|| -> 0.
```

The horizon

```text
4 * summableRhs <= epsilon^2 * eta * T
```

yields an iterate with

```text
||gradient objective (z_t)|| <= epsilon
R_t <= epsilon^2 / (lambda^2 * CR).
```

### Cesaro-vanishing perturbations

```text
average ||G_t||^2 -> 0
average R_t -> 0
```

and, with objective-gradient semantics,

```text
average ||gradient objective (z_t)||^2 -> 0.
```

### Persistent bounded perturbations

If

```text
Ceps * eps_t + Cb * b_t + Cd * d_t <= floor,
```

Lean proves an explicit average and same-iterate stationarity/residual
neighborhood. Persistent noise is not promoted to pointwise zero-error
convergence.

## 7. Stochastic expectation-level layer

`CenteredNoiseMoment` checks the scalar second-moment consequence of

```text
zero cross moment
bounded noise second moment.
```

`StochasticExpectedGainSystem` stores expectation-level one-step objective,
residual, and envelope interfaces and derives

```text
eta/4 * sum E||G_t||^2
  + Cgain * sum E Gamma_t
  + eta * lambda^2 * CR / 4 * sum E R_t
  <= expected initial gap
     + certificate-error budgets
     + Csigma * sum sigma_t^2,
```

where

```text
Csigma = LP * eta^2 / 2 + alpha * Aeta.
```

It also checks gain-adjusted expected average and same-horizon existence bounds.

With zero certificate bias and

```text
Aeta = eta / (2*sqrt(2)*lambda) + LR*eta^2/2,
```

`StochasticVarianceRate.lean` verifies

```text
4*Csigma/eta
  = eta * (
      2*LP
      + sqrt(2)*lambda*CR/theta
      + 2*lambda^2*CR*LR*eta/theta
    ),
```

which gives the explicit form

```text
O(1/(eta*T) + eta*sigma^2)
```

when the bracketed coefficient is bounded.

The stochastic development is expectation-level. It does not formalize a
specific probability space, filtration, mini-batch sampler, measurability proof,
or high-probability concentration theorem.

## 8. Parameter and proxy calibration coverage

Lean checks the manuscript constants

```text
mu      = 1 / (sqrt(2) * lambda)
Aeta    = eta / (2 * sqrt(2) * lambda) + LR * eta^2 / 2
betaEta = sqrt(2) * lambda * eta + lambda^2 * LR * eta^2
```

and a readable sufficient step-size bound for `LR > 0`:

```text
eta <= min(
  theta / (8 * CR * sqrt(2) * lambda),
  sqrt(theta / (8 * CR * lambda^2 * LR))
).
```

For proxy calibration, if

```text
||gProxy-gValue|| <= delta
||gCandidate-gValue|| <= B,
```

Lean proves

```text
| ||gCandidate-gProxy||^2 - ||gCandidate-gValue||^2 |
  <= delta * (2*B + delta).
```

Proposal/base and sequence-level asymmetric forms are included.

## 9. Stable paper-facing theorem names

`OUSVRBLO/ICMLTheoryPackage.lean` exports:

```text
ICMLTheoryPackage.fallback_safe_finite_horizon
ICMLTheoryPackage.certified_gain_same_iterate
ICMLTheoryPackage.certified_gain_objective_gradient_same_iterate
ICMLTheoryPackage.positive_gain_strictly_tightens
ICMLTheoryPackage.proximal_response_error_certificate
ICMLTheoryPackage.proximal_baseline_sequence_certificate
ICMLTheoryPackage.stochastic_expected_finite_horizon
ICMLTheoryPackage.stochastic_expected_gain_adjusted_average
ICMLTheoryPackage.stochastic_variance_rate
```

These are thin aliases of the fully checked theorem stack and introduce no new
assumptions.

## 10. Remaining analytic boundary

The following remain local or model-specific interfaces rather than globally
proved facts for a real LLM/LoRA system:

```text
local smoothness and lower boundedness of the concrete surrogate
trajectory region with calibrated response regularity constants
base residual contraction for a concrete optimizer
residual smoothness and residual-gradient calibration
regularity of the selected restricted response branch
specific neural proxy-gradient accuracy bounds
a concrete probability space and mini-batch filtration
projected main-variable gradient-mapping theory
original BLO KKT or general nonconvex BLO global convergence
convergence of the iterates to a unique point
numerical extraction and floating-point stability of the proof-level selector
```

The checked result is therefore a restricted/local fixed-penalty theorem with
certificate-generated fallback safety, gain-adjusted selected-trajectory bounds,
a proximal response instantiation, and an expectation-level stochastic variance
budget.
