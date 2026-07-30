# OUSVR-BLO Lean formalization

This repository formalizes a certificate-sensitive theorem stack for a
safeguarded online value-anchor method over a restricted/local fixed-penalty
value-function BLO surrogate.

The machine-learning-facing statement is:

> A learned updater may propose an arbitrary response. The proposal is used only
> when explicit residual-safety, calibrated proxy-improvement, and nonnegative-
> margin tests pass. Otherwise the method falls back to a safe base response and
> assigns zero certified gain to that round.

The development is intended as the theory component of a method-and-experiments
machine-learning paper. It is not presented as a general nonconvex bilevel-
optimization theorem.

## ICML-oriented theory package

Stable paper-facing theorem names are exported from
`OUSVRBLO/ICMLTheoryPackage.lean` under

```text
OUSVRBLO.ICMLTheoryPackage
```

### 1. Fallback-safe finite-horizon theorem

Lean checks

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

Stable declarations:

```text
ICMLTheoryPackage.fallback_safe_finite_horizon
ICMLTheoryPackage.fallback_safe_objective_gradient_finite_horizon
```

The first theorem is stated for the trajectory descent vector `G_t`; the second
requires a `TrajectoryGradientCertificate` and explicitly rewrites it as the
objective gradient.

### 2. Gain-adjusted selected-trajectory rate

For

```text
J_t = ||G_t||^2 + lambda^2 * CR * R_t,
```

Lean proves

```text
eta/4 * sum J_t
  <= accumulatedRhs(T) - Cgain * sum Gamma_t,
```

and an average and same-horizon existence bound with the same numerator. The
numerator is never larger than the safety-only numerator and is strictly smaller
when positive certified gain accumulates.

Stable declarations:

```text
ICMLTheoryPackage.certified_gain_average
ICMLTheoryPackage.certified_gain_same_iterate
ICMLTheoryPackage.certified_gain_objective_gradient_same_iterate
ICMLTheoryPackage.positive_gain_strictly_tightens
```

This is a selected-trajectory guarantee, not counterfactual online-versus-
baseline trajectory dominance.

### 3. Proximal local-response instantiation

For

```text
G_rho,x(xi) = g_x(xi) + rho * (xi - reference_x),
R_rho(x,xi) = ||G_rho,x(xi)||^2,
```

local `kappa`-hypomonotonicity, `rho > kappa`, response stationarity, and
response-Lipschitz upper/value partial gradients imply

```text
||gradV(x) - gradXH(x,xi)||^2
  <= L^2 / (rho-kappa)^2 * R_rho(x,xi).
```

Stable declarations:

```text
ICMLTheoryPackage.proximal_response_error_certificate
ICMLTheoryPackage.proximal_baseline_sequence_certificate
```

### 4. Stochastic expectation-level rate

A centered second-moment interface checks

```text
E_t ||G_t + E_t + W_t||^2
  <= ||G_t + E_t||^2 + sigma_t^2.
```

With

```text
Csigma = LP * eta^2 / 2 + alpha * Aeta,
```

Lean proves an expected finite-horizon budget containing

```text
Csigma * sum sigma_t^2
```

and retaining the accumulated expected certified gain.

For

```text
Aeta = eta / (2*sqrt(2)*lambda) + LR*eta^2/2,
```

Lean checks

```text
4*Csigma/eta
  = eta * (
      2*LP
      + sqrt(2)*lambda*CR/theta
      + 2*lambda^2*CR*LR*eta/theta
    ),
```

so the expected stationarity/residual rate has the explicit form

```text
O(1/(eta*T) + eta*sigma^2)
```

when the bracketed coefficient is bounded.

Stable declarations:

```text
ICMLTheoryPackage.stochastic_expected_finite_horizon
ICMLTheoryPackage.stochastic_expected_gain_adjusted_average
ICMLTheoryPackage.stochastic_expected_same_iterate
ICMLTheoryPackage.stochastic_positive_gain_strictly_tightens
ICMLTheoryPackage.stochastic_variance_rate
```

## Primary checked chain

```text
restricted minimizer + stationary response branch
  => represented local value gradient

response regularity / proximal domination / contraction
  => value-gradient error certificates

proposal statistics + calibrated proxy tests
  => explicit accept/fallback selector
  => selected residual Ronline and nonnegative gain Gamma

safe base contraction + residual tolerance
  => Q = Rbase + tauR
  => Rbase <= Q, Ronline <= Q,
     Q <= (1-theta) R + epsBase + tauR

base residual-to-error control + proxy calibration
  => eOnline <= CR * Q + b - Gamma
  => 0 <= Gamma <= eBase
  => 0 <= CR * Q + b - Gamma

selected value-gradient vector + isometric embedding
  => ||Err||^2 = lambda^2 * eOnline

fixed-penalty gradient semantics
  => G + Err = gradOuter + lambda * (gradLower - embed gradOnline)

trajectory smoothness + residual smoothness + small step
  => gain-aware Lyapunov budget and rates
```

The exact manuscript parameters are

```text
mu      = 1 / (sqrt(2) * lambda),
Aeta    = eta / (2 * sqrt(2) * lambda) + LR * eta^2 / 2,
betaEta = sqrt(2) * lambda * eta + lambda^2 * LR * eta^2.
```

For `LR > 0`, a readable sufficient step-size condition is

```text
eta <= min(
  theta / (8 * CR * sqrt(2) * lambda),
  sqrt(theta / (8 * CR * lambda^2 * LR))
).
```

## Perturbation regimes

The deterministic consequence layer distinguishes:

```text
summable perturbations
  => same-iterate O(1/T) and pointwise measure convergence

Cesaro-vanishing perturbations
  => average stationarity and residual convergence

persistent bounded perturbations
  => explicit stationarity/residual neighborhood
```

With an objective-gradient certificate, the horizon

```text
4 * summableRhs <= epsilon^2 * eta * T
```

yields an iterate satisfying

```text
||gradient objective (z_t)|| <= epsilon,
R_t <= epsilon^2 / (lambda^2 * CR).
```

## Claim boundary

Lean verifies the coefficient accounting, selector algebra, local response
sufficient conditions, trajectory substitution, fixed-penalty gradient
semantics, gain-adjusted rates, proximal instantiation, and expectation-level
stochastic variance accounting.

It does not prove:

```text
global nonconvex lower-level optimality
original BLO KKT convergence
global or set-valued Danskin theory
counterfactual online-versus-baseline trajectory dominance
projected main-variable stationarity
a concrete neural mini-batch filtration model
convergence of the iterates to a unique point
```

The selector is a proof-level object in a `noncomputable` section, not an
extracted floating-point implementation.

## Verification

Use the committed `lean-toolchain` and `lake-manifest.json`:

```bash
bash scripts/verify.sh
```

The script performs the locked root build, placeholder scan, Markdown theorem
sanity check, and Lean build-log diagnostic scan. Run `lake update` only when
intentionally refreshing and committing the dependency graph.

## Documentation

- `docs/ICML_METHOD_THEORY_PACKAGE.md`: compact paper-facing theorem package.
- `docs/ICML_THEORY_DEPENDENCY_AUDIT.md`: assumption ownership and exact theorem
  dependency map.
- `docs/OUSVR_BLO_CERTIFIED_THEORY.md`: full deterministic mathematical derivation.
- `docs/LEGACY_THEORY_MIGRATION.md`: migration from the deprecated
  `Rhat/Delta/zeta` notation to `Q/Gamma`.
- `docs/OBJECTIVE_GRADIENT_SEMANTICS.md`: distinction between the descent-vector
  budget and the actual objective-gradient theorem.
- `docs/STOCHASTIC_EXPECTED_RATE.md`: stochastic rate derivation.
- `docs/STOCHASTIC_GAIN_TIGHTENING.md`: expected gain-adjusted tightening.
- `docs/FORMALIZATION_SCOPE.md`: exact checked and unchecked boundaries.
- `docs/PROXY_GRADIENT_CALIBRATION.md`: vector proxy sufficient condition.

## Main Lean entry points

```text
ICMLTheoryPackage.lean
GainAdjustedRates.lean
ProximalLocalInstantiation.lean
StochasticExpectedGain.lean
StochasticGainAdjustedRates.lean
StochasticVarianceRate.lean
TrajectoryCertifiedProposalGain.lean
ValueGradientFixedPenaltyCoupling.lean
```
