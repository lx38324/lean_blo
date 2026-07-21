# OUSVR-BLO Lean formalization

This repository formalizes a certificate-sensitive theorem stack for a
safeguarded online value-anchor method applied to a restricted/local
fixed-penalty value-function BLO surrogate.

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

The package contains four principal results.

### 1. Fallback-safe finite-horizon stationarity

For the selected trajectory, Lean checks

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

Stable declaration:

```text
ICMLTheoryPackage.fallback_safe_finite_horizon
```

### 2. Gain-adjusted selected-trajectory rate

Define

```text
J_t = ||G_t||^2 + lambda^2 * CR * R_t.
```

The exact budget gives

```text
eta/4 * sum J_t
  <= accumulatedRhs(T) - Cgain * sum Gamma_t.
```

Hence

```text
average J_t
  <= 4 * (accumulatedRhs(T) - Cgain * sum Gamma_t) / (eta * T),
```

with a same-horizon existence theorem. Lean also verifies that this numerator is
never larger than the safety-only numerator and is strictly smaller whenever
positive certified gain accumulates.

Stable declarations:

```text
ICMLTheoryPackage.certified_gain_same_iterate
ICMLTheoryPackage.certified_gain_objective_gradient_same_iterate
ICMLTheoryPackage.positive_gain_strictly_tightens
```

This is a selected-trajectory guarantee. It is not a comparison between two
counterfactual online and baseline trajectories.

### 3. Proximal local-response instantiation

For

```text
G_rho,x(xi) = g_x(xi) + rho * (xi - reference_x),
```

assume local `kappa`-hypomonotonicity, `rho > kappa`, stationarity of the
represented response, and response-Lipschitz upper/value partial gradients with
constant `L`.

With

```text
R_rho(x,xi) = ||G_rho,x(xi)||^2,
```

Lean proves

```text
||gradV(x) - gradXH(x,xi)||^2
  <= L^2 / (rho-kappa)^2 * R_rho(x,xi).
```

Thus the response-error coefficient is explicitly

```text
CE = L^2 / (rho-kappa)^2.
```

Stable declarations:

```text
ICMLTheoryPackage.proximal_response_error_certificate
ICMLTheoryPackage.proximal_baseline_sequence_certificate
```

### 4. Stochastic expectation-level rate

A centered perturbation moment interface checks

```text
E_t ||G_t + E_t + W_t||^2
  <= ||G_t + E_t||^2 + sigma_t^2
```

from a zero cross moment and a bounded second moment.

With

```text
Csigma = LP * eta^2 / 2 + alpha * Aeta,
```

Lean proves the expected budget

```text
eta/4 * sum E||G_t||^2
  + Cgain * sum E Gamma_t
  + eta * lambda^2 * CR / 4 * sum E R_t
  <= expected initial gap
     + certificate-error budgets
     + Csigma * sum sigma_t^2.
```

For zero certificate bias and

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
    ).
```

Therefore the expected stationarity/residual rate has the explicit form

```text
O(1/(eta*T) + eta*sigma^2)
```

when the bracketed coefficient is bounded.

Stable declarations:

```text
ICMLTheoryPackage.stochastic_expected_finite_horizon
ICMLTheoryPackage.stochastic_expected_gain_adjusted_average
ICMLTheoryPackage.stochastic_variance_rate
```

## Primary checked chain

```text
restricted minimizer + differentiable stationary response branch
  => represented local value gradient

quadratic growth / strong monotonicity / proximal domination /
contractive response map
  => response-distance and value-gradient error certificates

restricted value-gradient interface + feasible base/proposal responses
  => actual base/proposal partial-gradient sequences

proposal residual + calibrated proxy statistics
  => proof-level explicit accept/fallback selector
  => selected residual Ronline, selected true error eOnline,
     and nonnegative uncertainty-adjusted gain Gamma

safe base contraction + residual acceptance tolerance
  => Q = Rbase + tauR
  => Rbase <= Q, Ronline <= Q,
     Q <= (1-theta) R + epsBase + tauR

base residual-to-error control + proxy calibration
  => eOnline <= CR * Q + b - Gamma
  => 0 <= Gamma <= eBase
  => 0 <= CR * Q + b - Gamma

selected value-gradient vector + isometric ambient embedding
  => ||Err||^2 = lambda^2 * eOnline

fixed-penalty component gradients + value-gradient coupling
  => G = gradOuter + lambda * (gradLower - embed gradV)
  => G + Err = gradOuter + lambda * (gradLower - embed gradOnline)

actual trajectory update + objective smoothness before substitution
  + contractive upper-variable block map
  => inexact descent and upper-block displacement control

residual smoothness + squared residual-gradient control
  => gain-aware residual drift

CR * beta <= theta / 4
  => every advertised Lyapunov coefficient bound
```

The manuscript parameterization is checked exactly:

```text
mu      = 1 / (sqrt(2) * lambda),
Aeta    = eta / (2 * sqrt(2) * lambda) + LR * eta^2 / 2,
betaEta = sqrt(2) * lambda * eta + lambda^2 * LR * eta^2.
```

A readable sufficient step-size condition is also checked for `LR > 0`:

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
  => same-iterate O(1/T) rate and pointwise measure convergence

Cesaro-vanishing perturbations
  => average stationarity and residual convergence

persistent uniformly bounded perturbations
  => explicit stationarity/residual neighborhood
```

If `G_t` is certified as the actual objective gradient, the horizon

```text
4 * summableRhs <= epsilon^2 * eta * T
```

yields an iterate satisfying

```text
||gradient objective (z_t)|| <= epsilon,
R_t <= epsilon^2 / (lambda^2 * CR).
```

Thus the deterministic gradient-norm stationarity dependence is
`O(epsilon^-2)`.

## Semantic and claim boundary

Lean verifies coefficient accounting, explicit selector algebra, restricted-
response sufficient conditions, trajectory substitution, fixed-penalty gradient
composition and value-gradient coupling, finite-horizon telescoping, gain-
adjusted rates, proximal response instantiation, and expectation-level
stochastic variance accounting.

The selector is defined by deciding real inequalities inside a `noncomputable`
section. It is a proof-level mathematical selector, not an extracted floating-
point implementation.

The repository does not prove that a concrete LLM/LoRA training system
automatically satisfies local smoothness, response regularity, calibration,
strong monotonicity, contraction, residual-gradient, or stochastic sampling
premises. It also does not prove:

```text
global nonconvex lower-level optimality
original BLO KKT convergence
global or set-valued Danskin theory
counterfactual online-versus-baseline trajectory dominance
projected main-variable stationarity
a concrete neural mini-batch filtration model
convergence of the iterates to a unique point
```

The value-response model is restricted/local. An arbitrary local response is not
identified with the global value function of the original nonconvex lower
problem.

## Build

Install `elan`, then use the committed `lean-toolchain` and
`lake-manifest.json`:

```bash
lake exe cache get
lake build
bash scripts/check_no_placeholder.sh
python3 scripts/check_docs_sanity.py
python3 scripts/check_lean_build_log.py
```

Run `lake update` only when intentionally refreshing and committing the locked
dependency graph.

## Documentation map

- `docs/ICML_METHOD_THEORY_PACKAGE.md`: compact paper-facing theory statement.
- `docs/ICML_THEORY_DEPENDENCY_AUDIT.md`: assumption ownership and theorem map.
- `docs/OUSVR_BLO_CERTIFIED_THEORY.md`: full mathematical derivation.
- `docs/FORMALIZATION_SCOPE.md`: exact checked and unchecked boundaries.
- `docs/PROXY_GRADIENT_CALIBRATION.md`: vector proxy sufficient condition.
- `docs/STOCHASTIC_EXPECTED_RATE.md`: stochastic expected-rate derivation.

## Main Lean files

### Paper-facing exports

- `ICMLTheoryPackage.lean`: stable names for the four ICML theory results.

### Certificate and response layers

- `LocalSurrogate.lean` and `RestrictedEnvelope.lean`: restricted response and
  local branch-envelope interfaces.
- `ResponseErrorBound.lean`, `StrongMonotonicityCertificate.lean`,
  `ProximalResponseCertificate.lean`, and `ProximalLocalInstantiation.lean`:
  response-error sufficient conditions and the concrete proximal class.
- `RestrictedValueProposalData.lean`: base/proposal gradient sequences from the
  restricted value interface.
- `QuadraticResponseExample.lean`: non-vacuous scalar model.

### Proposal, proxy, and safeguard layers

- `SafeguardCertificate.lean`: common residual envelope.
- `ProxyCertificate.lean`, `ProxySequenceCertificate.lean`, and
  `ProxyCalibrationFromGradient.lean`: scalar, sequence, and vector-gradient
  calibration certificates.
- `AcceptedResponseSelector.lean` and `CertifiedProposalAcceptance.lean`:
  explicit accept/fallback rule.
- `CertifiedGainFeasibility.lean`: gain and error-scale feasibility.
- `ValueGradientErrorEmbedding.lean`: exact ambient error norm identity.
- `CommonResidualScale.lean`: common affine residual scale.

### Analytic, trajectory, and Lyapunov layers

- `ManuscriptParameters.lean`, `ParameterBounds.lean`, and
  `ExplicitStepSize.lean`: exact constants and coefficient bounds.
- `InexactDescent.lean`, `ResidualSmoothnessCertificate.lean`, and
  `ResidualDrift.lean`: analytic descent and drift closure.
- `CertifiedSafety.lean` and `CertifiedGainDescent.lean`: scalar budgets.
- `EndToEndCertifiedGain.lean`, `SelectedEndToEndCertifiedGain.lean`,
  `CanonicalSelectedEndToEndCertifiedGain.lean`, and
  `TrajectoryCertifiedProposalGain.lean`: progressively natural theorem APIs.
- `ValueGradientTrajectory.lean`, `TrajectoryGradientSemantics.lean`,
  `FixedPenaltyGradientSemantics.lean`, and
  `ValueGradientFixedPenaltyCoupling.lean`: gradient semantics and trajectory
  coupling.

### Rate layers

- `GainAdjustedRates.lean`: exact gain-adjusted selected-trajectory rate.
- `FiniteTimeCorollaries.lean`, `JointCertificates.lean`,
  `IterationComplexity.lean`, and `TrajectoryIterationComplexity.lean`:
  finite-time and same-iterate results.
- `SummableCorollaries.lean`, `SummableRates.lean`,
  `CesaroPerturbationCorollaries.lean`, `PointwiseAsymptotics.lean`, and
  `PersistentErrorFloor.lean`: deterministic perturbation regimes.
- `StochasticExpectedGain.lean` and `StochasticVarianceRate.lean`:
  expectation-level stochastic budgets and explicit variance rates.
