# OUSVR-BLO Lean formalization

This repository formalizes the certificate-sensitive proof skeleton of a
safeguarded online value-anchor theorem for fixed-penalty value-function BLO.
The primary checked claim is finite-horizon stationarity of a restricted/local
value surrogate under explicit analytic interfaces.

## Primary checked chain

```text
restricted minimizer + differentiable stationary response branch
  => local value derivative equals the x-partial derivative

quadratic growth, strong monotonicity, or a contractive response map
  => unique represented response + response-distance error bound

response-gradient Lipschitzness
  => residual controls value-gradient approximation error

proximal regularization dominating local negative curvature
  => strong monotonicity of the regularized lower-gradient residual

safe base contraction + accepted-response tolerance
  => common residual certificate envelope Q

asymmetric proxy calibration + acceptance margin
  => nonnegative uncertainty-adjusted true gain Gamma

smoothness + squared value-gradient error control
  => inexact surrogate descent

raw residual compatibility + Young's inequality + step-square control
  => residual drift

CR * beta <= theta / 4
  => all advertised Lyapunov coefficient bounds

one-step descent + drift + envelope contraction
  => finite-horizon stationarity, residual, and gain budgets
  => averaged, best-iterate, bounded-budget, summable-error, and explicit O(1/T)
     guarantees
```

The exact enhanced budget is

```text
(eta / 4) * sum Gsq
  + (eta * lam^2 * CR / 4) * sum R
  + Cgain * sum Gamma
  <= initial Lyapunov gap + accumulated interface errors,
```

where

```text
Cgain = eta * lam^2 / 2 + 2 * alpha * Aeta * lam^2,
eta * lam^2 / 2 <= Cgain <= 3/4 * eta * lam^2.
```

The manuscript parameterization is checked exactly:

```text
mu      = 1 / (sqrt 2 * lam),
Aeta    = eta / (2 * sqrt 2 * lam) + LR * eta^2 / 2,
betaEta = sqrt 2 * lam * eta + lam^2 * LR * eta^2.
```

## Claim boundary

Lean checks coefficient accounting, restricted-response uniqueness under stated
local certificates, the differentiable branch-envelope identity,
residual-to-value-gradient sufficient conditions, strong-monotonicity,
proximal, and contraction-residual accounting, residual safeguard closure,
calibrated proxy algebra, Hilbert-space inexact-descent algebra, scalar
residual-drift propagation, finite-horizon telescoping, averaged and
best-iterate corollaries, and explicit rates under uniformly bounded or
summable perturbation budgets.

The repository does not prove that a real LLM/LoRA training system automatically
satisfies the local smoothness, hypomonotonicity, contraction, response
differentiability, or raw residual-compatibility premises. It also does not
prove general nonconvex BLO global convergence, original BLO KKT convergence,
projected/stochastic training correctness, or convergence of the iterates to a
unique point.

The value-response model is restricted/local: an arbitrary local response is
not identified with the global value function of the original nonconvex lower
problem. The local branch-envelope result is not a general nonsmooth or
set-valued Danskin theorem.

## Build

Install `elan`, then use the committed `lean-toolchain` and
`lake-manifest.json`:

```bash
lake exe cache get
lake build
```

Run `lake update` only when intentionally refreshing and committing the locked
dependency graph. To reject placeholder proofs, run:

```bash
bash scripts/check_no_placeholder.sh
```

## Main files

- `OUSVRBLO/ManuscriptParameters.lean`: exact manuscript `sqrt 2`
  parameterization and constructor from S2.
- `OUSVRBLO/ParameterBounds.lean`: all Lyapunov coefficient bounds from the
  drift parameterization and the single small-step condition.
- `OUSVRBLO/SafeguardCertificate.lean`: safe-base/accepted-response closure into
  one residual envelope `Q`.
- `OUSVRBLO/ProxyCertificate.lean`: asymmetric calibration and fallback closure
  into the true nonnegative gain `Gamma`.
- `OUSVRBLO/InexactDescent.lean`: Hilbert-space smoothness to safety and
  gain-aware descent interfaces.
- `OUSVRBLO/ResidualDrift.lean`: raw residual compatibility to safety and
  gain-aware drift recursions.
- `OUSVRBLO/AnalyticClosure.lean`: composed analytic fallback-safe theorem.
- `OUSVRBLO/AnalyticGainClosure.lean`: composed analytic certified-gain theorem.
- `OUSVRBLO/CertifiedSafety.lean`: public fallback-safe finite-horizon theorem.
- `OUSVRBLO/CertifiedGainDescent.lean`: exact and simplified gain budgets.
- `OUSVRBLO/FiniteTimeCorollaries.lean`: best-iterate stationarity and residual
  guarantees.
- `OUSVRBLO/Asymptotics.lean`: bounded-partial-sum and average-to-zero
  corollaries for stationarity, residual, and certified gain.
- `OUSVRBLO/SummableCorollaries.lean`: derives the bounded accumulated budget
  from summable nonnegative perturbations and gives direct average-convergence
  theorems.
- `OUSVRBLO/SummableRates.lean`: explicit `O(1 / T)` average and best-iterate
  bounds under summable perturbations.
- `OUSVRBLO/LocalSurrogate.lean`: restricted minimizer and abstract
  value-gradient interface boundary.
- `OUSVRBLO/RestrictedEnvelope.lean`: quadratic-growth uniqueness and local
  differentiable branch-envelope theorem.
- `OUSVRBLO/ResponseErrorBound.lean`: response-distance and objective-gap
  sufficient conditions for R2.
- `OUSVRBLO/StrongMonotonicityCertificate.lean`: lower-gradient residual error
  bounds and response uniqueness from strong monotonicity.
- `OUSVRBLO/ProximalResponseCertificate.lean`: proximal regularization dominates
  local negative curvature and produces a computable R2 residual certificate.
- `OUSVRBLO/ContractionResidualCertificate.lean`: contractive fixed-point or
  projected-response residual gives response-distance and R2 certificates.
- `OUSVRBLO/QuadraticResponseExample.lean`: concrete scalar model showing the
  restricted response and R2 assumptions are jointly satisfiable.
- `OUSVRBLO/SafetyDescent.lean`: reusable low-level scalar algebraic core.
- `OUSVRBLO/ImprovementDescent.lean`: legacy nominal-improvement formulation.
- `OUSVRBLO/LyapunovBudget.lean`: budget structures and averaged consequences.
- `docs/OUSVR_BLO_CERTIFIED_THEORY.md`: revised theorem and Lean theorem map.
- `docs/RESTRICTED_RESPONSE_CERTIFICATES.md`: local response, envelope, and R2
  certificate derivations.
- `docs/FORMALIZATION_SCOPE.md`: precise manuscript-to-Lean coverage boundary.
