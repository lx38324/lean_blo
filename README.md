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

asymmetric proxy calibration + baseline residual control
  => nonnegative uncertainty-adjusted true gain Gamma
  => certified squared inexact-gradient error bound

surrogate smoothness + squared value-gradient error control
  => inexact surrogate descent

residual smoothness + squared residual-gradient control + displacement control
  => raw residual compatibility
  => safety and gain-aware residual drift

CR * beta <= theta / 4
  => all advertised Lyapunov coefficient bounds

safeguard + sequence proxy + analytic certificates
  => end-to-end certified-gain system
  => finite-horizon stationarity, residual, and gain budget
  => same-iterate O(1/T) and pointwise consequences
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
proximal and contraction-residual accounting, residual safeguard closure,
sequence-level calibrated proxy algebra, Hilbert-space inexact descent,
residual-smoothness-to-drift propagation, finite-horizon telescoping,
same-iterate and best-iterate certificates, explicit summable-error rates, and
pointwise convergence of the stationarity measure and response residual.

The repository does not prove that a real LLM/LoRA training system automatically
satisfies the local smoothness, hypomonotonicity, contraction, response
regularity, proxy calibration, or residual-gradient premises. It also does not
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
- `OUSVRBLO/ProxyCertificate.lean`: scalar asymmetric calibration and fallback
  closure into the true nonnegative gain `Gamma`.
- `OUSVRBLO/ProxySequenceCertificate.lean`: sequence proxy comparison and
  baseline residual control produce the certified inexact-gradient error bound.
- `OUSVRBLO/InexactDescent.lean`: Hilbert-space smoothness to safety and
  gain-aware descent interfaces.
- `OUSVRBLO/ResidualSmoothnessCertificate.lean`: residual smoothness, squared
  residual-gradient control, and displacement control produce raw drift.
- `OUSVRBLO/ResidualDrift.lean`: raw residual compatibility to safety and
  gain-aware drift recursions.
- `OUSVRBLO/AnalyticClosure.lean`: composed analytic fallback-safe theorem.
- `OUSVRBLO/AnalyticGainClosure.lean`: composed analytic certified-gain theorem.
- `OUSVRBLO/SmoothResidualAnalyticClosure.lean`: removes `raw_drift` as a public
  premise by composing residual smoothness directly into both analytic systems.
- `OUSVRBLO/EndToEndCertifiedGain.lean`: packages the concrete safeguard,
  sequence proxy, local surrogate smoothness, and residual smoothness premises
  into the exact and simplified certified-gain budgets.
- `OUSVRBLO/EndToEndCorollaries.lean`: gives the same-iterate certificate and
  pointwise stationarity, residual, and gain consequences under summable base
  contraction, acceptance-tolerance, bias, and drift errors.
- `OUSVRBLO/CertifiedSafety.lean`: public fallback-safe finite-horizon theorem.
- `OUSVRBLO/CertifiedGainDescent.lean`: exact and simplified gain budgets.
- `OUSVRBLO/FiniteTimeCorollaries.lean`: best-iterate stationarity and residual
  guarantees.
- `OUSVRBLO/JointCertificates.lean`: same-iterate stationarity/residual
  certificates and exact gain-budget density accounting.
- `OUSVRBLO/Asymptotics.lean`: bounded-partial-sum and average-to-zero
  corollaries for stationarity, residual, and certified gain.
- `OUSVRBLO/SummableCorollaries.lean`: derives the bounded accumulated budget
  from summable nonnegative perturbations.
- `OUSVRBLO/SummableRates.lean`: explicit `O(1 / T)` average and best-iterate
  bounds under summable perturbations.
- `OUSVRBLO/PointwiseAsymptotics.lean`: summability and pointwise convergence of
  stationarity, residual, and gain sequences.
- `OUSVRBLO/AnalyticPointwise.lean`: converts squared stationarity convergence
  into `norm G_t -> 0` for the Hilbert-space analytic systems.
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
- `docs/END_TO_END_CERTIFIED_THEOREM.md`: highest-level certificate-facing
  theorem, same-iterate rate, and pointwise consequence map.
- `docs/RESTRICTED_RESPONSE_CERTIFICATES.md`: local response, envelope, and R2
  certificate derivations.
- `docs/FINITE_TIME_AND_POINTWISE_CERTIFICATES.md`: same-iterate, explicit-rate,
  and pointwise consequence map.
- `docs/FORMALIZATION_SCOPE.md`: precise manuscript-to-Lean coverage boundary.
