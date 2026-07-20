# OUSVR-BLO Lean formalization

This repository formalizes the certificate-sensitive proof stack of a
safeguarded online value-anchor theorem for fixed-penalty value-function BLO.
The primary checked claim is finite-horizon stationarity of a restricted/local
value surrogate under explicit analytic and acceptance certificates.

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

raw learned proposal statistics
  + residual-safety test
  + proxy-improvement test
  + nonnegative calibrated-margin test
  => explicit accept/fallback decision
  => selected residual Ronline and selected gain Gamma

safe base contraction + accepted-response tolerance
  => common residual certificate envelope Q

baseline residual control + asymmetric proxy calibration
  => eOnline <= CR * Q + b - Gamma
  => certified squared inexact-gradient error bound

actual trajectory update
  + local surrogate smoothness before substitution
  + contractive upper-block map
  => inexact surrogate descent and displacement control

residual smoothness + squared residual-gradient control
  => raw residual compatibility
  => safety and gain-aware residual drift

CR * beta <= theta / 4
  => all advertised Lyapunov coefficient bounds

all preceding certificates
  => exact finite-horizon stationarity, residual, and gain budget
  => same-iterate O(1/T), best-iterate, and pointwise consequences
```

The exact enhanced budget is

```text
(eta / 4) * sum Gsq
  + (eta * lam^2 * CR / 4) * sum R
  + Cgain * sum Gamma
  <= initial Lyapunov gap + accumulated certificate errors,
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
proximal and contraction-residual accounting, explicit proposal selection,
residual safeguard closure, sequence-level calibrated proxy algebra,
trajectory substitution, Hilbert-space inexact descent,
residual-smoothness-to-drift propagation, finite-horizon telescoping,
same-iterate and best-iterate certificates, explicit summable-error rates, and
pointwise convergence of the stationarity measure and response residual.

The repository does not prove that a real LLM/LoRA training system automatically
satisfies the local smoothness, hypomonotonicity, contraction, response
regularity, proxy calibration, or residual-gradient premises. It also does not
prove general nonconvex BLO global convergence, original BLO KKT convergence,
projected/stochastic main-variable correctness, or convergence of the iterates
to a unique point.

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
- `OUSVRBLO/AcceptedResponseSelector.lean`: explicit proposal/fallback branch,
  selected residual, selected true error, and zero-gain fallback.
- `OUSVRBLO/CertifiedProposalAcceptance.lean`: defines the acceptance decision
  from residual safety, proxy improvement, and calibrated-margin nonnegativity.
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
- `OUSVRBLO/EndToEndCertifiedGain.lean`: combines safeguard, sequence proxy,
  local surrogate smoothness, and residual smoothness into the gain budget.
- `OUSVRBLO/SelectedEndToEndCertifiedGain.lean`: starts from the actual base and
  selected-response residuals rather than pre-enlarged envelope premises.
- `OUSVRBLO/CanonicalSelectedEndToEndCertifiedGain.lean`: defines
  `H = sqrt (CR * Q + b)` and `stepNorm = norm (G + Err)` internally.
- `OUSVRBLO/TrajectoryCertifiedProposalGain.lean`: derives the canonical theorem
  from the actual deterministic trajectory update, smoothness before
  substitution, and a contractive upper-variable block map.
- `OUSVRBLO/EndToEndCorollaries.lean`: same-iterate and pointwise consequences
  for the certificate-facing end-to-end system.
- `OUSVRBLO/TrajectoryCertifiedProposalCorollaries.lean`: trajectory-facing
  same-iterate `O(1/T)` and pointwise stationarity/residual/gain consequences.
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
- `docs/OUSVR_BLO_CERTIFIED_THEORY.md`: revised theorem and Lean theorem map.
- `docs/END_TO_END_CERTIFIED_THEOREM.md`: certificate-facing theorem and
  finite-time consequence map.
- `docs/EXPLICIT_ACCEPTANCE_AND_CANONICAL_THEOREM.md`: explicit accept/fallback
  proof, natural base-residual interface, and canonical auxiliary definitions.
- `docs/TRAJECTORY_CERTIFICATE_CLOSURE.md`: actual-update and pre-substitution
  smoothness closure into the canonical theorem.
- `docs/RESTRICTED_RESPONSE_CERTIFICATES.md`: local response, envelope, and R2
  certificate derivations.
- `docs/FINITE_TIME_AND_POINTWISE_CERTIFICATES.md`: same-iterate, explicit-rate,
  and pointwise consequence map.
- `docs/FORMALIZATION_SCOPE.md`: precise manuscript-to-Lean coverage boundary.
