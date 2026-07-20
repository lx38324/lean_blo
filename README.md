# OUSVR-BLO Lean formalization

This repository formalizes a certificate-sensitive theorem stack for a
safeguarded online value-anchor method applied to a restricted/local
fixed-penalty value-function BLO surrogate.

The machine-learning-facing statement is: a learned updater may propose an
arbitrary response, but only a response passing explicit residual-safety and
calibrated value-gradient tests is used.  A rejected proposal falls back to the
safe base response with zero certified gain.

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
  => ||Err||^2 = lam^2 * eOnline

fixed-penalty component gradients + value-gradient coupling
  => G = gradOuter + lam * (gradLower - embed gradV)
  => G + Err = gradOuter + lam * (gradLower - embed gradOnline)

actual trajectory update + objective smoothness before substitution
  + contractive upper-variable block map
  => inexact descent and upper-block displacement control

residual smoothness + squared residual-gradient control
  => gain-aware residual drift

CR * beta <= theta / 4
  => every advertised Lyapunov coefficient bound

all preceding certificates
  => finite-horizon stationarity/residual/gain budget
  => same-iterate O(1/T), O(epsilon^-2) gradient-norm complexity,
     and pointwise consequences under summable perturbations

persistent uniformly bounded perturbations
  => explicit stationarity/residual error floor
```

The exact enhanced budget is

```text
(eta / 4) * sum Gsq
  + Cgain * sum Gamma
  + (eta * lam^2 * CR / 4) * sum R
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

A transparent sufficient decomposition of the small-step condition is

```text
CR * sqrt(2) * lam * eta <= theta / 8,
CR * lam^2 * LR * eta^2 <= theta / 8.
```

For summable certificate perturbations, one and the same iterate satisfies

```text
exists t < T,
  ||G t||^2 + lam^2 * CR * R t
    <= 4 * summableRhs / (eta * T).
```

If `G t` is certified as the actual objective gradient and

```text
4 * summableRhs <= epsilon^2 * eta * T,
```

then some `t < T` satisfies

```text
||gradient objective (z t)|| <= epsilon,
R t <= epsilon^2 / (lam^2 * CR).
```

Thus the checked gradient-norm stationarity dependence is the standard
`O(epsilon^-2)`.

For persistent bounded errors, define

```text
weightedPerturbation t
  = Ceps * eps t + Cb * b t + Cd * d t.
```

If `weightedPerturbation t <= floor` for every `t`, Lean proves

```text
exists t < T,
  ||G t||^2 + lam^2 * CR * R t
    <= 4 * (Psi 0 - Pstar) / (eta * T) + 4 * floor / eta.
```

This separates summable-error convergence from stochastic or fixed-tolerance
neighborhood guarantees.

## Semantic and claim boundary

Lean verifies the scalar coefficient accounting, explicit selector algebra,
restricted-response sufficient conditions, trajectory substitution,
fixed-penalty gradient composition and value-gradient coupling, finite-horizon
telescoping, same-iterate rates, pointwise consequences, and persistent-error
floors.

The selector built from inequalities over real numbers is a proof-level object in
a `noncomputable` section.  The repository does not claim extraction of a
floating-point acceptance implementation.

The theorem uses one common affine residual scale `CR * Q + b`.  This need not
mean that value-gradient error and residual-gradient drift have identical raw
constants: Lean verifies that two separately calibrated nonnegative affine
scales can be dominated by a common maximum coefficient and maximum bias, and
that the pointwise maximum of two nonnegative summable biases remains summable.

The repository does **not** prove that a concrete LLM/LoRA training system
automatically satisfies local smoothness, response regularity, calibration,
strong monotonicity, contraction, or residual-gradient premises.  It also does
not prove projected/stochastic main-variable correctness, global nonconvex lower
optimality, original BLO KKT convergence, or convergence of the iterates to a
unique point.

The value-response model is restricted/local.  An arbitrary local response is
not identified with the global value function of the original nonconvex lower
problem, and the branch-envelope result is not a general nonsmooth or set-valued
Danskin theorem.

## Build

Install `elan`, then use the committed `lean-toolchain` and
`lake-manifest.json`:

```bash
lake exe cache get
lake build
bash scripts/check_no_placeholder.sh
```

Run `lake update` only when intentionally refreshing and committing the locked
dependency graph.

## Main files

### Certificate and response layers

- `LocalSurrogate.lean`: restricted minimizer and abstract value-gradient
  interface.
- `RestrictedEnvelope.lean`: quadratic-growth uniqueness and differentiable
  stationary-branch envelope identity.
- `ResponseErrorBound.lean`: response-distance and objective-gap R2 sufficient
  conditions.
- `StrongMonotonicityCertificate.lean`: response uniqueness and lower-gradient
  residual bounds.
- `ProximalResponseCertificate.lean`: proximal regularization dominates local
  negative curvature.
- `ContractionResidualCertificate.lean`: fixed-point/projected-response residual
  certificates.
- `RestrictedValueProposalData.lean`: generates base/proposal gradient data
  directly from a restricted value-gradient interface and feasible responses.
- `QuadraticResponseExample.lean`: concrete non-vacuous scalar model.

### Proposal, proxy, and safeguard layers

- `SafeguardCertificate.lean`: common residual envelope.
- `ProxyCertificate.lean` and `ProxySequenceCertificate.lean`: calibrated scalar
  and sequence gain certificates.
- `AcceptedResponseSelector.lean`: explicit accepted/fallback branch and selected
  residual/error/gain.
- `CertifiedProposalAcceptance.lean`: constructs the Boolean decision from the
  three certificate tests.
- `CertifiedGainFeasibility.lean`: proves `0 <= Gamma <= eBase` and nonnegativity
  of the gain-aware error scale.
- `ValueGradientErrorEmbedding.lean`: defines true errors from value-gradient
  vectors and proves the exact ambient error norm identity.
- `CommonResidualScale.lean`: dominates independently calibrated affine residual
  scales by one common scale while preserving summability.

### Analytic and Lyapunov layers

- `ManuscriptParameters.lean` and `ParameterBounds.lean`: exact constants and all
  coefficient bounds from the single small-step condition.
- `ExplicitStepSize.lean`: split linear/quadratic sufficient conditions for the
  manuscript small-step inequality.
- `InexactDescent.lean`: Hilbert-space inexact descent.
- `ResidualSmoothnessCertificate.lean` and `ResidualDrift.lean`: residual
  smoothness to gain-aware drift.
- `CertifiedSafety.lean` and `CertifiedGainDescent.lean`: public scalar safety and
  gain budgets.
- `AnalyticClosure.lean`, `AnalyticGainClosure.lean`, and
  `SmoothResidualAnalyticClosure.lean`: composed analytic systems.
- `EndToEndCertifiedGain.lean`, `SelectedEndToEndCertifiedGain.lean`, and
  `CanonicalSelectedEndToEndCertifiedGain.lean`: certificate-facing closure with
  increasingly natural public assumptions.

### Trajectory and gradient-semantics layers

- `TrajectoryCertifiedProposalGain.lean`: derives the theorem from the actual
  deterministic update and pre-substitution smoothness.
- `ValueGradientTrajectory.lean`: defines the inexact update error from the
  selected value-gradient approximation.
- `TrajectoryGradientSemantics.lean`: identifies `G t` with the actual objective
  gradient when a local `HasGradientAt` certificate is supplied.
- `FixedPenaltyGradientSemantics.lean`: composes gradients for
  `outer + lam * (lower - value)` and generates the trajectory gradient
  certificate from its components.
- `ValueGradientFixedPenaltyCoupling.lean`: proves that the represented value
  gradient used by the error layer is the same value component occurring in the
  fixed-penalty objective gradient, and rewrites the actual update with the
  selected response gradient.

### Finite-time and asymptotic layers

- `FiniteTimeCorollaries.lean`, `JointCertificates.lean`,
  `SummableCorollaries.lean`, and `SummableRates.lean`: averaged, best-iterate,
  same-iterate, and explicit-rate results.
- `IterationComplexity.lean` and `TrajectoryIterationComplexity.lean`: explicit
  tolerance horizons and `O(epsilon^-2)` gradient-norm complexity.
- `PointwiseAsymptotics.lean`, `AnalyticPointwise.lean`,
  `EndToEndCorollaries.lean`, and `TrajectoryCertifiedProposalCorollaries.lean`:
  summability and pointwise stationarity/residual/gain conclusions.
- `PersistentErrorFloor.lean`: average and same-iterate neighborhood bounds under
  persistent uniformly bounded perturbations.

The current mathematical statement and theorem map are in
`docs/OUSVR_BLO_CERTIFIED_THEORY.md`; the exact coverage boundary is in
`docs/FORMALIZATION_SCOPE.md`.
