# Formalization scope

This repository formalizes a certificate-facing proof stack for a safeguarded
online value-anchor fixed-penalty stationarity theorem over a restricted/local
value surrogate.

## Public theorem

The learned updater produces a proposal, but the theorem uses an explicit
accept/fallback selector.  At round `t`, acceptance is the conjunction

```text
Rprop_t <= Rbase_t + tauR_t
and ehatProp_t <= ehatBase_t - DeltaHat_t + tauE_t
and 0 <= DeltaHat_t - tauE_t - rhoProp_t - rhoBase_t.
```

The proof-level selector defines

```text
Ronline_t = if accepted then Rprop_t else Rbase_t
Gamma_t   = if accepted
            then DeltaHat_t - tauE_t - rhoProp_t - rhoBase_t
            else 0.
```

The base update and residual tolerance generate

```text
Q_t   = Rbase_t + tauR_t
eps_t = epsBase_t + tauR_t,
```

with

```text
Rbase_t <= Q_t
Ronline_t <= Q_t
Q_t <= (1 - theta) * R_t + eps_t.
```

The natural baseline certificate

```text
eBase_t <= CR * Rbase_t + b_t
```

and asymmetric proxy calibration imply

```text
0 <= Gamma_t <= eBase_t
eOnline_t <= CR * Q_t + b_t - Gamma_t
0 <= CR * Q_t + b_t - Gamma_t.
```

For the selected value-gradient error embedded into the ambient update space,
Lean checks

```text
||Err_t||^2 = lam^2 * eOnline_t.
```

Under the deterministic update, objective smoothness before substitution,
selected-response residual smoothness, residual-gradient control, and
`CR * beta <= theta / 4`, the exact finite-horizon budget is

```text
(eta / 4) * SeqSum T Gsq
  + Cgain * SeqSum T Gamma
  + (eta * lam^2 * CR / 4) * SeqSum T R
  <= Psi 0 - Pstar
     + Ceps * SeqSum T eps
     + Cb * SeqSum T b
     + Cd * SeqSum T d,
```

where

```text
Cgain = eta * lam^2 / 2 + 2 * alpha * Aeta * lam^2,
eta * lam^2 / 2 <= Cgain <= 3/4 * eta * lam^2.
```

The exact manuscript parameters are

```text
mu      = 1 / (sqrt 2 * lam),
Aeta    = eta / (2 * sqrt 2 * lam) + LR * eta^2 / 2,
betaEta = sqrt 2 * lam * eta + lam^2 * LR * eta^2.
```

## Highest-level deterministic assumptions

`TrajectoryCertifiedProposalGainSystem` stores:

- proposal/base residual and proxy statistics;
- nonnegativity of residuals, squared true errors, tolerances, and calibration
  radii;
- safe base contraction;
- the actual update identity
  `z (t + 1) - z t = -eta • (G t + Err t)`;
- a nonnegative objective smoothness constant and local smoothness inequality
  before update substitution;
- a contractive continuous linear upper-variable block map;
- residual smoothness from the actually selected response;
- squared residual-gradient control;
- lower boundedness along the trajectory;
- the single small-step condition.

It derives rather than assumes:

- the accept/fallback decision;
- selected residual, selected true error, and selected gain;
- zero gain on fallback and calibrated gain on acceptance;
- selected residual/error nonnegativity;
- the residual envelope and total contraction error;
- feasibility of the gain-aware error scale;
- the exact ambient inexact-gradient norm identity when the value-gradient
  embedding layer is used;
- `H_t = sqrt (CR * Q_t + b_t)` and its square identity;
- `stepNorm_t = norm (G_t + Err_t)` and the squared-sum estimate;
- upper-block displacement control;
- the post-substitution smoothness inequality;
- the final residual recursion;
- every Lyapunov coefficient inequality;
- finite-time and asymptotic conclusions.

The selector is defined inside a `noncomputable` section because its conditions
are inequalities over real numbers.  This is a proof-level mathematical selector,
not a claim that Lean extracts a floating-point implementation.

## Coverage map

### Restricted response and value-gradient layer

Lean checks:

- represented restricted minimizers and restricted values;
- uniqueness under positive quadratic growth;
- a differentiable stationary-response branch envelope identity;
- response-gradient Lipschitzness plus response-distance control implies R2;
- objective-gap R2 under quadratic growth;
- strong-monotonicity, proximal, and contraction-residual sufficient conditions;
- a scalar quadratic model showing the response assumptions are jointly
  satisfiable.

Principal declarations include:

- `RestrictedValueResponseInterface.response_isMinimizer`;
- `RestrictedValueResponseInterface.eq_response_of_quadratic_growth`;
- `hasFDerivAt_branchValue_of_stationary_response`;
- `RestrictedValueResponseInterface.hasFDerivAt_value_of_stationary_response`;
- `RestrictedValueGradientInterface.r2_of_lipschitz_and_error_bound`;
- `RestrictedValueGradientInterface.r2_of_quadratic_growth`.

`RestrictedValueProposalData` additionally generates the actual base and
proposal partial-gradient sequences from a restricted value-gradient interface
and feasible response sequences.  Its sequence-level baseline R2 certificate
can be generated from either Lipschitz/error-bound assumptions or quadratic
growth.

### Explicit proposal selection and gain feasibility

Principal declarations include:

- `CertifiedProposalData.AcceptanceCondition`;
- `CertifiedProposalData.accept`;
- `CertifiedProposalData.toAcceptedResponseSelector`;
- accepted/rejected residual and gain branch theorems;
- `AcceptedResponseSelector.Ronline_nonneg`;
- `AcceptedResponseSelector.eOnline_nonneg`;
- `AcceptedResponseSelector.true_error_improves`;
- `AcceptedResponseSelector.r2_certified`;
- `AcceptedResponseSelector.Gamma_nonneg`;
- `AcceptedResponseSelector.Gamma_le_base_error`;
- `AcceptedResponseSelector.certified_scale_nonneg`.

On fallback rounds, the sequence proxy package uses proof-only exact baseline
error witnesses after the branch decision.  They do not enter the acceptance
condition.

### Residual envelope and common calibration scale

Lean checks:

- base and selected residuals are bounded by the same envelope;
- the envelope contracts up to `epsBase + tauR`;
- independently calibrated affine bounds
  `C1 * Q + b1` and `C2 * Q + b2` are dominated by
  `max C1 C2 * Q + max b1 b2` when `Q >= 0`;
- the pointwise maximum of two nonnegative summable bias sequences is summable.

Thus the common notation `CR * Q + b_t` does not require the value-gradient and
residual-gradient interfaces to have identical primitive constants.

### Value-gradient error and fixed-penalty gradient semantics

`ValueGradientProposalData` defines

```text
eBase_t = ||gradV_t - gradBase_t||^2
eProp_t = ||gradV_t - gradProp_t||^2.
```

The selector chooses `gradOnline_t`, and Lean verifies

```text
eOnline_t = ||gradV_t - gradOnline_t||^2.
```

For an isometric ambient embedding,

```text
Err_t = lam • embed (gradV_t - gradOnline_t)
```

satisfies the exact identity

```text
||Err_t||^2 = lam^2 * eOnline_t.
```

`FixedPenaltyGradientSemantics.lean` checks that gradients of the components of

```text
outer + lam * (lower - value)
```

compose into

```text
gradOuter + lam • (gradLower - gradValue).
```

A component-level certificate therefore generates the trajectory
`HasGradientAt` certificate used by the objective-gradient stationarity
statements.

### Descent, residual drift, and coefficient accounting

Lean checks:

- exact manuscript parameter identities;
- the single small-step condition implies all Lyapunov coefficient bounds;
- Hilbert-space polarization and inexact descent;
- residual smoothness to raw drift;
- Young's inequality and the final gain-aware residual recursion;
- the favorable gain term appears in both objective descent and residual drift;
- one-step Lyapunov descent telescopes to exact and simplified cumulative
  budgets.

### Finite-time and asymptotic layer

Lean checks:

- averaged and best-iterate stationarity/residual bounds;
- the same-iterate certificate

  ```text
  exists t < T,
    Gsq_t + lam^2 * CR * R_t <= 4 * budget / (eta * T);
  ```

- explicit tolerance horizons;
- under summable perturbations,
  `Gsq`, `R`, and nonnegative `Gamma` are summable and converge pointwise to
  zero;
- if `G_t` is certified as the objective gradient, then
  `||gradient objective (z_t)|| -> 0`;
- the horizon

  ```text
  4 * summableRhs <= epsilon^2 * eta * T
  ```

  yields one iterate with

  ```text
  ||gradient objective (z_t)|| <= epsilon
  R_t <= epsilon^2 / (lam^2 * CR).
  ```

The resulting gradient-norm stationarity complexity is `O(epsilon^-2)`.

## Remaining analytic boundary

The following remain explicit local interfaces rather than globally proved facts
for a real LLM/LoRA system:

1. local smoothness and lower boundedness of the concrete fixed-penalty
   surrogate;
2. a trajectory region on which quadratic growth, hypomonotonicity, strong
   monotonicity, or contraction holds with calibrated constants;
3. differentiability and regularity of the selected restricted response branch;
4. a general nonsmooth or set-valued nonconvex Danskin/envelope theorem;
5. calibration of response-gradient, residual-gradient, and proxy constants for
   a concrete neural model;
6. stochastic mini-batch analogues of the deterministic local inequalities;
7. projected/proximal main-variable gradient-mapping theory;
8. original BLO KKT convergence or general nonconvex BLO global convergence;
9. convergence of the iterates to a unique point.

The checked result is therefore a restricted/local interface theorem.  It proves
that arbitrary learned proposals can be routed through an explicit
certificate-generated fallback without invalidating the fixed-penalty
stationarity budget, while uncertainty-adjusted accepted improvements enter the
budget as a true nonnegative favorable term.
