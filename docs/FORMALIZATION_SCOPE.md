# Formalization scope

This repository formalizes a certificate-facing proof stack for a safeguarded
online value-anchor fixed-penalty stationarity theorem.

## Revised public theorem

The theorem uses a common residual envelope `Q_t` and an uncertainty-adjusted
true gain `Gamma_t`.  The highest-level deterministic API no longer assumes
that the proposal has already been accepted.

For raw proposal/base statistics, define the acceptance condition

```text
Rprop_t <= Rbase_t + tauR_t
and ehatProp_t <= ehatB_t - DeltaHat_t + tauE_t
and 0 <= DeltaHat_t - tauE_t - rhoProp_t - rhoB_t.
```

Lean decides this proposition and defines

```text
Ronline_t = if accepted then Rprop_t else Rbase_t
Gamma_t   = if accepted
            then DeltaHat_t - tauE_t - rhoProp_t - rhoB_t
            else 0.
```

Safe base contraction and residual tolerance generate

```text
Q_t   = Rbase_t + tauR_t
eps_t = epsBase_t + tauR_t,
```

with

```text
Ronline_t <= Q_t
Q_t <= (1 - theta) * R_t + eps_t.
```

Asymmetric proxy calibration and the natural baseline interface

```text
eB_t <= CR * Rbase_t + b_t
```

imply

```text
eOnline_t <= CR * Q_t + b_t - Gamma_t,
Gamma_t >= 0.
```

Under the deterministic update, local objective smoothness, selected-response
residual smoothness, residual-gradient control, and
`CR * beta <= theta / 4`, Lean checks

```text
(eta / 4) * SeqSum T Gsq
  + (eta * lam^2 * CR / 4) * SeqSum T R
  + Cgain * SeqSum T Gamma
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

## Highest-level deterministic API

`TrajectoryCertifiedProposalGainSystem` stores:

- raw proposal/base residual and proxy statistics;
- proxy calibration radii and acceptance tolerances;
- safe base contraction;
- the actual update identity
  `z (t + 1) - z t = -eta • (G t + Err t)`;
- objective smoothness before update substitution;
- a contractive continuous linear upper-block map;
- residual smoothness from the actually selected response;
- squared residual-gradient control;
- the single small-step condition.

It derives rather than assumes:

- the Boolean accept/fallback decision;
- the selected residual and selected true error;
- zero gain on fallback and calibrated gain on acceptance;
- the residual envelope and total contraction error;
- the certified squared inexact-gradient bound;
- `H_t = sqrt (CR * Q_t + b_t)` and its square identity;
- `stepNorm_t = norm (G_t + Err_t)` and the squared-sum estimate;
- the displacement bound for the upper block;
- the post-substitution smoothness inequality;
- the final residual recursion;
- all Lyapunov coefficient inequalities;
- the finite-horizon and asymptotic conclusions.

## Coverage map

### Restricted response and value-gradient layer

- `RestrictedValueResponseInterface.response_isMinimizer`;
- `RestrictedValueResponseInterface.eq_response_of_quadratic_growth`;
- `hasFDerivAt_branchValue_of_stationary_response`;
- `RestrictedValueResponseInterface.hasFDerivAt_value_of_stationary_response`;
- `gradient_error_sq_le_of_lipschitz_and_error_bound`;
- `RestrictedValueGradientInterface.r2_of_lipschitz_and_error_bound`;
- `RestrictedValueResponseInterface.distance_sq_le_gap_div`;
- `RestrictedValueGradientInterface.r2_of_quadratic_growth`;
- strong-monotonicity, proximal, contraction-residual, and scalar quadratic
  example theorems.

### Explicit proposal selection

- `CertifiedProposalData.AcceptanceCondition`;
- `CertifiedProposalData.accept`;
- `CertifiedProposalData.toAcceptedResponseSelector`;
- `CertifiedProposalData.Ronline_eq_proposal_of_accept`;
- `CertifiedProposalData.Ronline_eq_base_of_reject`;
- `CertifiedProposalData.Gamma_eq_margin_of_accept`;
- `CertifiedProposalData.Gamma_eq_zero_of_reject`;
- `AcceptedResponseSelector.true_error_improves`;
- `AcceptedResponseSelector.r2_certified`;
- `AcceptedResponseSelector.certified_error_bound`.

### Residual and proxy certificate closure

- `ResidualSafeguardSystem.base_le_envelope`;
- `ResidualSafeguardSystem.online_le_envelope`;
- `ResidualSafeguardSystem.envelope_contract`;
- `CalibratedProxyGain.true_error_improves`;
- `ProxyGainSequence.true_error_improves`;
- `ProxyResidualCertificate.r2_certified`;
- `ProxyResidualCertificate.certified_error_bound`.

### Descent, residual drift, and coefficient accounting

- exact manuscript parameterization and `SafetyParameters` coefficient bounds;
- `real_inner_self_add_identity`;
- `inexact_gradient_descent_of_smoothness`;
- `inexact_gradient_descent_with_certified_gain`;
- residual-smoothness-to-raw-drift theorems;
- `young_product_with_parameter`;
- `CertifiedResidualDriftScalar.certified_drift`;
- `CertifiedGainStepSystem.one_step_lyapunov` and cumulative budgets.

### Selector-facing and canonical closure

- `SelectedEndToEndCertifiedGainSystem.baseline_error_bound_envelope`;
- `SelectedEndToEndCertifiedGainSystem.residual_smooth_step_envelope`;
- `SelectedEndToEndCertifiedGainSystem.cumulative_budget`;
- `norm_add_sq_le_two`;
- `CanonicalSelectedEndToEndCertifiedGainSystem.residual_scale_nonneg`;
- `CanonicalSelectedEndToEndCertifiedGainSystem.toSelectedSystem`;
- canonical exact and simplified cumulative budgets.

### Trajectory closure

- `TrajectoryCertifiedProposalGainSystem.smooth_step`;
- `TrajectoryCertifiedProposalGainSystem.displacement_bound`;
- `TrajectoryCertifiedProposalGainSystem.toCanonicalSystem`;
- `TrajectoryCertifiedProposalGainSystem.toCertifiedGainStepSystem`;
- trajectory exact and simplified cumulative budgets.

### Finite-time and asymptotic layer

- averaged and best-iterate stationarity/residual bounds;
- `jointMeasure`, `joint_average_bound`, and same-iterate certificates;
- bounded-partial-sum and summable-error closures;
- explicit `O(1/T)` bounds;
- pointwise stationarity, response-residual, and gain convergence;
- trajectory-facing same-iterate and pointwise corollaries.

## What Lean checks

Lean checks that:

- the manuscript definitions of `mu`, `Aeta`, and `betaEta` agree with the
  generic Young-parameter formulas;
- S2 implies every coefficient inequality used in the Lyapunov proof;
- positive quadratic growth makes the represented restricted minimizer unique;
- the chain rule and lower stationarity give the local branch-envelope identity;
- several local sufficient conditions imply the residual-to-value-gradient
  error interface;
- the acceptance decision is exactly the conjunction of residual safety, proxy
  improvement, and nonnegative uncertainty-adjusted margin;
- every rejected proposal becomes the base response with zero certified gain;
- every accepted proposal satisfies both residual and calibrated true-error
  certificates;
- baseline residual control can be lifted from `Rbase_t` to the envelope `Q_t`;
- selected-response residual smoothness can be lifted from `Ronline_t` to `Q_t`;
- the actual deterministic update and pre-substitution smoothness imply the
  inexact-descent premise;
- upper-block contractivity implies the displacement bound;
- residual smoothness and squared residual-gradient control imply raw drift;
- the certified gain enters both surrogate descent and residual drift favorably;
- the complete chain telescopes to the advertised finite-horizon budget;
- finite-horizon budgets imply averaged, best-iterate, and same-iterate bounds;
- summable certificate perturbations imply explicit rates and pointwise
  `norm G_t -> 0`, `R_t -> 0`, and `Gamma_t -> 0`.

## Remaining analytic boundary

The following remain explicit local interfaces rather than globally proved facts
for real LLM/LoRA systems:

1. local smoothness and lower boundedness of the concrete fixed-penalty
   surrogate;
2. a trajectory region on which quadratic growth, hypomonotonicity, strong
   monotonicity, or contraction holds with calibrated constants;
3. differentiability and regularity of the selected restricted response branch;
4. a general nonsmooth or set-valued nonconvex Danskin/envelope theorem;
5. calibration of response-gradient, residual-gradient, and proxy constants for
   a concrete neural model;
6. stochastic mini-batch analogues of the deterministic local inequalities;
7. projected or stochastic main-variable updates;
8. original BLO KKT convergence or general nonconvex BLO global convergence.

Thus the checked result remains a restricted/local interface theorem. It proves
that arbitrary learned proposals can be routed through an explicit
certificate-generated fallback without invalidating the finite-horizon
stationarity budget, and that calibrated accepted improvements enter the budget
as a true nonnegative favorable term.
