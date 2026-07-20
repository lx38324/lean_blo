# Formalization scope

This repository formalizes the proof skeleton of a safeguarded online
value-anchor fixed-penalty stationarity theorem.

## Revised public theorem

The public theorem uses a certificate envelope `Q_t` and an
uncertainty-adjusted gain `Gamma_t`:

```text
safe base contraction + accepted-response tolerance
  => common residual envelope Q_t

asymmetric proxy calibration + acceptance margin
  => eO_t <= eB_t - Gamma_t, Gamma_t >= 0

baseline residual-to-error control
  => eO_t <= CR * Q_t + b_t - Gamma_t
```

Under the analytic descent and residual-drift premises, together with
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

## Coverage map

- Exact manuscript parameterization:
  `ManuscriptDriftParameters.parameterization_Aeta`,
  `ManuscriptDriftParameters.parameterization_beta`, and
  `ManuscriptDriftParameters.toSafetyParameters`.
- Restricted response minimizer and envelope layer:
  `RestrictedValueResponseInterface.response_isMinimizer`,
  `RestrictedValueResponseInterface.eq_response_of_quadratic_growth`,
  `hasFDerivAt_branchValue_of_stationary_response`, and
  `RestrictedValueResponseInterface.hasFDerivAt_value_of_stationary_response`.
- Response-distance and objective-gap R2 certificates:
  `gradient_error_sq_le_of_lipschitz_and_error_bound`,
  `RestrictedValueGradientInterface.r2_of_lipschitz_and_error_bound`,
  `RestrictedValueResponseInterface.distance_sq_le_gap_div`, and
  `RestrictedValueGradientInterface.r2_of_quadratic_growth`.
- Computable lower-gradient residual certificate:
  `distance_sq_le_gradient_residual_of_strong_monotonicity`,
  `eq_of_strong_monotonicity_and_stationarity`, and
  `value_gradient_error_sq_le_lower_gradient_residual`.
- Proximal response certificate:
  `proximalLowerGradient_inner_sub`,
  `proximalLowerGradient_strong_monotone`,
  `proximalLowerGradient_stationary_unique`, and
  `value_gradient_error_sq_le_proximal_residual`.
- Contractive fixed-point/projected-response residual certificate:
  `dist_le_fixedPoint_residual_of_contraction`,
  `dist_sq_le_fixedPoint_residual_sq_of_contraction`,
  `eq_of_contraction_fixedPoints`, and
  `value_gradient_error_sq_le_fixedPoint_residual`.
- Concrete non-vacuous restricted response model:
  the `ScalarQuadraticResponse` quadratic-growth, uniqueness, exact R2, and
  certified R2 theorems.
- Residual safeguard closure:
  `ResidualSafeguardSystem.base_le_envelope`,
  `ResidualSafeguardSystem.online_le_envelope`, and
  `ResidualSafeguardSystem.envelope_contract`.
- Parameter derivation:
  `SafetyParameters.two_alpha_Aeta_le`,
  `SafetyParameters.residual_drop_coeff`,
  `SafetyParameters.eps_coeff_bound`,
  `SafetyParameters.b_coeff_bound`, and the `Cgain` bounds.
- Hilbert-space descent:
  `real_inner_self_add_identity`,
  `inexact_gradient_descent_of_smoothness`,
  `inexact_gradient_descent_with_error_bound`, and
  `inexact_gradient_descent_with_certified_gain`.
- Residual drift:
  `young_product_with_parameter`,
  `SafeResidualDriftScalar.drift`, and
  `CertifiedResidualDriftScalar.certified_drift`.
- Analytic safety closure:
  `AnalyticSafetySystem.descent_interface`,
  `AnalyticSafetySystem.drift_interface`,
  `AnalyticSafetySystem.toCertifiedSafetySystem`, and
  `AnalyticSafetySystem.cumulative_budget`.
- Analytic certified-gain closure:
  `AnalyticGainSystem.descent_interface`,
  `AnalyticGainSystem.drift_interface`,
  `AnalyticGainSystem.toCertifiedGainStepSystem`,
  `AnalyticGainSystem.cumulative_budget`, and
  `AnalyticGainSystem.cumulative_budget_simple`.
- Fallback-safe public theorem:
  `CertifiedSafetySystem.one_step_lyapunov`,
  `CertifiedSafetySystem.cumulative_budget`, and averaged corollaries.
- Proxy certificate:
  `CalibratedProxyGain.true_error_improves` and
  `CertifiedGainInterface.r2_certified`.
- Certified-gain public theorem:
  `CertifiedGainStepSystem.one_step_lyapunov`, exact and simplified cumulative
  budgets, and averaged stationarity/residual bounds.
- Finite-time best-iterate layer:
  `CertifiedSafetySystem.exists_stationary_iterate`,
  `CertifiedSafetySystem.exists_small_residual_iterate`,
  `CertifiedGainStepSystem.exists_stationary_iterate`, and
  `CertifiedGainStepSystem.exists_small_residual_iterate`.
- Bounded-budget asymptotic layer:
  `seq_average_tendsto_zero_of_bounded_partial_sums`, the safety and gain-system
  partial-sum bounds, and the stationarity/residual/gain
  `average_tendsto_zero` theorems.
- Summable-error closure:
  `CertifiedSafetySystem.accumulatedRhs_le_summableRhs`,
  `CertifiedGainStepSystem.accumulatedRhs_le_summableRhs`, and the five direct
  `average_tendsto_zero_of_summable` corollaries.
- Explicit summable-error rates:
  the safety and certified-gain `average_bound_of_summable`, joint
  `gradient_gain_average_bound_of_summable`, and best-iterate corollaries in
  `SummableRates.lean`.
- Restricted value-response interface boundary:
  `RestrictedValueResponseInterface` and
  `RestrictedValueGradientInterface`.

## What Lean checks

Lean checks:

- the exact manuscript definitions of `mu`, `Aeta`, and `betaEta` agree with the
  generic Young-inequality parameterization;
- positive quadratic growth makes the represented restricted minimizer unique;
- the chain rule and lower stationarity remove the derivative of a differentiable
  response branch from the local value derivative;
- response-gradient Lipschitzness plus a distance error bound implies the R2
  squared value-gradient error interface;
- quadratic growth gives an objective-gap version of R2;
- strong monotonicity gives response uniqueness and an R2 certificate using the
  computable squared lower-gradient residual;
- a quadratic proximal term dominating a local hypomonotonicity constant produces
  strong monotonicity with modulus `rho - curvature` and the corresponding R2
  constant `L^2 / (rho - curvature)^2`;
- a contractive response map gives fixed-point uniqueness, a response-distance
  error bound, and an R2 certificate using the computable squared fixed-point or
  projected-response residual with constant `L^2 / (1-q)^2`;
- a scalar quadratic model satisfies the restricted minimizer, quadratic-growth,
  and value-gradient error interfaces simultaneously;
- the single small-step condition implies all coefficient inequalities used by
  the Lyapunov proof;
- safe fallback and residual acceptance produce one common contraction
  envelope;
- proxy tolerance and asymmetric calibration radii are correctly subtracted
  from the nominal proxy margin;
- a Hilbert-space smoothness inequality and squared error control imply the
  scalar inexact-descent interface;
- raw residual compatibility, Young's inequality, the step-square estimate, and
  squared error control imply the scalar residual recursion;
- the certified gain appears favorably in both surrogate descent and residual
  drift;
- one-step inequalities telescope to finite-horizon budgets;
- finite-horizon budgets imply averaged and best-iterate stationarity/residual
  bounds;
- uniformly bounded accumulated right-hand sides imply bounded stationarity,
  residual, and gain partial sums and hence average convergence to zero;
- summability of the nonnegative perturbation sequences supplies the required
  uniform accumulated-budget bound, explicit `O(1 / T)` rates, and the
  corresponding asymptotic conclusions directly.

## Remaining analytic boundary

The following remain explicit local interfaces rather than globally proved facts
for real LLM/LoRA systems:

1. local smoothness and lower boundedness of the concrete fixed-penalty
   surrogate;
2. a trajectory region on which quadratic growth, hypomonotonicity, strong
   monotonicity, or contraction holds with calibrated constants;
3. differentiability and regularity of the selected restricted response branch;
4. a general nonsmooth or set-valued nonconvex Danskin/envelope theorem;
5. calibration of the residual-to-value-gradient constants for a concrete
   neural model;
6. the raw residual-compatibility inequality for a full stochastic training
   system;
7. projected or stochastic main-variable updates;
8. original BLO KKT convergence or general nonconvex BLO global convergence.

Thus the checked result remains an interface theorem. It establishes that, when
the listed local analytic premises hold, arbitrary learned proposals can be
embedded through a certifiable fallback without invalidating the finite-horizon
stationarity budget, and calibrated improvements enter that budget as a true
nonnegative gain. The response-certificate layer verifies several concrete
sufficient conditions for those interfaces without claiming global neural lower
optimality.
