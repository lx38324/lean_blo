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

Under one-step surrogate descent, residual drift, and
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
Cgain = eta * lam^2 / 2 + 2 * alpha * Aeta * lam^2
eta * lam^2 / 2 <= Cgain <= 3/4 * eta * lam^2.
```

## Coverage map

- Residual safeguard closure:
  `ResidualSafeguardSystem.base_le_envelope`,
  `ResidualSafeguardSystem.online_le_envelope`, and
  `ResidualSafeguardSystem.envelope_contract`.
- Parameter derivation:
  `SafetyParameters.two_alpha_Aeta_le`,
  `SafetyParameters.residual_drop_coeff`,
  `SafetyParameters.eps_coeff_bound`,
  `SafetyParameters.b_coeff_bound`, and the `Cgain` bounds.
- Fallback-safe public theorem:
  `CertifiedSafetySystem.one_step_lyapunov`,
  `CertifiedSafetySystem.cumulative_budget`, and averaged corollaries.
- Proxy certificate:
  `CalibratedProxyGain.true_error_improves` and
  `CertifiedGainInterface.r2_certified`.
- Certified-gain public theorem:
  `CertifiedGainStepSystem.one_step_lyapunov`, exact and simplified cumulative
  budgets, and averaged stationarity/residual bounds.
- Restricted value-response boundary:
  `RestrictedValueResponseInterface` and
  `RestrictedValueGradientInterface`.

## What Lean checks

Lean checks:

- the single small-step condition implies the coefficient inequalities used by
  the Lyapunov proof;
- safe fallback and residual acceptance produce one common contraction
  envelope;
- proxy tolerance and asymmetric calibration radii are correctly subtracted
  from the nominal proxy margin;
- the certified gain appears favorably in both surrogate descent and residual
  drift;
- one-step inequalities telescope to finite-horizon budgets;
- the finite-horizon budgets imply averaged stationarity and residual bounds.

## Remaining analytic boundary

The following remain explicit interfaces rather than globally proved facts for
real LLM/LoRA systems:

1. local smoothness and lower boundedness of the fixed-penalty surrogate;
2. existence and regularity of the restricted lower response;
3. a general nonconvex Danskin/envelope theorem;
4. residual-to-value-gradient error control for a concrete neural model;
5. residual drift compatibility for a full stochastic training system;
6. projected or stochastic main-variable updates;
7. original BLO KKT convergence or general nonconvex BLO global convergence.

The checked claim is therefore an interface theorem. It establishes that, when
these analytic interfaces hold, arbitrary learned proposals can be embedded
through a certifiable fallback without invalidating the finite-horizon
stationarity budget, and calibrated improvements enter that budget as a true
nonnegative gain.
