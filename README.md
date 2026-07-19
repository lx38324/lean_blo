# OUSVR-BLO Lean formalization

This repository formalizes the certificate-sensitive proof skeleton of a
safeguarded online value-anchor theorem for fixed-penalty value-function BLO.
The primary checked claim is finite-horizon stationarity of a restricted/local
value surrogate under explicit analytic interfaces.

## Primary checked chain

1. A safe base response and an accepted online response generate a common
   residual envelope `Q`.
2. Calibrated proxy comparison generates a nonnegative uncertainty-adjusted
   gain `Gamma`.
3. The single small-step condition `CR * beta ≤ theta / 4` implies all final
   Lyapunov coefficient bounds.
4. One-step descent and residual drift telescope to finite-horizon stationarity,
   residual, and certified-gain budgets.

The exact enhanced budget contains

```text
(eta / 4) * sum Gsq
  + (eta * lam^2 * CR / 4) * sum R
  + Cgain * sum Gamma
  <= initial Lyapunov gap + accumulated interface errors,
```

with

```text
eta * lam^2 / 2 <= Cgain <= 3/4 * eta * lam^2.
```

## Claim boundary

Lean checks the scalar coefficient accounting, safeguard closure, calibrated
proxy algebra, finite-horizon telescoping, and averaged consequences. The
repository does not prove that a real LLM/LoRA training system automatically
satisfies the analytic interfaces. It also does not prove general nonconvex BLO
global convergence, original BLO KKT convergence, or convergence of the
iterates to a unique point.

The value-response model is restricted/local: an arbitrary local response is
not identified with the global value function of the original nonconvex lower
problem.

## Build

Install `elan`, then use the committed `lean-toolchain` and
`lake-manifest.json`:

```bash
lake exe cache get
lake build
```

Run `lake update` only when intentionally refreshing and committing the locked
dependency graph.

To reject placeholder proofs, run:

```bash
bash scripts/check_no_placeholder.sh
```

## Main files

- `OUSVRBLO/ParameterBounds.lean`: derives the Lyapunov coefficient bounds from
  the drift parameterization and the small-step condition.
- `OUSVRBLO/SafeguardCertificate.lean`: closes the safe-base/accepted-response
  rule into a common residual envelope.
- `OUSVRBLO/ProxyCertificate.lean`: converts asymmetric proxy calibration into
  an uncertainty-adjusted true-error gain, including fallback as zero gain.
- `OUSVRBLO/CertifiedSafety.lean`: public fallback-safe theorem whose final
  coefficients are derived rather than assumed.
- `OUSVRBLO/CertifiedGainDescent.lean`: exact and simplified certified-gain
  Lyapunov budgets and averaged bounds.
- `OUSVRBLO/SafetyDescent.lean`: reusable low-level scalar algebraic core.
- `OUSVRBLO/ImprovementDescent.lean`: legacy nominal-improvement/error-budget
  formulation retained for comparison.
- `OUSVRBLO/LyapunovBudget.lean`: finite-horizon budget structures and averaged
  consequences.
- `OUSVRBLO/LocalSurrogate.lean`: restricted minimizer and value-gradient
  interface boundary.
- `docs/OUSVR_BLO_CERTIFIED_THEORY.md`: revised theorem statement and proof map.
- `docs/FORMALIZATION_SCOPE.md`: manuscript-to-Lean coverage boundary.
