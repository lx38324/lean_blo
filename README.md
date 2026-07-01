# OUSVR-BLO Lean formalization

This repository is a Lean 4 / Mathlib project for formalizing the proof
skeleton of the revised OUSVR-BLO online value-anchor theorem.

## Verification phases

The project is organized into three Lean verification phases:

1. Core theorem verification: one-step safety Lyapunov descent, finite-horizon
   budget summation, averaged stationarity bound, and averaged residual bound.
2. Whole-proof verification: upper-gradient improvement, corrected `Czeta`, and
   the proxy certificate that yields the enhanced `R2+` interface.
3. Detailed verification: sufficient-condition lemmas for selected analytic
   interfaces, including scalar smooth descent, residual-to-gradient conversion,
   and local regularized surrogate/value-response abstractions.

The first two phases validate the main manuscript proof structure under explicit
interface hypotheses. The third phase starts to replace selected hypotheses with
machine-checked sufficient conditions.

## Claim boundary

Lean checks the algebraic proof skeleton, coefficient flow, finite-horizon sums,
and averaged bounds. The repository does not prove general nonconvex BLO global
convergence, original BLO KKT convergence, or that a real LLM/LoRA training
system automatically satisfies all analytic hypotheses.

## Build

Install `elan`, then run:

```bash
lake update
lake exe cache get
lake build
```

To reject placeholder proofs, run:

```bash
bash scripts/check_no_placeholder.sh
```

## Files

- `OUSVRBLO/LyapunovBudget.lean`: finite-horizon budget structures and averaged
  consequences.
- `OUSVRBLO/SafetyDescent.lean`: one-step safety descent to cumulative budget.
- `OUSVRBLO/ImprovementDescent.lean`: enhanced improvement descent with `Czeta`.
- `OUSVRBLO/ProxyCertificate.lean`: proxy calibration certificate.
- `OUSVRBLO/AnalyticInterfaces.lean`: scalar analytic sufficient-condition
  lemmas.
- `OUSVRBLO/LocalSurrogate.lean`: local surrogate and value-response interfaces.
- `docs/FORMALIZATION_SCOPE.md`: manuscript-to-Lean coverage boundary.
- `docs/LEAN_VERIFICATION_PHASES.md`: Chinese phase explanation and acceptance
  criteria.
