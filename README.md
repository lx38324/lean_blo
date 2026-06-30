# OUSVR-BLO Lean formalization scaffold

This repository is a Lean 4 / Mathlib project for formalizing the algebraic core of the OUSVR-BLO online value-anchor proof.

## Current formalization scope

The current Lean file formalizes the finite-horizon Lyapunov-budget part of the proof:

- fallback-safe fixed-penalty stationarity budget;
- averaged gradient-stationarity bound;
- averaged residual bound;
- upper-gradient-improvement budget with the corrected `zeta` coefficient;
- averaged stationarity-plus-improvement bound;
- error-free corollaries for both theorem families when the accumulated
  perturbation budgets vanish.

The analytic assumptions are intentionally represented as hypotheses. This is appropriate for the current proof stage: the original argument is an interface theorem, not yet a full formalization of differentiability of the value function, smoothness of the LLM fine-tuning loss, or the construction of lower-response anchors.

## Not yet fully formalized

The following remain as separate theorem layers:

1. differentiability and smoothness of the value function;
2. the residual-to-value-gradient error bound;
3. residual drift compatibility;
4. validity of the LLM/LoRA local regularized lower-response assumptions;
5. the safeguard implementation as executable Lean code.

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

- `OUSVRBLO/LyapunovBudget.lean`: machine-checkable formalization target.
- `docs/FORMALIZATION_SCOPE.md`: summary of what is and is not formalized.
- `.github/workflows/lean.yml`: CI build and placeholder-proof check.
