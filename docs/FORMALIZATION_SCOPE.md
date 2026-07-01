# Formalization scope

This repository formalizes the proof skeleton of the revised OUSVR-BLO online
value-anchor theorem.

## Coverage map

- Sections 1-4: represented as explicit hypotheses and abstract interfaces.
- Section 5: represented by `SafetyBudget` and `SafetyStepSystem`.
- Section 6: represented by `SafetyStepSystem.one_step_lyapunov`,
  `SafetyStepSystem.cumulative_budget_to_time`, and
  `SafetyStepSystem.cumulative_budget`.
- Sections 7-8: represented by `ImprovementBudget` and
  `ImprovementStepSystem`.
- Section 9: represented by `ImprovementStepSystem.Czeta`,
  `ImprovementStepSystem.Czeta_le`, and the enhanced cumulative budget.
- Section 10: represented by `ProxyComparison.true_error_improves` and
  `ProxyR2Plus.r2plus`.
- Sections 11-14: documented as modeling interpretation and claim boundary.

## What Lean checks

Lean checks:

- coefficient accounting in the one-step Lyapunov descent;
- telescoping finite-horizon budget inequalities;
- averaged stationarity, residual, and improvement bounds;
- the corrected `zeta` contribution in the enhanced theorem;
- the proxy calibration algebra that converts proxy improvement into true error
  improvement;
- scalar sufficient-condition lemmas for selected analytic interfaces.

The variables `Gsq`, `R`, `Delta`, `eps`, `b`, `d`, and `zeta` are represented as
real-valued sequences. Nonnegativity assumptions are explicit where they are
needed to drop terms.

## Remaining analytic boundary

The following are still not claimed as globally proved for real LLM/LoRA
training:

1. global differentiability and smoothness of the learned value function;
2. construction and uniqueness of neural lower-response anchors;
3. residual contraction produced by a concrete safeguard implementation;
4. residual drift compatibility for a full training system;
5. original BLO KKT convergence or general nonconvex BLO global convergence.

The current claim is therefore an interface theorem: if the listed analytic
interfaces hold, the OUSVR-BLO value-anchor proof skeleton and its advertised
finite-horizon consequences are machine-checked.
