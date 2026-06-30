# Formalization scope

This repository currently formalizes the algebraic Lyapunov-budget layer of the OUSVR-BLO online value-anchor proof.

The informal mathematical proof has two layers.

First, a fallback-safe fixed-penalty stationarity theorem states that if the accepted online anchor satisfies residual contraction, residual-to-value-gradient compatibility, and residual drift compatibility, then the fixed-penalty surrogate stationarity budget is controlled.

Second, an upper-gradient-improvement theorem states that if the accepted online anchor improves the value-gradient approximation over a lower-only anchor, then the improvement appears explicitly as a negative term in the Lyapunov descent budget. The revised version accounts for the `zeta` error inside the residual drift calculation by using an abstract `Czeta` coefficient.

## What Lean checks now

The Lean file starts from the already-summed finite-horizon Lyapunov inequalities and proves the averaged consequences:

```text
cumulative safety budget
  => averaged stationarity bound
  => averaged residual bound

cumulative improvement budget
  => averaged stationarity-plus-improvement bound
  => averaged residual bound

zero accumulated error budgets
  => clean averaged fallback-safe stationarity/residual bounds
  => clean averaged upper-gradient-improvement/residual bounds
```

The variables `Gsq`, `R`, `Delta`, `eps`, `b`, `d`, and `zeta` are represented as real-valued sequences. Nonnegativity assumptions are explicit where they are needed to drop terms.

## What remains analytic

The following are intentionally left as hypotheses for later formalization:

1. smoothness of the fixed-penalty surrogate;
2. construction of the value function or local regularized value function;
3. residual contraction produced by the safeguard;
4. residual-to-value-gradient error control;
5. residual drift compatibility;
6. the LLM/LoRA local regularized lower-response model.

This is consistent with the intended claim: learned online value-anchor updates can be safely embedded into a value-function BLO update through an explicit residual interface.
