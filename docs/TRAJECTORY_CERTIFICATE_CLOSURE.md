# Trajectory-level certificate closure

This note records the theorem-facing layer above the explicit proposal selector
and canonical certified-gain theorem.  It has been checked by Lean as part of
the root library.

## 1. Motivation

The canonical system already derives:

- the accepted response from an explicit residual/proxy certificate decision;
- the common residual envelope and uncertainty-adjusted gain;
- `H_t = sqrt (C_R Q_t + b_t)`;
- `stepNorm_t = ‖G_t + E_t‖`;
- the final finite-horizon Lyapunov budget.

The trajectory layer removes two further pre-collected premises:

1. the smoothness inequality after the algorithmic update has already been
   substituted;
2. the upper-block displacement estimate.

## 2. Actual trajectory update

Assume an ambient real Hilbert space `E`, an upper-variable Hilbert space `X`,
and a contractive continuous linear map `projectX : E →L[ℝ] X`.  Store the
actual deterministic update identity

```text
z (t + 1) - z t = -eta • (G t + Err t).
```

Start from the pre-substitution local smoothness inequality

```text
objective (z (t + 1)) <= objective (z t)
  + <G t, z (t + 1) - z t>
  + LP / 2 * ‖z (t + 1) - z t‖^2.
```

The formalized scalar and inner-product identities give

```text
objective (z (t + 1)) <= objective (z t)
  - eta * <G t, G t + Err t>
  + LP * eta^2 / 2 * ‖G t + Err t‖^2.
```

This is exactly the smoothness premise consumed by the checked inexact-descent
theorem.

Lean declaration:

```text
TrajectoryCertifiedProposalGainSystem.smooth_step
```

## 3. Upper-variable displacement

Define the displacement used in residual smoothness by

```text
dx t = projectX (z (t + 1) - z t).
```

If

```text
‖projectX u‖ <= ‖u‖,
```

then the update identity and norm homogeneity give

```text
‖dx t‖ <= eta * ‖G t + Err t‖.
```

Thus the displacement estimate is a consequence of the actual trajectory and
block extraction, rather than a separately supplied scalar inequality.

Lean declaration:

```text
TrajectoryCertifiedProposalGainSystem.displacement_bound
```

## 4. Complete trajectory-facing theorem

The structure

```text
TrajectoryCertifiedProposalGainSystem
```

contains:

- raw proposal/base residual and proxy statistics;
- calibration radii and acceptance tolerances;
- safe base contraction;
- the actual deterministic update identity;
- local objective smoothness before update substitution;
- selected-response residual smoothness;
- the residual-gradient bound;
- a contractive upper-block map;
- the small-step condition `CR * beta <= theta / 4`.

It constructs

```text
TrajectoryCertifiedProposalGainSystem.toCanonicalSystem
TrajectoryCertifiedProposalGainSystem.toCertifiedGainStepSystem
```

and proves both finite-horizon forms:

```text
TrajectoryCertifiedProposalGainSystem.cumulative_budget
TrajectoryCertifiedProposalGainSystem.cumulative_budget_simple
```

The exact form is

```text
(eta / 4) * sum Gsq
  + Cgain * sum Gamma
  + (eta * lam^2 * CR / 4) * sum R
  <= initial Lyapunov gap + accumulated certificate errors.
```

## 5. Finite-time and pointwise consequences

`OUSVRBLO/TrajectoryCertifiedProposalCorollaries.lean` transfers the checked
same-iterate and asymptotic conclusions to the trajectory-facing API.

For every `T > 0`, one iterate satisfies

```text
exists t < T,
  ‖G t‖^2 + lam^2 * CR * R t
    <= 4 * accumulatedRhs T / (eta * T).
```

If the base contraction errors, residual acceptance tolerances, value-gradient
bias errors, and residual-drift errors are summable, Lean proves the explicit
`O(1/T)` same-iterate version and

```text
‖G t‖ -> 0,
R t -> 0,
Gamma t -> 0.
```

The gain limit is a consequence of the finite nonnegative gain budget; gain is
not treated as an error objective.

## 6. Claim boundary

This layer still treats the local smoothness inequality itself as an analytic
premise. It does not establish local smoothness for a concrete neural model and
it does not add projected or stochastic main-variable dynamics. Its role is to
machine-connect the deterministic algorithmic update to the previously verified
certificate/Lyapunov theorem.
