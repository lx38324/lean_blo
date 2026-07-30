# Trajectory-level certificate closure

This note records the theorem-facing layer above the explicit proposal selector
and canonical certified-gain theorem.  It also records the stronger vector and
fixed-penalty semantic layers that identify the inexact update with the response
gradient selected by the certificates.

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

The value-gradient trajectory and fixed-penalty coupling layers remove two
additional semantic abstractions:

3. the error vector is defined from actual represented value-gradient vectors;
4. the represented value gradient used by that error is the same value component
   appearing in the fixed-penalty objective gradient.

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

## 4. Error vector from selected value-gradient responses

Let

$$
g_t^v
$$

be the represented value gradient, and let

$$
g_t^B,
\qquad
g_t^P
$$

be the response partial gradients associated with the base response and learned
proposal.  The explicit selector chooses

$$
g_t^O
=
\begin{cases}
g_t^P,&\text{if accepted},\\
g_t^B,&\text{if rejected}.
\end{cases}
$$

The vector proposal layer defines

$$
e_t^B=\|g_t^v-g_t^B\|^2,
$$

$$
e_t^P=\|g_t^v-g_t^P\|^2,
$$

and proves

$$
e_t^O=\|g_t^v-g_t^O\|^2.
$$

For an isometric ambient embedding `embed`, define

$$
E_t
=
\lambda\,\operatorname{embed}(g_t^v-g_t^O).
$$

Lean verifies the exact identity

$$
\boxed{
\|E_t\|^2=\lambda^2e_t^O.
}
$$

Therefore the trajectory theorem's error-vector premise can be generated from
actual selected value-gradient vectors rather than supplied as an unrelated
inequality.

Lean declarations:

```text
ValueGradientProposalData.selector_eOnline
ValueGradientProposalData.ambientError_sq
ValueGradientTrajectorySystem.Err_sq
ValueGradientTrajectorySystem.toTrajectorySystem
```

## 5. Fixed-penalty gradient coupling

For a represented objective

$$
P(z)
=
F(z)+\lambda\bigl(h(z)-v(z)\bigr),
$$

component gradient certificates give

$$
G_t
=
 g_t^F
+
\lambda
\left(
 g_t^h-\operatorname{embed}(g_t^v)
\right).
$$

The coupling certificate requires the `g_t^v` above to be exactly the value
gradient stored in the proposal layer.  Since

$$
E_t
=
\lambda\operatorname{embed}(g_t^v-g_t^O),
$$

Lean proves

$$
\boxed{
G_t+E_t
=
 g_t^F
+
\lambda
\left(
 g_t^h-\operatorname{embed}(g_t^O)
\right).
}
$$

Consequently the actual displacement is

$$
\boxed{
z_{t+1}-z_t
=
-
\eta
\left[
 g_t^F
+
\lambda
\left(
 g_t^h-\operatorname{embed}(g_t^O)
\right)
\right].
}
$$

This closes the semantic gap between the exact fixed-penalty objective gradient
and the selected online response gradient.

Lean declarations:

```text
ValueGradientFixedPenaltyCertificate.objective_gradient_eq
ValueGradientFixedPenaltyCertificate.approximate_gradient_eq
ValueGradientFixedPenaltyCertificate.update_uses_selected_gradient
```

## 6. Complete trajectory-facing theorem

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

`ValueGradientTrajectorySystem` constructs this trajectory API with the error
vector defined from the selected value-gradient approximation.  A separate
`ValueGradientFixedPenaltyCertificate` then identifies `G` and `G + Err` with
the exact and selected-response fixed-penalty gradients.

## 7. Finite-time, pointwise, and persistent-error consequences

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

If the weighted one-round perturbation is only uniformly bounded by `floor`,
`OUSVRBLO/PersistentErrorFloor.lean` gives

```text
exists t < T,
  ‖G t‖^2 + lam^2 * CR * R t
    <= 4 * (Psi 0 - Pstar) / (eta * T) + 4 * floor / eta.
```

Thus persistent stochastic or fixed-tolerance errors lead to a certified
stationarity/residual neighborhood rather than an unjustified pointwise zero
limit.

## 8. Claim boundary

This layer still treats the local smoothness inequality itself as an analytic
premise. It does not establish local smoothness for a concrete neural model and
it does not add projected or stochastic main-variable dynamics.  The coupling
certificate also remains an explicit component-gradient premise for a concrete
objective.  The role of this layer is to machine-connect the deterministic
algorithmic update and selected value-gradient response to the verified
certificate/Lyapunov theorem.
