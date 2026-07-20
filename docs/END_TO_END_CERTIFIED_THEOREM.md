# End-to-end certified online value-anchor theorem

## 1. The theorem-facing objects

The checked theorem concerns a restricted/local fixed-penalty value-function
surrogate. A learned updater proposes a response, a certifiable base update
provides fallback safety, and an explicit selector decides which response enters
the main update.

At round `t`, the proposal data contain

```text
R_t                 current response residual,
Rbase_t             safe-base response residual,
Rprop_t             proposal response residual,
eBase_t             base true squared value-gradient error,
eProp_t             proposal true squared value-gradient error,
eHatBase_t          base proxy error,
eHatProp_t          proposal proxy error.
```

The proposal is accepted exactly when

```text
Rprop_t <= Rbase_t + tauR_t,
eHatProp_t <= eHatBase_t - DeltaHat_t + tauE_t,
0 <= DeltaHat_t - tauE_t - rhoProp_t - rhoBase_t.
```

The proof-level selected quantities are

```text
Ronline_t = if accepted then Rprop_t else Rbase_t,
eOnline_t = if accepted then eProp_t else eBase_t,
Gamma_t   = if accepted
            then DeltaHat_t - tauE_t - rhoProp_t - rhoBase_t
            else 0.
```

Every rejected proposal is therefore converted into a safe zero-gain fallback
round by theorem construction.

## 2. Residual safeguard closure

Assume

```text
Rbase_t <= (1 - theta) * R_t + epsBase_t,
0 < theta <= 1,
tauR_t >= 0.
```

Define

```text
Q_t   = Rbase_t + tauR_t,
eps_t = epsBase_t + tauR_t.
```

Lean proves

```text
Rbase_t <= Q_t,
Ronline_t <= Q_t,
Q_t <= (1 - theta) * R_t + eps_t.
```

Thus the common residual envelope is generated from the actual base and
acceptance rule; it is not an independent contraction hypothesis at the highest
API level.

## 3. Calibrated gain closure

Assume asymmetric calibration

```text
|eHatProp_t - eProp_t| <= rhoProp_t,
|eHatBase_t - eBase_t| <= rhoBase_t.
```

The selector proves in both branches

```text
0 <= Gamma_t,
eOnline_t <= eBase_t - Gamma_t.
```

If

```text
eBase_t <= CR * Rbase_t + b_t,
CR > 0,
```

then

```text
eOnline_t <= CR * Q_t + b_t - Gamma_t.
```

Since `eOnline_t` is a true squared norm, Lean also proves

```text
Gamma_t <= eBase_t,
0 <= CR * Q_t + b_t - Gamma_t.
```

## 4. Exact value-gradient error vector

Let

```text
gValue_t    represented restricted value gradient,
gBase_t     response gradient at the base response,
gProp_t     response gradient at the proposal,
gOnline_t   selector output in gradient space.
```

Define

```text
eBase_t   = ||gValue_t - gBase_t||^2,
eProp_t   = ||gValue_t - gProp_t||^2,
Err_t     = lambda * embed(gValue_t - gOnline_t),
```

where `embed` is an isometric linear embedding into the ambient update space.
Lean proves

```text
||Err_t||^2 = lambda^2 * eOnline_t
            <= lambda^2 * (CR * Q_t + b_t - Gamma_t).
```

## 5. Fixed-penalty objective semantics

For

```text
P(z) = outer(z) + lambda * (lower(z) - value(z)),
```

component gradient certificates give

```text
G_t = gradOuter_t + lambda * (gradLower_t - embed(gValue_t)).
```

The coupling theorem then proves

```text
G_t + Err_t
  = gradOuter_t + lambda * (gradLower_t - embed(gOnline_t)).
```

Thus the approximate update is exactly the fixed-penalty update that substitutes
the selected response gradient for the represented exact value gradient.

## 6. Trajectory and residual drift

The deterministic trajectory satisfies

```text
z_(t+1) - z_t = -eta * (G_t + Err_t),
eta > 0.
```

The objective smoothness premise is stated before update substitution:

```text
P_(t+1) <= P_t
  + <G_t, z_(t+1) - z_t>
  + LP / 2 * ||z_(t+1) - z_t||^2,
LP * eta <= 1.
```

Residual smoothness starts from `Ronline_t`:

```text
R_(t+1) <= Ronline_t
  + <gradR_t, dx_t>
  + LR / 2 * ||dx_t||^2
  + d_t,
```

with

```text
||gradR_t||^2 <= CR * Q_t + b_t,
||dx_t|| <= eta * ||G_t + Err_t||.
```

Lean derives the post-substitution inexact descent and the gain-aware residual
recursion.

## 7. Parameters

Use

```text
mu      = 1 / (sqrt(2) * lambda),
Aeta    = eta / (2 * sqrt(2) * lambda) + LR * eta^2 / 2,
betaEta = sqrt(2) * lambda * eta + lambda^2 * LR * eta^2.
```

Assume

```text
CR * betaEta <= theta / 4.
```

A checked sufficient condition for `LR > 0` is

```text
eta <= min(
  theta / (8 * CR * sqrt(2) * lambda),
  sqrt(theta / (8 * CR * lambda^2 * LR))
).
```

The Lyapunov weight is

```text
alpha = eta * lambda^2 * CR / theta.
```

All final coefficient inequalities are derived from these definitions and the
small-step condition.

## 8. Exact finite-horizon result

Define

```text
Psi_t = P_t + alpha * R_t,
Cgain = eta * lambda^2 / 2 + 2 * alpha * Aeta * lambda^2.
```

Lean verifies

```text
eta * lambda^2 / 2 <= Cgain <= 3/4 * eta * lambda^2.
```

For every `T`,

```text
eta/4 * sum_(t<T) ||G_t||^2
  + Cgain * sum_(t<T) Gamma_t
  + eta * lambda^2 * CR / 4 * sum_(t<T) R_t
  <= Psi_0 - Pstar
     + Ceps * sum_(t<T) eps_t
     + Cb * sum_(t<T) b_t
     + Cd * sum_(t<T) d_t,
```

where

```text
Ceps = eta * lambda^2 * CR * (3/4 + 1/theta),
Cb   = 3/4 * eta * lambda^2,
Cd   = eta * lambda^2 * CR / theta.
```

The simplified theorem replaces `Cgain` by `eta * lambda^2 / 2`.

## 9. Same-iterate certificate

For every `T > 0`, Lean proves

```text
exists t < T,
  ||G_t||^2 + lambda^2 * CR * R_t
    <= 4 * accumulatedRhs(T) / (eta * T).
```

With an objective-gradient certificate, `G_t` can be replaced by
`gradient P(z_t)` in this statement.

## 10. Perturbation regimes

### Summable errors

If `epsBase_t`, `tauR_t`, `b_t`, and `d_t` are summable, then

```text
||G_t|| -> 0,
R_t -> 0,
Gamma_t -> 0,
```

and the same-iterate joint measure has an explicit `O(1/T)` bound. The resulting
gradient-norm complexity is `O(epsilon^-2)`.

### Cesaro-vanishing errors

If only the finite-horizon averages satisfy

```text
average epsBase_t -> 0,
average tauR_t     -> 0,
average b_t        -> 0,
average d_t        -> 0,
```

then Lean proves

```text
average ||G_t||^2 -> 0,
average R_t       -> 0.
```

With an objective-gradient certificate,

```text
average ||gradient P(z_t)||^2 -> 0.
```

These are average statements; they do not imply pointwise convergence.

### Persistent bounded errors

If

```text
Ceps * eps_t + Cb * b_t + Cd * d_t <= floor,
```

then Lean proves the neighborhood certificate

```text
exists t < T,
  ||gradient P(z_t)||^2 + lambda^2 * CR * R_t
    <= 4 * (Psi_0 - Pstar) / (eta * T)
       + 4 * floor / eta,
```

when the objective-gradient certificate is supplied.

## 11. API map

```text
EndToEndCertifiedGainSystem
  <- SelectedEndToEndCertifiedGainSystem
  <- CanonicalSelectedEndToEndCertifiedGainSystem
  <- TrajectoryCertifiedProposalGainSystem
  <- ValueGradientTrajectorySystem
  +  ValueGradientFixedPenaltyCertificate.
```

Principal result declarations include

```text
EndToEndCertifiedGainSystem.cumulative_budget
SelectedEndToEndCertifiedGainSystem.cumulative_budget
CanonicalSelectedEndToEndCertifiedGainSystem.cumulative_budget
TrajectoryCertifiedProposalGainSystem.cumulative_budget
ValueGradientTrajectorySystem.cumulative_budget
TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_joint_certificate
TrajectoryCertifiedProposalGainSystem.objective_gradient_average_tendsto_zero_of_cesaro
TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_joint_certificate_of_error_floor
```

## 12. Claim boundary

The theorem remains conditional on local model-specific interfaces:

```text
local smoothness and lower boundedness,
restricted response regularity,
residual-gradient control,
proxy calibration,
local quadratic growth / strong monotonicity / contraction where used.
```

It does not establish global lower-level optimality, original BLO KKT
convergence, projected or stochastic main-variable correctness, or convergence
of the iterates to a unique point.
