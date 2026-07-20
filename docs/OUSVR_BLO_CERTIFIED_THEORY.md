# OUSVR-BLO certified theorem

## 1. Scope

This repository verifies a certificate-facing convergence theorem for a
safeguarded online value-anchor method applied to a restricted/local
fixed-penalty value-function BLO surrogate.

The machine-learning interpretation is:

> A learned updater may propose an arbitrary response. The proposal is used only
> when explicit residual-safety, calibrated proxy-improvement, and nonnegative
> margin certificates pass. Otherwise the method uses a safe base response and
> assigns zero certified gain to that round.

The checked result is not a theorem for global nonconvex lower-level optimality,
original BLO KKT convergence, projected or stochastic main-variable dynamics, or
convergence of the iterates to a unique point.

The accept/fallback rule decides propositions over real numbers in a
`noncomputable` section. It is a proof-level selector, not an extracted
floating-point implementation.

## 2. Restricted local value response

For every upper variable `x`, the represented lower response satisfies

```text
xiStar(x) in feasible(x),
h(x, xiStar(x)) <= h(x, xi)  for every feasible xi,
v(x) = h(x, xiStar(x)).
```

The theorem uses the represented value-gradient identity

```text
grad v(x) = grad_x h(x, xiStar(x)).
```

This identity can be supplied as an interface, or obtained from the checked
local differentiable-branch envelope theorem under differentiability of the
response branch and stationarity in every response-space direction.

This is a restricted/local value model. It does not identify an arbitrary local
response with a global minimizer of the original nonconvex lower problem.

Principal Lean files:

```text
OUSVRBLO/LocalSurrogate.lean
OUSVRBLO/RestrictedEnvelope.lean
OUSVRBLO/ResponseErrorBound.lean
```

## 3. Base response, proposal, and explicit selection

At round `t`, let

```text
Rbase_t, Rprop_t             response residuals,
eBase_t, eProp_t             true squared value-gradient errors,
eHatBase_t, eHatProp_t       calibrated computable proxies.
```

The vector-valued layer may define the true errors directly:

```text
eBase_t = ||gValue_t - gBase_t||^2,
eProp_t = ||gValue_t - gProp_t||^2.
```

Define the uncertainty-adjusted proposal margin

```text
margin_t = DeltaHat_t - tauE_t - rhoProp_t - rhoBase_t.
```

The proposal is accepted exactly when

```text
Rprop_t <= Rbase_t + tauR_t,
eHatProp_t <= eHatBase_t - DeltaHat_t + tauE_t,
0 <= margin_t.
```

The selected quantities are

```text
Ronline_t = if accepted then Rprop_t else Rbase_t,
eOnline_t = if accepted then eProp_t else eBase_t,
Gamma_t   = if accepted then margin_t else 0.
```

Lean proves

```text
0 <= Ronline_t,
0 <= eOnline_t,
0 <= Gamma_t.
```

Principal Lean files:

```text
OUSVRBLO/RestrictedValueProposalData.lean
OUSVRBLO/ValueGradientErrorEmbedding.lean
OUSVRBLO/AcceptedResponseSelector.lean
OUSVRBLO/CertifiedProposalAcceptance.lean
```

## 4. Residual envelope and calibrated true gain

Assume the safe base response contracts:

```text
Rbase_t <= (1 - theta) * R_t + epsBase_t,
0 < theta <= 1.
```

Define

```text
Q_t   = Rbase_t + tauR_t,
eps_t = epsBase_t + tauR_t.
```

The selector yields

```text
Rbase_t <= Q_t,
Ronline_t <= Q_t,
Q_t <= (1 - theta) * R_t + eps_t.
```

Asymmetric proxy calibration proves, in both the accepted and fallback branches,

```text
eOnline_t <= eBase_t - Gamma_t.
```

If the natural baseline certificate is

```text
eBase_t <= CR * Rbase_t + b_t,
CR > 0,
```

then

```text
eOnline_t <= CR * Q_t + b_t - Gamma_t.
```

The selected true squared error is nonnegative, so Lean also proves

```text
Gamma_t <= eBase_t,
0 <= CR * Q_t + b_t - Gamma_t.
```

No separate effective-gain clipping operation is needed.

Two primitive affine scales need not have identical constants. If two bounds use
`C1 * Q + b1` and `C2 * Q + b2`, Lean verifies that both are dominated by

```text
max(C1, C2) * Q + max(b1, b2),
```

and that the pointwise maximum of two nonnegative summable bias sequences is
summable.

Principal Lean files:

```text
OUSVRBLO/SafeguardCertificate.lean
OUSVRBLO/ProxyCertificate.lean
OUSVRBLO/ProxySequenceCertificate.lean
OUSVRBLO/CertifiedGainFeasibility.lean
OUSVRBLO/CommonResidualScale.lean
```

## 5. Exact inexact-gradient semantics

Let `embed` be an isometric embedding of the represented value-gradient block
into the ambient update space. Define

```text
Err_t = lambda * embed(gValue_t - gOnline_t).
```

Lean proves the exact identity

```text
||Err_t||^2 = lambda^2 * eOnline_t,
```

and hence

```text
||Err_t||^2 <= lambda^2 * (CR * Q_t + b_t - Gamma_t).
```

For the represented fixed-penalty objective

```text
P(z) = outer(z) + lambda * (lower(z) - value(z)),
```

component gradient certificates yield

```text
G_t = gradOuter_t + lambda * (gradLower_t - embed(gValue_t)).
```

The value-gradient coupling theorem then proves

```text
G_t + Err_t
  = gradOuter_t + lambda * (gradLower_t - embed(gOnline_t)).
```

Thus the actual approximate direction is the fixed-penalty gradient with the
exact value gradient replaced by the response gradient selected by the
certificates.

Principal Lean files:

```text
OUSVRBLO/ValueGradientTrajectory.lean
OUSVRBLO/FixedPenaltyGradientSemantics.lean
OUSVRBLO/ValueGradientFixedPenaltyCoupling.lean
OUSVRBLO/TrajectoryGradientSemantics.lean
```

## 6. Trajectory and analytic premises

The deterministic trajectory satisfies

```text
z_(t+1) - z_t = -eta * (G_t + Err_t),
eta > 0.
```

The local objective smoothness premise is stored before substituting the update:

```text
P_(t+1) <= P_t
  + <G_t, z_(t+1) - z_t>
  + LP / 2 * ||z_(t+1) - z_t||^2,
LP * eta <= 1.
```

Residual smoothness starts from the response actually selected:

```text
R_(t+1) <= Ronline_t
  + <gradR_t, dx_t>
  + LR / 2 * ||dx_t||^2
  + d_t.
```

The residual-gradient and upper-block displacement interfaces are

```text
||gradR_t||^2 <= CR * Q_t + b_t,
||dx_t|| <= eta * ||G_t + Err_t||.
```

Lean derives the substituted objective inequality, the displacement bound, and
the final gain-aware residual recursion; they are not independent fields of the
highest-level trajectory theorem.

## 7. Manuscript parameters and explicit step size

Use

```text
mu      = 1 / (sqrt(2) * lambda),
Aeta    = eta / (2 * sqrt(2) * lambda) + LR * eta^2 / 2,
betaEta = sqrt(2) * lambda * eta + lambda^2 * LR * eta^2.
```

The small-step condition is

```text
CR * betaEta <= theta / 4.
```

A checked transparent sufficient split is

```text
CR * sqrt(2) * lambda * eta <= theta / 8,
CR * lambda^2 * LR * eta^2 <= theta / 8.
```

When `LR > 0`, the following single readable condition implies the split and
therefore the small-step condition:

```text
eta <= min(
  theta / (8 * CR * sqrt(2) * lambda),
  sqrt(theta / (8 * CR * lambda^2 * LR))
).
```

Together with objective smoothness, a conventional sufficient choice is

```text
eta <= min(
  1 / LP,
  theta / (8 * CR * sqrt(2) * lambda),
  sqrt(theta / (8 * CR * lambda^2 * LR))
).
```

Terms with zero denominating smoothness constants are omitted.

Principal Lean files:

```text
OUSVRBLO/ManuscriptParameters.lean
OUSVRBLO/ExplicitStepSize.lean
OUSVRBLO/ParameterBounds.lean
```

## 8. One-step and finite-horizon theorem

Define

```text
alpha = eta * lambda^2 * CR / theta,
Psi_t = P_t + alpha * R_t.
```

The exact favorable gain coefficient is

```text
Cgain = eta * lambda^2 / 2 + 2 * alpha * Aeta * lambda^2.
```

Lean derives

```text
eta * lambda^2 / 2 <= Cgain <= 3/4 * eta * lambda^2.
```

The one-step Lyapunov inequality is

```text
Psi_(t+1) <= Psi_t
  - eta/4 * ||G_t||^2
  - eta * lambda^2 * CR / 4 * R_t
  - Cgain * Gamma_t
  + Ceps * eps_t
  + Cb * b_t
  + Cd * d_t,
```

where

```text
Ceps = eta * lambda^2 * CR * (3/4 + 1/theta),
Cb   = 3/4 * eta * lambda^2,
Cd   = eta * lambda^2 * CR / theta.
```

For every finite horizon `T`, Lean checks

```text
eta/4 * sum_(t<T) ||G_t||^2
  + Cgain * sum_(t<T) Gamma_t
  + eta * lambda^2 * CR / 4 * sum_(t<T) R_t
  <= Psi_0 - Pstar
     + Ceps * sum_(t<T) eps_t
     + Cb * sum_(t<T) b_t
     + Cd * sum_(t<T) d_t.
```

A simplified form replaces `Cgain` by its checked lower bound
`eta * lambda^2 / 2`.

Principal Lean files:

```text
OUSVRBLO/InexactDescent.lean
OUSVRBLO/ResidualSmoothnessCertificate.lean
OUSVRBLO/ResidualDrift.lean
OUSVRBLO/CertifiedGainDescent.lean
OUSVRBLO/TrajectoryCertifiedProposalGain.lean
```

## 9. Finite-time stationarity

Define the joint performance measure

```text
J_t = ||G_t||^2 + lambda^2 * CR * R_t.
```

For every `T > 0`, the finite-horizon theorem gives one and the same iterate
satisfying

```text
exists t < T,
  J_t <= 4 * accumulatedRhs(T) / (eta * T).
```

When `G_t` is certified as the actual objective gradient, this becomes

```text
exists t < T,
  ||gradient P(z_t)||^2 + lambda^2 * CR * R_t
    <= 4 * accumulatedRhs(T) / (eta * T).
```

## 10. Three perturbation regimes

### 10.1 Summable perturbations

If the nonnegative sequences `epsBase_t`, `tauR_t`, `b_t`, and `d_t` are
summable, Lean proves

```text
sum_t ||G_t||^2 < infinity,
sum_t R_t < infinity,
sum_t Gamma_t < infinity.
```

Consequently

```text
||G_t|| -> 0,
R_t -> 0,
Gamma_t -> 0.
```

It also proves the same-iterate rate

```text
exists t < T,
  J_t <= 4 * summableRhs / (eta * T).
```

If `G_t = gradient P(z_t)` and

```text
4 * summableRhs <= epsilon^2 * eta * T,
```

then some `t < T` satisfies

```text
||gradient P(z_t)|| <= epsilon,
R_t <= epsilon^2 / (lambda^2 * CR).
```

Thus the gradient-norm stationarity complexity is `O(epsilon^-2)`.

### 10.2 Cesaro-vanishing perturbations

Summability is not required for an average convergence statement. If

```text
average_(t<T) eps_t -> 0,
average_(t<T) b_t   -> 0,
average_(t<T) d_t   -> 0,
```

then Lean proves

```text
average_(t<T) (||G_t||^2 + lambda^2 * CR * R_t) -> 0,
average_(t<T) ||G_t||^2 -> 0,
average_(t<T) R_t -> 0.
```

The trajectory wrapper derives the total envelope condition from
Cesaro-vanishing averages of `epsBase_t` and `tauR_t`. With an objective-gradient
certificate it also gives

```text
average_(t<T) ||gradient P(z_t)||^2 -> 0.
```

These conclusions are average statements only; they do not imply pointwise
convergence without stronger assumptions.

Principal Lean file:

```text
OUSVRBLO/CesaroPerturbationCorollaries.lean
```

### 10.3 Persistent bounded perturbations

Define the one-round weighted perturbation

```text
delta_t = Ceps * eps_t + Cb * b_t + Cd * d_t.
```

If

```text
delta_t <= floor  for every t,
```

then Lean proves the neighborhood bound

```text
average_(t<T) J_t
  <= 4 * (Psi_0 - Pstar) / (eta * T)
     + 4 * floor / eta,
```

and one same-horizon iterate satisfies the same upper bound.

With an actual objective-gradient certificate:

```text
exists t < T,
  ||gradient P(z_t)||^2 + lambda^2 * CR * R_t
    <= 4 * (Psi_0 - Pstar) / (eta * T)
       + 4 * floor / eta.
```

This is the correct theorem for persistent stochastic noise or fixed acceptance
tolerances; such errors are not promoted to zero-error pointwise convergence.

Principal Lean file:

```text
OUSVRBLO/PersistentErrorFloor.lean
```

## 11. Checked sufficient conditions for the baseline error interface

The repository verifies several local sufficient conditions for

```text
eBase_t <= CR * Rbase_t + b_t.
```

They include:

1. response-gradient Lipschitzness plus a response-distance error bound;
2. positive quadratic growth;
3. strong monotonicity of a computable lower-gradient residual;
4. proximal regularization dominating local hypomonotonicity;
5. a contractive fixed-point or projected-response map.

A scalar quadratic model verifies that the restricted response and error-bound
interfaces are jointly satisfiable.

Principal Lean files:

```text
OUSVRBLO/StrongMonotonicityCertificate.lean
OUSVRBLO/ProximalResponseCertificate.lean
OUSVRBLO/ContractionResidualCertificate.lean
OUSVRBLO/QuadraticResponseExample.lean
```

## 12. Highest-level API hierarchy

The checked construction proceeds through

```text
EndToEndCertifiedGainSystem
  <- SelectedEndToEndCertifiedGainSystem
  <- CanonicalSelectedEndToEndCertifiedGainSystem
  <- TrajectoryCertifiedProposalGainSystem
  <- ValueGradientTrajectorySystem
  +  ValueGradientFixedPenaltyCertificate.
```

The upper layers derive rather than assume:

```text
accept/fallback selection,
selected residual and selected true error,
zero-gain fallback,
residual envelope contraction,
calibrated true gain,
feasibility of the gain-aware error scale,
exact ambient error norm,
canonical Young scale and step norm,
post-substitution smoothness,
upper-block displacement,
final residual recursion,
all Lyapunov coefficient inequalities.
```

## 13. Precise claim boundary

The remaining model-specific interfaces are:

1. local smoothness and lower boundedness of the concrete fixed-penalty
   surrogate;
2. a local region on which quadratic growth, hypomonotonicity, strong
   monotonicity, or contraction holds with calibrated constants;
3. differentiability and regularity of the selected restricted response branch;
4. calibration of response-gradient, residual-gradient, and proxy constants;
5. stochastic mini-batch analogues of the deterministic local inequalities;
6. projected or proximal main-variable gradient-mapping theory;
7. a general nonsmooth or set-valued nonconvex Danskin theorem;
8. original BLO KKT or general nonconvex BLO global convergence.

The precise checked claim is:

> Under explicit local response, residual, calibration, trajectory, and
> small-step certificates, arbitrary learned response proposals can be routed
> through a certificate-generated fallback without invalidating fixed-penalty
> stationarity. Accepted uncertainty-adjusted value-gradient improvement enters
> the Lyapunov budget as a true nonnegative favorable term.
