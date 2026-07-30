# Finite-time and perturbation-regime certificates

## 1. Finite-horizon Lyapunov budget

For the certified-gain system, define

```text
B_T = Psi_0 - Pstar
      + Ceps * sum_(t<T) eps_t
      + Cb * sum_(t<T) b_t
      + Cd * sum_(t<T) d_t.
```

The simplified checked budget is

```text
eta/4 * sum_(t<T) Gsq_t
  + eta * lambda^2 / 2 * sum_(t<T) Gamma_t
  + eta * lambda^2 * CR / 4 * sum_(t<T) R_t
  <= B_T.
```

The exact gain coefficient is

```text
Cgain = eta * lambda^2 / 2 + 2 * alpha * Aeta * lambda^2,
eta * lambda^2 / 2 <= Cgain <= 3/4 * eta * lambda^2.
```

`Gamma_t` is a favorable term. It is retained in the Lyapunov accounting but is
not treated as an optimization error that should be minimized.

## 2. Same-iterate certificate

Define

```text
J_t = Gsq_t + lambda^2 * CR * R_t.
```

The finite-horizon theorem gives

```text
average_(t<T) J_t <= 4 * B_T / (eta * T).
```

Therefore one and the same round satisfies

```text
exists t < T,
  Gsq_t + lambda^2 * CR * R_t
    <= 4 * B_T / (eta * T).
```

This is stronger than separate existence statements for stationarity and
residual control, because both properties hold at the same accepted-response
round.

When a trajectory gradient certificate is supplied,

```text
Gsq_t = ||gradient P(z_t)||^2.
```

Hence the certificate can be stated directly with the actual fixed-penalty
objective gradient.

Principal Lean declarations:

```text
CertifiedGainStepSystem.jointMeasure
CertifiedGainStepSystem.joint_average_bound
CertifiedGainStepSystem.exists_joint_certificate
TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_joint_certificate
```

## 3. Explicit gradient-norm complexity under summable errors

Assume the nonnegative perturbation sequences are summable:

```text
sum_t eps_t < infinity,
sum_t b_t   < infinity,
sum_t d_t   < infinity.
```

Define

```text
B_infinity = Psi_0 - Pstar
  + Ceps * sum_t eps_t
  + Cb * sum_t b_t
  + Cd * sum_t d_t.
```

Lean proves

```text
exists t < T,
  Gsq_t + lambda^2 * CR * R_t
    <= 4 * B_infinity / (eta * T).
```

For a gradient-norm target `epsilon >= 0`, the horizon condition

```text
4 * B_infinity <= epsilon^2 * eta * T
```

implies

```text
exists t < T,
  ||gradient P(z_t)|| <= epsilon,
  R_t <= epsilon^2 / (lambda^2 * CR).
```

Thus the checked dependence for gradient-norm stationarity is
`O(epsilon^-2)`.

Principal Lean declarations:

```text
CertifiedGainStepSystem.exists_joint_certificate_of_summable
TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_joint_certificate_of_summable
TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_norm_and_scaled_residual_le_of_summable
```

## 4. Pointwise conclusions under summable errors

The finite budget bounds partial sums of the nonnegative sequences. Lean derives

```text
sum_t Gsq_t < infinity,
sum_t R_t < infinity,
sum_t Gamma_t < infinity.
```

Consequently

```text
Gsq_t -> 0,
R_t -> 0,
Gamma_t -> 0.
```

At the Hilbert-space trajectory level,

```text
||G_t|| -> 0.
```

With the objective-gradient certificate,

```text
||gradient P(z_t)|| -> 0.
```

The conclusion `Gamma_t -> 0` is a finite-budget consequence for a nonnegative
favorable term; it does not make small gain a performance goal.

These pointwise conclusions still do not imply convergence of `z_t` to a unique
point.

## 5. Cesaro-vanishing perturbations

Summability is stronger than necessary for average convergence. Define

```text
CesaroAverage(a, T) = (1/T) * sum_(t<T) a_t.
```

Suppose

```text
CesaroAverage(eps, T) -> 0,
CesaroAverage(b, T)   -> 0,
CesaroAverage(d, T)   -> 0.
```

Lean rewrites the finite-horizon theorem as

```text
CesaroAverage(J, T)
  <= 4 * (Psi_0 - Pstar) / (eta * T)
     + 4 * Ceps / eta * CesaroAverage(eps, T)
     + 4 * Cb / eta * CesaroAverage(b, T)
     + 4 * Cd / eta * CesaroAverage(d, T).
```

Therefore

```text
CesaroAverage(J, T)   -> 0,
CesaroAverage(Gsq, T) -> 0,
CesaroAverage(R, T)   -> 0.
```

For the explicit safeguard,

```text
eps_t = epsBase_t + tauR_t.
```

Thus Cesaro-vanishing averages of `epsBase_t` and `tauR_t` imply a
Cesaro-vanishing total envelope error. At the trajectory level Lean obtains

```text
average_(t<T) ||G_t||^2 -> 0,
average_(t<T) R_t       -> 0.
```

With an objective-gradient certificate,

```text
average_(t<T) ||gradient P(z_t)||^2 -> 0.
```

These are average convergence results only. Cesaro-vanishing perturbations do
not by themselves imply pointwise convergence or summability.

Principal Lean file:

```text
OUSVRBLO/CesaroPerturbationCorollaries.lean
```

## 6. Persistent bounded perturbations

Define the one-round weighted perturbation

```text
delta_t = Ceps * eps_t + Cb * b_t + Cd * d_t.
```

Suppose

```text
delta_t <= floor  for every t.
```

Then

```text
B_T <= Psi_0 - Pstar + T * floor.
```

Lean proves the average neighborhood bound

```text
average_(t<T) J_t
  <= 4 * (Psi_0 - Pstar) / (eta * T)
     + 4 * floor / eta.
```

It also gives a same-iterate certificate:

```text
exists t < T,
  Gsq_t + lambda^2 * CR * R_t
    <= 4 * (Psi_0 - Pstar) / (eta * T)
       + 4 * floor / eta.
```

With an objective-gradient certificate,

```text
exists t < T,
  ||gradient P(z_t)||^2 + lambda^2 * CR * R_t
    <= 4 * (Psi_0 - Pstar) / (eta * T)
       + 4 * floor / eta.
```

This is the appropriate result for persistent mini-batch noise, a nonvanishing
proxy calibration radius, or fixed safeguard tolerances. Such errors produce a
neighborhood, not an incorrect zero-error convergence claim.

Principal Lean file:

```text
OUSVRBLO/PersistentErrorFloor.lean
```

## 7. Relationship among the regimes

```text
summable perturbations
  => explicit O(1/T) same-iterate rate
  => summability of Gsq, R, Gamma
  => pointwise convergence to zero;

Cesaro-vanishing perturbations
  => average joint performance tends to zero
  => average stationarity and residual tend to zero;

persistent uniformly bounded perturbations
  => finite stationarity/residual neighborhood.
```

These conclusions are logically distinct and are kept as separate theorem
families in Lean.

## 8. Claim boundary

None of these consequences proves:

```text
convergence of the iterates to a unique point,
global lower-level optimality,
original BLO KKT convergence,
projected or stochastic main-variable correctness.
```

They are finite-horizon, average, pointwise-measure, or neighborhood conclusions
for the represented restricted/local fixed-penalty surrogate under the stated
certificate and analytic interfaces.
