# Finite-time, joint, and pointwise certificates

This note records the consequence layer of the OUSVR-BLO certified Lyapunov
budget.  It distinguishes three logically different statements:

1. averaged finite-horizon bounds;
2. one-iterate certificates on the same round;
3. pointwise convergence under summable perturbations.

The distinction matters because the uncertainty-adjusted gain `Gamma_t` is a
favorable budget term, not an error quantity that should be minimized.

## 1. Accumulated right-hand sides

For the fallback-safe system define

$$
\mathcal B_T
=
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
$$

The checked safety budget is

$$
\frac{\eta}{4}\sum_{t<T}G_t^2
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\le
\mathcal B_T.
$$

For the certified-gain system the simplified checked budget is

$$
\frac{\eta}{4}\sum_{t<T}G_t^2
+
\frac{\eta\lambda^2}{2}\sum_{t<T}\Gamma_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\le
\mathcal B_T.
$$

The exact gain coefficient is larger:

$$
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2,
\qquad
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2.
$$

## 2. Same-iterate safety certificate

Define the nonnegative joint performance measure

$$
\mathcal J_t
:=
G_t^2+\lambda^2C_RR_t.
$$

The finite-horizon budget gives

$$
\frac1T\sum_{t<T}\mathcal J_t
\le
\frac{4\mathcal B_T}{\eta T}.
$$

Since a finite average is at least its minimum, Lean verifies the existence of a
single round `t<T` satisfying

$$
\boxed{
G_t^2+\lambda^2C_RR_t
\le
\frac{4\mathcal B_T}{\eta T}.
}
$$

This is stronger than separately stating that one round has small stationarity
and possibly another round has small residual.  The same accepted response round
satisfies both controls.

Lean declarations:

```text
CertifiedSafetySystem.jointMeasure
CertifiedSafetySystem.joint_average_bound
CertifiedSafetySystem.exists_joint_certificate
```

## 3. Same-iterate certified-gain performance certificate

For the enhanced system, the performance measure remains

$$
\mathcal J_t
=
G_t^2+\lambda^2C_RR_t.
$$

The nonnegative favorable term `Gamma_t` may be dropped from the Lyapunov budget,
so Lean verifies

$$
\boxed{
\exists t<T:\quad
G_t^2+\lambda^2C_RR_t
\le
\frac{4\mathcal B_T}{\eta T}.
}
$$

Lean declarations:

```text
CertifiedGainStepSystem.jointMeasure
CertifiedGainStepSystem.joint_average_bound
CertifiedGainStepSystem.exists_joint_certificate
```

The full expression

$$
G_t^2+2\lambda^2\Gamma_t+\lambda^2C_RR_t
$$

is retained separately as `budgetDensity`.  Its average is bounded by
`4 * B_T / (eta * T)`, but it is not presented as a performance metric: a large
nonnegative `Gamma_t` is an accepted certified improvement, not an optimization
error.

Lean declaration:

```text
CertifiedGainStepSystem.budgetDensity_average_bound
```

## 4. Explicit rates under summable perturbations

Assume

$$
\sum_{t=0}^\infty\varepsilon_t<\infty,
\qquad
\sum_{t=0}^\infty b_t<\infty,
\qquad
\sum_{t=0}^\infty d_t<\infty.
$$

Define the finite constant

$$
\mathcal B_\infty
:=
\Psi_0-P_\star
+C_\varepsilon\sum_{t=0}^\infty\varepsilon_t
+C_b\sum_{t=0}^\infty b_t
+C_d\sum_{t=0}^\infty d_t.
$$

Lean verifies the explicit rates

$$
\frac1T\sum_{t<T}G_t^2
\le
\frac{4\mathcal B_\infty}{\eta T},
$$

$$
\frac1T\sum_{t<T}R_t
\le
\frac{4\mathcal B_\infty}{\eta\lambda^2C_RT},
$$

and, for the enhanced system,

$$
\frac1T\sum_{t<T}G_t^2
+
\frac{2\lambda^2}{T}\sum_{t<T}\Gamma_t
\le
\frac{4\mathcal B_\infty}{\eta T}.
$$

The same-iterate form is

$$
\boxed{
\exists t<T:\quad
G_t^2+\lambda^2C_RR_t
\le
\frac{4\mathcal B_\infty}{\eta T}.
}
$$

Lean files:

```text
SummableRates.lean
JointCertificates.lean
```

## 5. Pointwise convergence

The finite accumulated budget bounds the nonnegative partial sums.  Under the
summable perturbation premise, Lean derives

$$
\sum_{t=0}^\infty G_t^2<\infty,
\qquad
\sum_{t=0}^\infty R_t<\infty.
$$

Consequently

$$
G_t^2\to0,
\qquad
R_t\to0.
$$

For the certified-gain system Lean additionally proves

$$
\sum_{t=0}^\infty\Gamma_t<\infty,
\qquad
\Gamma_t\to0.
$$

The last statement is a finite-budget consequence.  It does not say that small
certified gain is an algorithmic objective; it says that a uniformly positive
per-round gain cannot persist forever while the Lyapunov function is lower
bounded and perturbations are summable.

Lean declarations include:

```text
CertifiedSafetySystem.gradient_summable_of_summable
CertifiedSafetySystem.residual_summable_of_summable
CertifiedSafetySystem.gradient_tendsto_zero_of_summable
CertifiedSafetySystem.residual_tendsto_zero_of_summable

CertifiedGainStepSystem.gradient_summable_of_summable
CertifiedGainStepSystem.residual_summable_of_summable
CertifiedGainStepSystem.gain_summable_of_summable
CertifiedGainStepSystem.gradient_tendsto_zero_of_summable
CertifiedGainStepSystem.residual_tendsto_zero_of_summable
CertifiedGainStepSystem.gain_tendsto_zero_of_summable
```

## 6. Gradient-norm interpretation

In the analytic Hilbert-space closure,

$$
G_t^2=\|G_t\|^2.
$$

The generic fact

$$
\|G_t\|^2\to0
\quad\Longrightarrow\quad
\|G_t\|\to0
$$

is verified using continuity of the real square root.  Therefore summable
perturbations imply the pointwise stationarity statement

$$
\boxed{\|G_t\|\to0.}
$$

Lean declarations:

```text
tendsto_norm_zero_of_tendsto_norm_sq_zero
AnalyticSafetySystem.gradient_norm_tendsto_zero_of_summable
AnalyticGainSystem.gradient_norm_tendsto_zero_of_summable
```

This still does not assert that the iterates `z_t` converge to a unique point.
It asserts that the fixed-penalty stationarity measure and response residual
vanish along the sequence.
