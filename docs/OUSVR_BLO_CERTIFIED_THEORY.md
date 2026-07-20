# Revised certified theorem

This document states the current public theorem and maps each proof layer to its
Lean implementation. The claim concerns a restricted/local value-function
fixed-penalty surrogate. It retains the machine-learning meaning of an arbitrary
learned response proposal protected by a certifiable fallback.

## 1. Certificate objects

Let `Gsq_t` represent the squared fixed-penalty stationarity measure, `R_t` the
current response residual, and `Q_t` a certificate envelope controlling both the
safe base response and the accepted online response.

A safe base update and residual acceptance tolerance give

\[
Q_t \le (1-\theta)R_t+\varepsilon_t.
\]

The concrete closure is checked in `SafeguardCertificate.lean`.

Let `e_t^B` and `e_t^O` be the true value-gradient approximation errors of the
base and accepted responses. With asymmetric calibration

\[
|\widehat e_t^O-e_t^O|\le\rho_t^O,
\qquad
|\widehat e_t^B-e_t^B|\le\rho_t^B,
\]

and proxy acceptance

\[
\widehat e_t^O
\le
\widehat e_t^B-\widehat\Delta_t+\tau_t^e,
\]

define

\[
\Gamma_t
:=
\widehat\Delta_t-\tau_t^e-\rho_t^O-\rho_t^B.
\]

Only a nonnegative `Gamma_t` is certified; fallback is represented by
`Gamma_t=0`. Lean proves

\[
e_t^O\le e_t^B-\Gamma_t.
\]

If the base response satisfies

\[
e_t^B\le C_RQ_t+b_t,
\]

then

\[
\boxed{e_t^O\le C_RQ_t+b_t-\Gamma_t.}
\]

The main Lean theorems are `CalibratedProxyGain.true_error_improves` and
`CertifiedGainInterface.r2_certified`.

## 2. Exact drift parameterization

For a positive Young parameter `mu`, define

\[
A_\eta=\frac{\eta\mu}{2}+\frac{L_R\eta^2}{2},
\qquad
\beta=2A_\eta\lambda^2+\frac{\eta}{2\mu}.
\]

The manuscript choice is

\[
\mu=\frac{1}{\sqrt2\lambda},
\]

which gives exactly

\[
A_\eta
=
\frac{\eta}{2\sqrt2\lambda}
+
\frac{L_R\eta^2}{2},
\]

and

\[
\beta_\eta
=
\sqrt2\lambda\eta
+
\lambda^2L_R\eta^2.
\]

These identities are checked by
`ManuscriptDriftParameters.parameterization_Aeta` and
`ManuscriptDriftParameters.parameterization_beta`.

Assume

\[
C_R\beta\le\frac\theta4,
\qquad
0<\theta\le1,
\]

and set

\[
\alpha=\frac{\eta\lambda^2C_R}{\theta}.
\]

`ParameterBounds.lean` derives, rather than assumes,

\[
2\alpha A_\eta\le\frac\eta4,
\]

\[
\alpha-(1-\theta)
\left[
\frac{\eta\lambda^2C_R}{2}+\alpha(1+C_R\beta)
\right]
\ge
\frac{\eta\lambda^2C_R}{4},
\]

and all advertised error-coefficient bounds.

## 3. Analytic descent closure

Let `G_t` and `E_t` be vectors in a real Hilbert space. After substituting the
update into local smoothness, assume

\[
P_{t+1}
\le
P_t-\eta\langle G_t,G_t+E_t\rangle
+
\frac{L_P\eta^2}{2}\|G_t+E_t\|^2,
\]

with `L_P * eta <= 1`.

`InexactDescent.lean` checks the polarization identity

\[
\langle G,G+E\rangle
=
\frac12\left(
\|G\|^2+\|G+E\|^2-\|E\|^2
\right)
\]

and derives

\[
P_{t+1}
\le
P_t-rac\eta2\|G_t\|^2+rac\eta2\|E_t\|^2.
\]

With the safety error interface

\[
\|E_t\|^2\le\lambda^2(C_RQ_t+b_t),
\]

Lean obtains

\[
P_{t+1}
\le
P_t-rac\eta2\|G_t\|^2
+
\frac{\eta\lambda^2}{2}(C_RQ_t+b_t).
\]

With the certified error interface

\[
\|E_t\|^2\le\lambda^2(C_RQ_t+b_t-\Gamma_t),
\]

Lean obtains

\[
P_{t+1}
\le
P_t-rac\eta2\|G_t\|^2
+
\frac{\eta\lambda^2}{2}(C_RQ_t+b_t)
-
\frac{\eta\lambda^2}{2}\Gamma_t.
\]

## 4. Analytic residual-drift closure

Assume the raw compatibility inequality

\[
R_{t+1}
\le
Q_t+\eta H_t s_t
+
\frac{L_R\eta^2}{2}s_t^2+d_t,
\]

where

\[
H_t^2=C_RQ_t+b_t,
\qquad
s_t^2\le2\|G_t\|^2+2\|E_t\|^2.
\]

`ResidualDrift.lean` checks Young's inequality and all coefficient propagation.
The safety error interface gives

\[
R_{t+1}
\le
(1+C_R\beta)Q_t
+2A_\eta\|G_t\|^2
+\beta b_t+d_t.
\]

The certified error interface retains the favorable gain term:

\[
R_{t+1}
\le
(1+C_R\beta)Q_t
+2A_\eta\|G_t\|^2
+\beta b_t
-2A_\eta\lambda^2\Gamma_t
+d_t.
\]

The relevant Lean theorems are `SafeResidualDriftScalar.drift` and
`CertifiedResidualDriftScalar.certified_drift`.

## 5. Composed analytic theorem

`AnalyticClosure.lean` stores the Hilbert-space smoothness premise, squared
error bound, raw residual compatibility, step-square bound, envelope
contraction, and S2 in one `AnalyticSafetySystem`. It then checks

```text
analytic assumptions
  => scalar descent and drift interfaces
  => CertifiedSafetySystem
  => finite-horizon safety budget.
```

The principal declarations are

- `AnalyticSafetySystem.descent_interface`;
- `AnalyticSafetySystem.drift_interface`;
- `AnalyticSafetySystem.toCertifiedSafetySystem`;
- `AnalyticSafetySystem.cumulative_budget`.

`AnalyticGainClosure.lean` performs the same composition for the
uncertainty-adjusted gain:

- `AnalyticGainSystem.descent_interface`;
- `AnalyticGainSystem.drift_interface`;
- `AnalyticGainSystem.toCertifiedGainStepSystem`;
- `AnalyticGainSystem.cumulative_budget`;
- `AnalyticGainSystem.cumulative_budget_simple`.

Thus the public Lean chain no longer begins by assuming already-collected
one-step descent and drift inequalities. It begins from the analytic scalar and
Hilbert-space premises used in the mathematical proof.

## 6. Fallback-safe finite-horizon theorem

Define

\[
\Psi_t=P_t+\alpha R_t.
\]

Lean checks

\[
\boxed{
\frac\eta4\sum_{t<T}Gsq_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
}
\]

The public theorem is `CertifiedSafetySystem.cumulative_budget`. Averaged
stationarity and residual statements are provided by
`CertifiedSafetySystem.gradient_average_bound` and
`CertifiedSafetySystem.residual_average_bound`.

## 7. Certified-gain finite-horizon theorem

Define

\[
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2.
\]

Lean checks

\[
\boxed{
\frac\eta4\sum_{t<T}Gsq_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
+C_\Gamma\sum_{t<T}\Gamma_t
\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t,
}
\]

with

\[
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2.
\]

The exact theorem is `CertifiedGainStepSystem.cumulative_budget`; the
conventional lower coefficient is provided by
`CertifiedGainStepSystem.cumulative_budget_simple`.

## 8. Best-iterate finite-time consequences

`FiniteTimeCorollaries.lean` verifies the generic fact that every nonempty finite
horizon contains an iterate no larger than its arithmetic average. Hence the
fallback-safe theorem gives some `t < T` satisfying

\[
\begin{aligned}
Gsq_t\le&
\frac{4(\Psi_0-P_\star)}{\eta T}
+\frac{4C_\varepsilon}{\eta T}\sum_{s<T}\varepsilon_s
\\
&+
\frac{4C_b}{\eta T}\sum_{s<T}b_s
+\frac{4C_d}{\eta T}\sum_{s<T}d_s.
\end{aligned}
\]

There are analogous residual and certified-gain-system results. The public
Lean declarations are

- `CertifiedSafetySystem.exists_stationary_iterate`;
- `CertifiedSafetySystem.exists_small_residual_iterate`;
- `CertifiedGainStepSystem.exists_stationary_iterate`;
- `CertifiedGainStepSystem.exists_small_residual_iterate`.

This is the direct finite-time epsilon-stationarity interpretation: when the
right-hand side is at most a target `epsilon`, one of the first `T` iterates has
`Gsq_t <= epsilon`.

## 9. Bounded-budget asymptotics

`Asymptotics.lean` checks the generic result

\[
\left(\forall T,\ \sum_{t<T}a_t\le M\right),
\quad a_t\ge0
\quad\Longrightarrow\quad
\frac1T\sum_{t<T}a_t\longrightarrow0.
\]

If the accumulated right-hand side of the safety budget is uniformly bounded
by `M`, Lean derives

\[
\sum_{t<T}Gsq_t\le\frac{4M}{\eta},
\qquad
\sum_{t<T}R_t\le\frac{4M}{\eta\lambda^2C_R},
\]

and consequently both averages converge to zero.

For the certified-gain system, Lean additionally proves

\[
\sum_{t<T}\Gamma_t
\le
\frac{2M}{\eta\lambda^2},
\qquad
\frac1T\sum_{t<T}\Gamma_t\longrightarrow0.
\]

The main declarations are the safety/gain `partial_sums_bounded` and
`average_tendsto_zero` theorem families. Summable nonnegative perturbation
sequences imply the required uniform boundedness of their partial sums; the
formal theorem uses the more direct accumulated-budget premise.

## 10. Claim boundary

The theorem concerns a restricted/local value-function fixed-penalty surrogate.
The following remain explicit analytic interfaces for a concrete neural model:

1. local smoothness and lower boundedness of the concrete surrogate;
2. existence and regularity of the restricted response;
3. a general nonconvex Danskin/envelope theorem;
4. concrete residual-to-value-gradient error control;
5. raw residual compatibility for a stochastic training system;
6. projected/stochastic main-variable updates.

The project does not prove global nonconvex lower optimality, original BLO KKT
convergence, or convergence of the iterates to a unique point.
