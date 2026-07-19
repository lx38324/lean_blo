# Revised certified theorem

## Objects

Let `Gsq_t` represent the squared fixed-penalty stationarity measure, `R_t` the
current response residual, and `Q_t` a certificate envelope controlling both
the safe base response and the accepted online response.

A safe base update and residual acceptance tolerance give

\[
Q_t \le (1-\theta)R_t+\varepsilon_t.
\]

Let `e_t^B` and `e_t^O` be the true value-gradient approximation errors of the
base and accepted responses. With asymmetric proxy calibration,

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
`Gamma_t=0`. Then

\[
e_t^O\le e_t^B-\Gamma_t.
\]

If the base response satisfies

\[
e_t^B\le C_RQ_t+b_t,
\]

then

\[
e_t^O\le C_RQ_t+b_t-\Gamma_t.
\]

## Parameter condition

For drift constants `Aeta` and `beta`, assume

\[
A_\eta\ge0,
\qquad
\beta\ge0,
\qquad
2A_\eta\lambda^2\le\beta,
\]

and the single small-step condition

\[
C_R\beta\le\frac\theta4.
\]

Set

\[
\alpha=\frac{\eta\lambda^2C_R}{\theta}.
\]

Lean derives, rather than assumes,

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

and the advertised error coefficients.

## Fallback-safe theorem

Under the one-step descent and drift interfaces,

\[
\frac\eta4\sum_{t<T}Gsq_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
\]

The public Lean theorem is `CertifiedSafetySystem.cumulative_budget`.

## Certified-gain theorem

Keeping the favorable gain term in both interfaces gives

\[
P_{t+1}
\le
P_t-
\frac\eta2Gsq_t
+
\frac{\eta\lambda^2}{2}(C_RQ_t+b_t)
-
\frac{\eta\lambda^2}{2}\Gamma_t,
\]

and

\[
R_{t+1}
\le
(1+C_R\beta)Q_t
+2A_\eta Gsq_t
+\beta b_t
-2A_\eta\lambda^2\Gamma_t
+d_t.
\]

Therefore, with

\[
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2,
\]

Lean checks

\[
\frac\eta4\sum_{t<T}Gsq_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
+C_\Gamma\sum_{t<T}\Gamma_t
\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t,
\]

with

\[
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2.
\]

The exact public Lean theorem is
`CertifiedGainStepSystem.cumulative_budget`; the conventional simplified
coefficient is provided by
`CertifiedGainStepSystem.cumulative_budget_simple`.

## Claim boundary

The theorem concerns a restricted/local value-function fixed-penalty
surrogate. It does not prove global nonconvex lower optimality, original BLO KKT
convergence, or convergence of the iterates to a unique point.
