# Migration from the legacy proof notation

This note records how the earlier manuscript notation is replaced by the current
certificate-facing theorem stack. The earlier draft used a single accepted
residual `Rhat_t`, a nominal improvement `Delta_t`, and a separate proxy-error
budget `zeta_t`. Those objects are deprecated in the current theorem statement.

## 1. Residual migration

Legacy notation used

$$
\widehat R_t=R(x_t,\xi_{t+1}^{O})
$$

both for accepted-response drift and, indirectly, for the baseline response
error bound. That substitution is not valid from the one-sided safeguard
condition alone.

The current proof distinguishes

$$
R_t^B=R(x_t,\xi_{t+1}^{B}),
\qquad
R_t^O=R(x_t,\xi_{t+1}^{O}),
$$

and defines the common certificate envelope

$$
Q_t:=R_t^B+\tau_t^R.
$$

The explicit selector proves

$$
R_t^B\le Q_t,
\qquad
R_t^O\le Q_t,
$$

and the safe base contraction gives

$$
Q_t\le(1-\theta)R_t+\varepsilon_t^B+\tau_t^R.
$$

Thus the current total contraction error is

$$
\varepsilon_t:=\varepsilon_t^B+\tau_t^R.
$$

## 2. Improvement migration

The legacy enhanced theorem used

$$
e_t^O\le C_R\widehat R_t+b_t-\Delta_t+\zeta_t.
$$

The current proof subtracts calibration uncertainty before a gain is admitted.
For asymmetric calibration radii and proxy tolerance, define

$$
M_t
:=
\widehat\Delta_t-\tau_t^e-\rho_t^P-\rho_t^B.
$$

The proposal is credited with gain only when it passes all acceptance tests and
$M_t\ge0$. The selected gain is

$$
\Gamma_t
=
\begin{cases}
M_t,&\text{accepted},\\
0,&\text{fallback}.
\end{cases}
$$

The selector and calibration proof yield

$$
e_t^O\le e_t^B-\Gamma_t.
$$

Combining this with the natural baseline certificate

$$
e_t^B\le C_RR_t^B+b_t
$$

gives

$$
\boxed{
e_t^O\le C_RQ_t+b_t-\Gamma_t.
}
$$

No separate positive `zeta_t` budget or effective-gain clipping is required.

## 3. Drift migration

Because the current certified error bound retains the favorable term,

$$
\|E_t\|^2
\le
\lambda^2(C_RQ_t+b_t-\Gamma_t),
$$

the residual recursion also retains gain:

$$
R_{t+1}
\le
(1+C_R\beta_\eta)Q_t
+2A_\eta\|G_t\|^2
+\beta_\eta b_t
-2A_\eta\lambda^2\Gamma_t
+d_t.
$$

Consequently, the exact one-step Lyapunov coefficient of `Gamma_t` is

$$
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2,
$$

with

$$
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2.
$$

## 4. Current finite-horizon statement

The current enhanced theorem is

$$
\boxed{
\begin{aligned}
&\frac{\eta}{4}\sum_{t<T}\|G_t\|^2
+C_\Gamma\sum_{t<T}\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\\
&\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
\end{aligned}
}
$$

Equivalently, for

$$
J_t:=\|G_t\|^2+\lambda^2C_RR_t,
$$

$$
\frac{\eta}{4}\sum_{t<T}J_t
\le
\mathcal B_T-C_\Gamma\sum_{t<T}\Gamma_t.
$$

The right-hand side is strictly smaller than the safety-only numerator whenever
positive certified gain accumulates.

## 5. Stochastic extension

The current stochastic theorem does not reuse a generic deterministic `zeta_t`.
A centered stochastic update perturbation contributes the explicit variance
coefficient

$$
C_\sigma
=
\frac{L_P\eta^2}{2}+\alpha A_\eta.
$$

For the manuscript parameterization, the expected rate has the form

$$
O\!\left(\frac1{\eta T}+\eta\sigma^2\right).
$$

This is an expectation-level interface theorem; a concrete neural mini-batch
filtration is not claimed to be formalized.

## 6. Current citation surface

Use the stable declarations in

```text
OUSVRBLO.ICMLTheoryPackage
```

rather than citing the legacy `Rhat/Delta/zeta` proof directly. The compact
statement is in `docs/ICML_METHOD_THEORY_PACKAGE.md`; the exact assumption audit
is in `docs/ICML_THEORY_DEPENDENCY_AUDIT.md`.
