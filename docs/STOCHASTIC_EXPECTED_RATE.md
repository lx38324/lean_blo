# Stochastic expected certified-gain rate

This note records the expectation-level stochastic extension used in the
ICML-oriented method-theory package.

## 1. Scope

The deterministic selected update is perturbed by a centered stochastic term
`W_t`.  At the scalar moment level, the formalized sufficient condition is

$$
\mathbb E_t\langle G_t+E_t,W_t\rangle=0,
\qquad
\mathbb E_t\|W_t\|^2\le \sigma_t^2.
$$

Consequently,

$$
\mathbb E_t\|G_t+E_t+W_t\|^2
\le
\|G_t+E_t\|^2+\sigma_t^2.
$$

`CenteredNoiseMoment.fullStepSq_le` checks this moment algebra.

The file does not formalize a specific neural mini-batch sampler, filtration,
or measurability proof.  Instead, it machine-checks the expected Lyapunov
consequences once the centered one-step moment interfaces are supplied.

## 2. Expected one-step budget

The stochastic objective descent adds

$$
\frac{L_P\eta^2}{2}\sigma_t^2,
$$

and the residual drift adds

$$
A_\eta\sigma_t^2.
$$

With

$$
\alpha=\frac{\eta\lambda^2C_R}{\theta},
$$

define

$$
C_\sigma
:=
\frac{L_P\eta^2}{2}+\alpha A_\eta.
$$

Lean verifies

$$
\begin{aligned}
\mathbb E\Psi_{t+1}
\le{}&
\mathbb E\Psi_t
-\frac{\eta}{4}\mathbb E\|G_t\|^2
-\frac{\eta\lambda^2C_R}{4}\mathbb E R_t
-C_\Gamma\mathbb E\Gamma_t
\\
&+C_\varepsilon\mathbb E\varepsilon_t
+C_b\mathbb E b_t
+C_d\mathbb E d_t
+C_\sigma\sigma_t^2.
\end{aligned}
$$

The exact finite-horizon consequence is

$$
\boxed{
\begin{aligned}
&\frac{\eta}{4}\sum_{t<T}\mathbb E\|G_t\|^2
+C_\Gamma\sum_{t<T}\mathbb E\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}\mathbb E R_t
\\
&\le
\mathbb E\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\mathbb E\varepsilon_t
+C_b\sum_{t<T}\mathbb E b_t
+C_d\sum_{t<T}\mathbb E d_t
+C_\sigma\sum_{t<T}\sigma_t^2.
\end{aligned}
}
$$

The corresponding gain-adjusted average retains

$$
C_\Gamma\sum_{t<T}\mathbb E\Gamma_t
$$

in the numerator instead of discarding it.

Lean file: `OUSVRBLO/StochasticExpectedGain.lean`.

## 3. Explicit variance scaling

Lean also proves

$$
\frac{4C_\sigma}{\eta}
=
2L_P\eta+
\frac{4\lambda^2C_RA_\eta}{\theta}.
$$

For the manuscript coefficient

$$
A_\eta
=
\frac{\eta}{2\sqrt2\lambda}
+
\frac{L_R\eta^2}{2},
$$

this becomes

$$
\boxed{
\frac{4C_\sigma}{\eta}
=
\eta\left(
2L_P
+
\frac{\sqrt2\lambda C_R}{\theta}
+
\frac{2\lambda^2C_RL_R}{\theta}\eta
\right).
}
$$

Therefore, with zero certificate bias and a uniform variance bound

$$
\sigma_t^2\le\bar\sigma^2,
$$

Lean verifies

$$
\boxed{
\begin{aligned}
\frac1T\sum_{t<T}
\left(
\mathbb E\|G_t\|^2+
\lambda^2C_R\mathbb E R_t
\right)
\le{}&
\frac{4(\mathbb E\Psi_0-P_\star)}{\eta T}
\\
&+
\eta\left(
2L_P
+
\frac{\sqrt2\lambda C_R}{\theta}
+
\frac{2\lambda^2C_RL_R}{\theta}\eta
\right)\bar\sigma^2.
\end{aligned}
}
$$

This is the standard

$$
O\!\left(\frac1{\eta T}+\eta\sigma^2\right)
$$

stochastic first-order form whenever the bracketed coefficient is uniformly
bounded.  A horizon-dependent choice `eta = O(T^{-1/2})`, subject to the checked
small-step restrictions, gives the usual `O(T^{-1/2})` scaling.

Lean file: `OUSVRBLO/StochasticVarianceRate.lean`.

## 4. Claim boundary

The checked stochastic contribution is an expectation-level interface theorem.
It proves:

1. centered second-moment algebra;
2. expected one-step Lyapunov accounting;
3. exact gain retention;
4. uniform-noise neighborhoods;
5. explicit `1/(eta*T) + eta*sigma^2` dependence.

It does not prove that a concrete LLM/LoRA mini-batch implementation satisfies
the conditional centering, variance, smoothness, or residual-drift premises.
Those remain model-specific sufficient conditions rather than hidden conclusions.
