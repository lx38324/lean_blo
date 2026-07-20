# ICML-oriented method theory package

This note records the compact theory package intended to support a method-and-
experiments ICML submission.  The theory is not positioned as a general
nonconvex bilevel-optimization result.  Its purpose is to establish three
method-facing claims:

1. arbitrary learned response proposals are fallback-safe after certification;
2. accepted calibrated improvements tighten the selected trajectory's
   stationarity bound;
3. a meaningful local proximal response class and a stochastic expected
   Lyapunov system instantiate the main abstract interfaces.

## 1. Deterministic fallback-safe theorem

For the selected trajectory, define

$$
J_t:=\|G_t\|^2+\lambda^2C_RR_t.
$$

The checked finite-horizon budget is

$$
\frac{\eta}{4}\sum_{t<T}\|G_t\|^2
+C_\Gamma\sum_{t<T}\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\le \mathcal B_T,
$$

where

$$
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2,
\qquad
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le \frac34\eta\lambda^2.
$$

The safety-only consequence is

$$
\frac1T\sum_{t<T}J_t
\le
\frac{4\mathcal B_T}{\eta T}.
$$

## 2. Gain-adjusted rate

The exact budget also gives

$$
\frac{\eta}{4}\sum_{t<T}J_t
\le
\mathcal B_T-C_\Gamma\sum_{t<T}\Gamma_t.
$$

Consequently,

$$
\boxed{
\frac1T\sum_{t<T}J_t
\le
\frac{4}{\eta T}
\left(
\mathcal B_T-C_\Gamma\sum_{t<T}\Gamma_t
\right).
}
$$

There is also a same-iterate form:

$$
\boxed{
\exists t<T:\quad
J_t
\le
\frac{4}{\eta T}
\left(
\mathcal B_T-C_\Gamma\sum_{s<T}\Gamma_s
\right).
}
$$

This is the precise theoretical benefit of the learned proposal.  It does not
compare two counterfactual trajectories.  It states that certified gain
strictly tightens the upper bound for the trajectory actually selected by the
algorithm.

Lean file: `OUSVRBLO/GainAdjustedRates.lean`.

## 3. Concrete proximal local-response instantiation

Let the local lower-gradient map before regularization be

$$
g_x(\xi),
$$

and define the proximal lower-gradient map

$$
G_{\rho,x}(\xi)
=
g_x(\xi)+\rho(\xi-\bar\xi_x).
$$

Assume the base map is locally $\kappa$-hypomonotone:

$$
\langle g_x(u)-g_x(w),u-w\rangle
\ge
-\kappa\|u-w\|^2,
$$

with

$$
\rho>\kappa.
$$

Then $G_{\rho,x}$ is $(\rho-\kappa)$-strongly monotone.  If the represented
response $\xi^\star(x)$ satisfies

$$
G_{\rho,x}(\xi^\star(x))=0,
$$

it is the unique stationary response in the modeled local region.

Assume the upper/value partial gradient is response-Lipschitz:

$$
\|\nabla_xh(x,\xi)-\nabla_xh(x,\xi^\star(x))\|
\le
L_{x\xi}\|\xi-\xi^\star(x)\|.
$$

With the computable residual

$$
R_\rho(x,\xi):=\|G_{\rho,x}(\xi)\|^2,
$$

Lean proves

$$
\boxed{
\|\nabla_xh(x,\xi)-\nabla v(x)\|^2
\le
\frac{L_{x\xi}^2}{(\rho-\kappa)^2}
R_\rho(x,\xi).
}
$$

Thus the main residual-to-value-gradient coefficient can be instantiated as

$$
C_E=\frac{L_{x\xi}^2}{(\rho-\kappa)^2}.
$$

The sequence theorem directly supplies the baseline-error field used by the
proposal/trajectory theorem.  If a common coefficient $C_R\ge C_E$ is required
for residual drift as well, and $b_t\ge0$, Lean derives

$$
e_t^B\le C_RR_t^B+b_t.
$$

Lean file: `OUSVRBLO/ProximalLocalInstantiation.lean`.

## 4. Stochastic expected theorem

The expectation-level theorem models an update perturbation $W_t$ through the
standard centered second-moment interface.  At the scalar moment level, if

$$
\mathbb E_t\langle G_t+E_t,W_t\rangle=0,
\qquad
\mathbb E_t\|W_t\|^2\le\sigma_t^2,
$$

then

$$
\mathbb E_t\|G_t+E_t+W_t\|^2
\le
\|G_t+E_t\|^2+\sigma_t^2.
$$

The expected objective descent receives the additional term

$$
\frac{L_P\eta^2}{2}\sigma_t^2,
$$

and the expected residual drift receives

$$
A_\eta\sigma_t^2.
$$

After Lyapunov coupling, define

$$
C_\sigma
:=
\frac{L_P\eta^2}{2}+\alpha A_\eta.
$$

The checked expected finite-horizon budget is

$$
\boxed{
\begin{aligned}
&\frac{\eta}{4}\sum_{t<T}\mathbb E\|G_t\|^2
+C_\Gamma\sum_{t<T}\mathbb E\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}\mathbb ER_t
\\
&\le
\mathbb E\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\mathbb E\varepsilon_t
+C_b\sum_{t<T}\mathbb Eb_t
+C_d\sum_{t<T}\mathbb Ed_t
+C_\sigma\sum_{t<T}\sigma_t^2.
\end{aligned}
}
$$

The gain-adjusted expected average form is

$$
\frac1T\sum_{t<T}
\left(
\mathbb E\|G_t\|^2+\lambda^2C_R\mathbb ER_t
\right)
\le
\frac{4}{\eta T}
\left[
\mathcal B_T^{\rm stoch}
-C_\Gamma\sum_{t<T}\mathbb E\Gamma_t
\right].
$$

For uniform bounds

$$
\mathbb E\varepsilon_t\le\bar\varepsilon,
\quad
\mathbb Eb_t\le\bar b,
\quad
\mathbb Ed_t\le\bar d,
\quad
\sigma_t^2\le\bar\sigma^2,
$$

Lean proves the expected neighborhood

$$
\frac1T\sum_{t<T}
\left(
\mathbb E\|G_t\|^2+\lambda^2C_R\mathbb ER_t
\right)
\le
\frac{4(\mathbb E\Psi_0-P_\star)}{\eta T}
+
\frac{4}{\eta}
\left(
C_\varepsilon\bar\varepsilon
+C_b\bar b
+C_d\bar d
+C_\sigma\bar\sigma^2
\right).
$$

Lean file: `OUSVRBLO/StochasticExpectedGain.lean`.

## 5. Claim boundary

The stochastic file machine-checks the expectation-level Lyapunov algebra from
centered moment and expected one-step interfaces.  It does not yet formalize a
specific mini-batch sampling distribution, measurability of a concrete neural
network training loop, or conditional expectation in a filtration.  Those are
model-specific sufficient conditions for the expected one-step interfaces, not
claims silently assumed to have been verified.

The paper-facing theoretical claim should therefore remain:

> Certified learned value-anchor proposals preserve restricted/local
> fixed-penalty stationarity; accepted calibrated improvements tighten the
> selected trajectory's finite-horizon bound; local proximal response models
> instantiate the key response-error certificate; and centered stochastic
> perturbations produce an explicit expected variance budget.
