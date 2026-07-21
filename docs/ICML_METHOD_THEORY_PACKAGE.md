# ICML-oriented method theory package

This note records the compact theory package intended to support a
method-and-experiments ICML submission. The theory is not positioned as a
general nonconvex bilevel-optimization result. Its purpose is to establish four
method-facing claims:

1. arbitrary learned response proposals are fallback-safe after certification;
2. accepted calibrated improvements tighten the selected trajectory's bound;
3. a meaningful proximal local-response class instantiates the key response
   error interface;
4. centered stochastic perturbations yield an explicit expected variance rate.

Stable paper-facing Lean names are exported from
`OUSVRBLO/ICMLTheoryPackage.lean`. The full assumption audit is in
`docs/ICML_THEORY_DEPENDENCY_AUDIT.md`.

## 1. Fallback-safe deterministic theorem

For the selected trajectory, define

$$
J_t:=\|G_t\|^2+\lambda^2C_RR_t.
$$

The checked finite-horizon budget is

$$
\boxed{
\frac{\eta}{4}\sum_{t<T}\|G_t\|^2
+C_\Gamma\sum_{t<T}\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\le \mathcal B_T.
}
$$

Here

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

The proposal generator is unrestricted before certification. The explicit
selector accepts only when the residual, proxy-comparison, and nonnegative-margin
tests pass; otherwise the update uses the safe base response and records zero
certified gain.

Stable Lean declaration:

```text
OUSVRBLO.ICMLTheoryPackage.fallback_safe_finite_horizon
```

## 2. Gain-adjusted selected-trajectory rate

Retaining the favorable term instead of dropping it gives

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

There is also a same-horizon existence form:

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

Lean verifies

$$
\mathcal B_T-C_\Gamma\sum_{t<T}\Gamma_t
\le
\mathcal B_T,
$$

and the inequality is strict whenever

$$
\sum_{t<T}\Gamma_t>0.
$$

This is the precise theoretical benefit of the learned proposal. It does not
compare two counterfactual trajectories. It states that positive certified gain
strictly tightens the upper bound for the trajectory actually selected by the
algorithm.

Stable Lean declarations:

```text
OUSVRBLO.ICMLTheoryPackage.certified_gain_same_iterate
OUSVRBLO.ICMLTheoryPackage.certified_gain_objective_gradient_same_iterate
OUSVRBLO.ICMLTheoryPackage.positive_gain_strictly_tightens
```

## 3. Concrete proximal local-response instantiation

Let the local lower-gradient map before regularization be

$$
g_x(\xi),
$$

and define

$$
G_{\rho,x}(\xi)
=
g_x(\xi)+\rho(\xi-\bar\xi_x).
$$

Assume local $\kappa$-hypomonotonicity:

$$
\langle g_x(u)-g_x(w),u-w\rangle
\ge
-\kappa\|u-w\|^2,
$$

with

$$
\rho>\kappa.
$$

Then $G_{\rho,x}$ is $(\rho-\kappa)$-strongly monotone. If the represented
response satisfies

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

For the computable residual

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

Thus

$$
C_E=\frac{L_{x\xi}^2}{(\rho-\kappa)^2}
$$

instantiates the main residual-to-value-gradient coefficient. The sequence
version directly supplies the baseline error certificate. If a common
coefficient $C_R\ge C_E$ is needed for residual drift and $b_t\ge0$, Lean derives

$$
e_t^B\le C_RR_t^B+b_t.
$$

Stable Lean declarations:

```text
OUSVRBLO.ICMLTheoryPackage.proximal_response_error_certificate
OUSVRBLO.ICMLTheoryPackage.proximal_baseline_sequence_certificate
```

## 4. Stochastic expectation-level theorem

The stochastic layer models an update perturbation $W_t$ through a centered
second-moment interface. At the scalar conditional-moment level, if

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

The expected objective descent receives

$$
\frac{L_P\eta^2}{2}\sigma_t^2,
$$

and expected residual drift receives

$$
A_\eta\sigma_t^2.
$$

Define

$$
C_\sigma
:=
\frac{L_P\eta^2}{2}+\alpha A_\eta.
$$

Lean proves

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

The gain-adjusted expected average retains

$$
C_\Gamma\sum_{t<T}\mathbb E\Gamma_t.
$$

Uniform certificate-error and variance bounds give an explicit expected
neighborhood.

For zero certificate bias and the manuscript coefficient

$$
A_\eta
=
\frac{\eta}{2\sqrt2\lambda}
+
\frac{L_R\eta^2}{2},
$$

Lean checks

$$
\frac{4C_\sigma}{\eta}
=
\eta
\left(
2L_P
+
\frac{\sqrt2\lambda C_R}{\theta}
+
\frac{2\lambda^2C_RL_R}{\theta}\eta
\right).
$$

Therefore the expected joint stationarity/residual rate has the explicit form

$$
\boxed{
O\!\left(\frac1{\eta T}+\eta\sigma^2\right)
}
$$

when the bracketed coefficient is bounded. A horizon-dependent
$\eta=O(T^{-1/2})$, subject to the checked small-step restrictions, gives the
standard $O(T^{-1/2})$ scaling.

Stable Lean declarations:

```text
OUSVRBLO.ICMLTheoryPackage.stochastic_expected_finite_horizon
OUSVRBLO.ICMLTheoryPackage.stochastic_expected_gain_adjusted_average
OUSVRBLO.ICMLTheoryPackage.stochastic_variance_rate
```

## 5. Recommended main-text presentation

For a method-oriented paper, use the following order:

1. fallback-safe finite-horizon theorem;
2. gain-adjusted corollary and strict-tightening statement;
3. proximal local-response instantiation;
4. stochastic expected corollary.

The full coefficient derivation, Cesaro/summability variants, pointwise
consequences, and detailed Lean coverage map can remain in the appendix.

## 6. Claim boundary

The stochastic theorem machine-checks expectation-level Lyapunov algebra from
centered moment and expected one-step interfaces. It does not formalize a
specific mini-batch distribution, measurability of a neural network training
loop, conditional expectation in a concrete filtration, or high-probability
concentration.

The full package also does not prove:

```text
global nonconvex lower-level optimality
original BLO KKT convergence
global or set-valued Danskin theory
counterfactual online-versus-baseline trajectory dominance
projected main-variable stationarity
convergence of the iterates to a unique point
```

The paper-facing claim should remain:

> Certified learned value-anchor proposals preserve restricted/local
> fixed-penalty stationarity; accepted calibrated improvements tighten the
> selected trajectory's finite-horizon bound; a proximal local response model
> instantiates the key response-error certificate; and centered stochastic
> perturbations produce an explicit expected variance rate.
