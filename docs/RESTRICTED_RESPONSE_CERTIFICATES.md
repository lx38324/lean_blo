# Restricted response and value-gradient certificates

This note records the local analytic layer connecting a restricted lower response
to the residual-to-value-gradient interface used by the OUSVR-BLO Lyapunov
theorem.  The results are deliberately local.  They do not identify an arbitrary
local neural response with the global value function of the original nonconvex
lower problem.

## 1. Restricted minimizer interface

For each upper variable `x`, let `feasible x` be the represented trust region or
restricted response set.  The selected response satisfies

$$
\xi^\star(x)\in\mathcal Y(x),
\qquad
h(x,\xi^\star(x))\le h(x,\xi)
\quad
\text{for all }\xi\in\mathcal Y(x),
$$

and

$$
v(x)=h(x,\xi^\star(x)).
$$

This is encoded by `RestrictedValueResponseInterface`.

`RestrictedEnvelope.lean` defines the proposition
`RestrictedValueResponseInterface.IsMinimizer` and proves that the selected
response is a represented minimizer.

## 2. Uniqueness from quadratic growth

Assume a local quadratic-growth condition

$$
m\,d(\xi,\xi^\star(x))^2
\le
h(x,\xi)-h(x,\xi^\star(x)),
\qquad m>0.
$$

If `xi` is another exact feasible minimizer, then its objective gap is
nonpositive, while the left-hand side is nonnegative.  Hence

$$
d(\xi,\xi^\star(x))=0,
$$

so the response is unique in the represented metric space.

Lean declaration:

```text
RestrictedValueResponseInterface.eq_response_of_quadratic_growth
```

This is uniqueness for the restricted problem only.

## 3. Local branch-envelope derivative

Let `response : X -> Y` be differentiable at `x`, and let

$$
h:X\times Y\to\mathbb R
$$

be differentiable at `(x, response x)`.  Write its derivative as `dh`.  Assume
stationarity in every response-space direction:

$$
dh(0,d\xi)=0
\quad\text{for every }d\xi.
$$

The chain rule gives

$$
D\bigl[h(x,\operatorname{response}(x))\bigr]
=
 dh\circ
 \begin{pmatrix}I\\D\operatorname{response}(x)\end{pmatrix}.
$$

The vertical contribution vanishes by stationarity, leaving exactly

$$
D\bigl[h(x,\operatorname{response}(x))\bigr]
=
 dh\circ
 \begin{pmatrix}I\\0\end{pmatrix}.
$$

Lean declarations:

```text
hasFDerivAt_branchValue_of_stationary_response
RestrictedValueResponseInterface.hasFDerivAt_value_of_stationary_response
```

This is a local differentiable-branch envelope theorem.  It is not a general
Danskin theorem for a nonsmooth or set-valued global nonconvex response map.

## 4. Response distance to value-gradient error

Suppose the upper partial gradient is locally Lipschitz in the response:

$$
\|\nabla_x h(x,\xi)-\nabla_x h(x,\xi^\star(x))\|
\le
L_{x\xi}\,d(\xi,\xi^\star(x)).
$$

Suppose also that a residual gives the response-distance error bound

$$
d(\xi,\xi^\star(x))^2
\le
C_{\rm EB}R(x,\xi)+\nu.
$$

Then Lean verifies

$$
\|\nabla_x h(x,\xi)-\nabla v(x)\|^2
\le
L_{x\xi}^2C_{\rm EB}R(x,\xi)
+L_{x\xi}^2\nu.
$$

Thus the main theorem's R2 constants can be instantiated as

$$
C_R=L_{x\xi}^2C_{\rm EB},
\qquad
b=L_{x\xi}^2\nu.
$$

Lean declarations:

```text
gradient_error_sq_le_of_lipschitz_and_error_bound
RestrictedValueGradientInterface.r2_of_lipschitz_and_error_bound
```

Quadratic growth gives the special response-distance bound

$$
d(\xi,\xi^\star(x))^2
\le
\frac{h(x,\xi)-v(x)}{m},
$$

and therefore

$$
\|\nabla_x h(x,\xi)-\nabla v(x)\|^2
\le
\frac{L_{x\xi}^2}{m}
\bigl(h(x,\xi)-v(x)\bigr).
$$

Lean declarations:

```text
RestrictedValueResponseInterface.distance_sq_le_gap_div
RestrictedValueGradientInterface.r2_of_quadratic_growth
```

## 5. Computable lower-gradient residual

Let `g_lower` denote the lower-gradient map.  Assume `g_lower` is locally
strongly monotone with modulus `m>0` relative to a stationary response:

$$
m\|\xi-\xi^\star\|^2
\le
\langle
 g_{\rm lower}(\xi)-g_{\rm lower}(\xi^\star),
 \xi-\xi^\star
\rangle,
$$

with

$$
g_{\rm lower}(\xi^\star)=0.
$$

Cauchy--Schwarz and cancellation give

$$
\|\xi-\xi^\star\|^2
\le
\frac{1}{m^2}\|g_{\rm lower}(\xi)\|^2.
$$

Hence the computable residual

$$
R(x,\xi)=\|g_{\rm lower}(x,\xi)\|^2
$$

satisfies

$$
\|\nabla_x h(x,\xi)-\nabla v(x)\|^2
\le
\frac{L_{x\xi}^2}{m^2}R(x,\xi).
$$

Lean declarations:

```text
distance_sq_le_gradient_residual_of_strong_monotonicity
eq_of_strong_monotonicity_and_stationarity
value_gradient_error_sq_le_lower_gradient_residual
```

## 6. Why proximal regularization helps

Define the proximal lower-gradient map

$$
g_\rho(\xi)
=
 g(\xi)+\rho(\xi-\bar\xi).
$$

Assume the base gradient is locally `c`-hypomonotone:

$$
-c\|\xi-\zeta\|^2
\le
\langle g(\xi)-g(\zeta),\xi-\zeta\rangle.
$$

Lean verifies the exact identity

$$
\begin{aligned}
\langle g_\rho(\xi)-g_\rho(\zeta),\xi-\zeta\rangle
&=
\langle g(\xi)-g(\zeta),\xi-\zeta\rangle
+ho\|\xi-\zeta\|^2
\end{aligned}
$$

and therefore

$$
(\rho-c)\|\xi-\zeta\|^2
\le
\langle g_\rho(\xi)-g_\rho(\zeta),\xi-\zeta\rangle.
$$

When `rho > c`, the proximal map is locally strongly monotone with modulus
`rho - c`.  A stationary proximal response is unique, and

$$
\|\nabla_xh(x,\xi)-\nabla v(x)\|^2
\le
\frac{L_{x\xi}^2}{(\rho-c)^2}
\|g_\rho(\xi)\|^2.
$$

Lean declarations:

```text
proximalLowerGradient_sub
proximalLowerGradient_inner_sub
proximalLowerGradient_strong_monotone
proximalLowerGradient_stationary_unique
value_gradient_error_sq_le_proximal_residual
```

This supplies a precise local role for proximal regularization.  Proximal
regularization does not by itself solve the original nonconvex lower problem;
it can, however, dominate a bounded amount of local negative curvature and make
the represented response residual informative.

## 7. Concrete non-vacuous instance

`QuadraticResponseExample.lean` verifies the scalar model

$$
h(k,x,\xi)=\frac12(\xi-kx)^2,
\qquad
\xi^\star(x)=kx,
\qquad
v(x)=0.
$$

For this model,

$$
\nabla_xh(k,x,\xi)=-k(\xi-kx),
$$

and Lean proves the exact identity

$$
\|\nabla_xh(k,x,\xi)-\nabla v(x)\|^2
=
2k^2\bigl(h(k,x,\xi)-v(x)\bigr).
$$

It also verifies quadratic growth, uniqueness of the restricted response, and
the generic R2 certificate.  This demonstrates that the analytic interfaces are
jointly satisfiable and are not merely formal fields with no model.

## 8. Remaining boundary

The following remain assumptions for a concrete LLM/LoRA model:

1. a restricted trajectory region on which the stated smoothness or
   hypomonotonicity bound holds;
2. differentiability of the selected response branch when the envelope derivative
   theorem is used;
3. calibration of constants such as `L_xxi`, `c`, and the residual perturbation;
4. compatibility of stochastic mini-batch estimates with the deterministic local
   inequalities.

The checked result concerns the restricted/local surrogate.  It does not prove
that the unrestricted original neural lower problem has a unique global
minimizer.
