# OUSVR-BLO certified theorem

## Scope

The checked theorem concerns a restricted/local value-function fixed-penalty
surrogate.  A learned updater may propose an arbitrary online response, but the
response used by the main update is selected by an explicit certificate-based
accept/fallback rule.

The result is not a general nonconvex BLO convergence theorem, an original BLO
KKT theorem, or a proof that the iterates converge to a unique point.

## 1. Restricted value response

Within one analysis stage, fix a local feasible response set and define

$$
v(x)=\min_{\xi\in\mathcal Y_{\rm loc}}h(x,\xi),
\qquad
\xi^\star(x)\in\arg\min_{\xi\in\mathcal Y_{\rm loc}}h(x,\xi).
$$

The represented value-gradient interface is

$$
\nabla v(x)=\nabla_x h(x,\xi^\star(x)).
$$

The fixed-penalty objective is

$$
\bar P_\lambda(x,y)
=
F(x,y)+\lambda\bigl(h(x,y)-v(x)\bigr).
$$

For LLM fine-tuning, $h$ may be a proximal local surrogate over LoRA, adapter,
prompt, prefix, router, or small-head parameters.  The theorem does not identify
an arbitrary local response with the global value function of the original
nonconvex lower problem.

## 2. Explicit proposal acceptance and fallback

Let $R_t$ be the current response residual.  The safe base update and learned
proposal produce residuals $R_t^B$ and $R_t^P$.  Assume

$$
R_t^B\le(1-\theta)R_t+\varepsilon_t^B,
\qquad 0<\theta\le1.
$$

Let $e_t^B,e_t^P$ be the true squared value-gradient approximation errors, and
let $\widehat e_t^B,\widehat e_t^P$ be calibrated proxies:

$$
|\widehat e_t^B-e_t^B|\le\rho_t^B,
\qquad
|\widehat e_t^P-e_t^P|\le\rho_t^P.
$$

The proposal is accepted exactly when

$$
\begin{aligned}
R_t^P&\le R_t^B+\tau_t^R,\\
\widehat e_t^P
&\le\widehat e_t^B-\widehat\Delta_t+\tau_t^e,\\
0&\le\widehat\Delta_t-\tau_t^e-\rho_t^P-\rho_t^B.
\end{aligned}
$$

Define the accepted residual/error and uncertainty-adjusted gain by

$$
(R_t^O,e_t^O,\Gamma_t)=
\begin{cases}
\left(R_t^P,e_t^P,
\widehat\Delta_t-\tau_t^e-\rho_t^P-\rho_t^B\right),
&\text{if accepted},\\[1mm]
(R_t^B,e_t^B,0),&\text{otherwise}.
\end{cases}
$$

Thus fallback is part of the theorem rather than an informal convention.

Lean files:

- `AcceptedResponseSelector.lean`;
- `CertifiedProposalAcceptance.lean`.

## 3. Residual envelope and true certified gain

Define

$$
Q_t:=R_t^B+\tau_t^R,
\qquad
\varepsilon_t:=\varepsilon_t^B+\tau_t^R.
$$

Lean proves

$$
R_t^B\le Q_t,
\qquad
R_t^O\le Q_t,
\qquad
Q_t\le(1-\theta)R_t+\varepsilon_t.
$$

Proxy calibration and the selector imply

$$
\Gamma_t\ge0,
\qquad
e_t^O\le e_t^B-\Gamma_t.
$$

If the natural base-response interface is

$$
e_t^B\le C_RR_t^B+b_t,
\qquad C_R>0,
$$

then

$$
\boxed{
e_t^O\le C_RQ_t+b_t-\Gamma_t.
}
$$

Lean files:

- `SafeguardCertificate.lean`;
- `ProxyCertificate.lean`;
- `ProxySequenceCertificate.lean`;
- `SelectedEndToEndCertifiedGain.lean`.

## 4. Value-gradient error vector

Let

$$
g_t^v=\nabla v(x_t),
\qquad
g_t^B=\nabla_xh(x_t,\xi_{t+1}^B),
\qquad
g_t^P=\nabla_xh(x_t,\xi_{t+1}^P).
$$

The selector chooses $g_t^O$, and

$$
e_t^O=\|g_t^v-g_t^O\|^2.
$$

For an isometric embedding $\iota$ of the value-gradient block into the ambient
update space, define

$$
E_t=\lambda\,\iota(g_t^v-g_t^O).
$$

Lean checks the exact identity

$$
\boxed{
\|E_t\|^2=\lambda^2e_t^O
}
$$

and therefore

$$
\|E_t\|^2
\le
\lambda^2(C_RQ_t+b_t-\Gamma_t).
$$

Lean files:

- `ValueGradientErrorEmbedding.lean`;
- `ValueGradientTrajectory.lean`.

## 5. Trajectory and analytic assumptions

Let

$$
G_t=\nabla\bar P_\lambda(z_t)
$$

along the trajectory, and assume the update

$$
z_{t+1}-z_t=-\eta(G_t+E_t),
\qquad \eta>0.
$$

The objective smoothness premise is kept before update substitution:

$$
P_{t+1}
\le
P_t+\langle G_t,z_{t+1}-z_t\rangle
+\frac{L_P}{2}\|z_{t+1}-z_t\|^2,
$$

with

$$
L_P\eta\le1.
$$

The residual premise starts from the response actually selected:

$$
R_{t+1}
\le
R_t^O+\langle r_t,\Delta x_t\rangle
+\frac{L_R}{2}\|\Delta x_t\|^2+d_t,
$$

where

$$
\|r_t\|^2\le C_RQ_t+b_t,
$$

and the upper-block displacement satisfies

$$
\|\Delta x_t\|\le\eta\|G_t+E_t\|.
$$

Lean derives the substituted smoothness inequality and the displacement bound
from the actual trajectory update and a contractive upper-block map.

Lean files:

- `TrajectoryCertifiedProposalGain.lean`;
- `TrajectoryGradientSemantics.lean`;
- `ResidualSmoothnessCertificate.lean`.

## 6. Manuscript parameters

Set

$$
\mu=\frac1{\sqrt2\lambda},
$$

$$
A_\eta
=
\frac{\eta\mu}{2}+\frac{L_R\eta^2}{2}
=
\frac{\eta}{2\sqrt2\lambda}+\frac{L_R\eta^2}{2},
$$

and

$$
\beta_\eta
=
2A_\eta\lambda^2+\frac{\eta}{2\mu}
=
\sqrt2\lambda\eta+\lambda^2L_R\eta^2.
$$

Assume

$$
C_R\beta_\eta\le\frac\theta4.
$$

Define

$$
\alpha=\frac{\eta\lambda^2C_R}{\theta},
\qquad
\Psi_t=P_t+\alpha R_t.
$$

The checked budget constants are

$$
C_\varepsilon
=
\eta\lambda^2C_R
\left(\frac34+\frac1\theta\right),
$$

$$
C_b=\frac34\eta\lambda^2,
\qquad
C_d=\frac{\eta\lambda^2C_R}{\theta},
$$

and

$$
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2.
$$

Lean derives rather than assumes

$$
2\alpha A_\eta\le\frac\eta4,
$$

$$
\alpha-(1-\theta)
\left[
\frac{\eta\lambda^2C_R}{2}
+\alpha(1+C_R\beta_\eta)
\right]
\ge
\frac{\eta\lambda^2C_R}{4},
$$

and

$$
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2.
$$

Lean files:

- `ManuscriptParameters.lean`;
- `ParameterBounds.lean`.

## 7. Inexact descent

The polarization identity gives

$$
P_{t+1}
\le
P_t-rac\eta2\|G_t\|^2+rac\eta2\|E_t\|^2.
$$

Using the certified error bound,

$$
\boxed{
P_{t+1}
\le
P_t-rac\eta2\|G_t\|^2
+
\frac{\eta\lambda^2}{2}(C_RQ_t+b_t)
-
\frac{\eta\lambda^2}{2}\Gamma_t.
}
$$

Lean file: `InexactDescent.lean`.

## 8. Gain-aware residual drift

Young's inequality and

$$
\|G_t+E_t\|^2
\le2\|G_t\|^2+2\|E_t\|^2
$$

yield

$$
\boxed{
\begin{aligned}
R_{t+1}
\le
&(1+C_R\beta_\eta)Q_t
+2A_\eta\|G_t\|^2
+\beta_\eta b_t\\
&-2A_\eta\lambda^2\Gamma_t+d_t.
\end{aligned}
}
$$

The favorable gain term is retained rather than discarded.

Lean files:

- `ResidualSmoothnessCertificate.lean`;
- `ResidualDrift.lean`.

## 9. Main finite-horizon theorem

For every horizon $T$,

$$
\boxed{
\begin{aligned}
&\frac\eta4\sum_{t<T}\|G_t\|^2
+C_\Gamma\sum_{t<T}\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t\\
&\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
\end{aligned}
}
$$

A simplified checked form replaces $C_\Gamma$ by its lower bound
$\eta\lambda^2/2$.

The highest-level closure does not assume the collected one-step descent,
collected residual recursion, certified error bound, envelope contraction, or
final coefficient inequalities as independent fields.

Lean files:

- `EndToEndCertifiedGain.lean`;
- `SelectedEndToEndCertifiedGain.lean`;
- `CanonicalSelectedEndToEndCertifiedGain.lean`;
- `TrajectoryCertifiedProposalGain.lean`.

## 10. Finite-time and asymptotic consequences

Let

$$
\mathcal B_T
=
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
$$

Dropping the nonnegative gain term gives

$$
\frac1T\sum_{t<T}
\left(\|G_t\|^2+\lambda^2C_RR_t\right)
\le
\frac{4\mathcal B_T}{\eta T}.
$$

Hence one and the same iterate satisfies

$$
\boxed{
\exists t<T:\quad
\|G_t\|^2+\lambda^2C_RR_t
\le
\frac{4\mathcal B_T}{\eta T}.
}
$$

If $G_t=\nabla\bar P_\lambda(z_t)$, this is an actual objective-gradient
certificate.

If $\varepsilon_t^B$, $\tau_t^R$, $b_t$, and $d_t$ are nonnegative and
summable, then

$$
\sum_t\|G_t\|^2<\infty,
\qquad
\sum_tR_t<\infty,
\qquad
\sum_t\Gamma_t<\infty,
$$

and therefore

$$
\|G_t\|\to0,
\qquad
R_t\to0,
\qquad
\Gamma_t\to0.
$$

For a gradient-norm tolerance $\epsilon\ge0$, the horizon condition

$$
4\mathcal B_\infty\le\epsilon^2\eta T
$$

implies that some $t<T$ satisfies

$$
\|\nabla\bar P_\lambda(z_t)\|\le\epsilon,
\qquad
R_t\le\frac{\epsilon^2}{\lambda^2C_R}.
$$

Thus the gradient-norm stationarity dependence is the standard
$O(\epsilon^{-2})$.

Lean files:

- `JointCertificates.lean`;
- `SummableRates.lean`;
- `PointwiseAsymptotics.lean`;
- `TrajectoryCertifiedProposalCorollaries.lean`;
- `IterationComplexity.lean`;
- `TrajectoryIterationComplexity.lean`;
- `TrajectoryGradientSemantics.lean`.

## 11. Sufficient conditions for the base R2 certificate

The repository checks several local sufficient conditions for

$$
e_t^B\le C_RR_t^B+b_t:
$$

1. response-gradient Lipschitzness plus a response-distance error bound;
2. positive quadratic growth;
3. strong monotonicity of a computable lower-gradient residual;
4. proximal regularization dominating local hypomonotonicity, with modulus
   $\rho-\kappa>0$;
5. a contractive fixed-point/projected-response map, with constant
   $L^2/(1-q)^2$.

A scalar quadratic model verifies that the restricted response and R2 assumptions
are jointly satisfiable.

## 12. Claim boundary

The following remain explicit local analytic interfaces for a concrete neural
model:

1. local smoothness and lower boundedness of the concrete fixed-penalty
   surrogate;
2. existence and regularity of the selected restricted response branch;
3. a general nonsmooth or set-valued nonconvex Danskin theorem;
4. calibration of response-gradient, residual-gradient, and proxy constants;
5. stochastic mini-batch analogues of the deterministic inequalities;
6. projected/proximal main-variable gradient-mapping theory;
7. original BLO KKT or general nonconvex BLO global convergence.

The precise checked claim is:

> Under explicit local response, residual, calibration, and small-step
> certificates, an arbitrary learned online response proposal can be embedded
> through an accept/fallback selector without invalidating fixed-penalty
> stationarity.  Accepted uncertainty-adjusted value-gradient improvement enters
> the Lyapunov budget as a nonnegative certified gain.
