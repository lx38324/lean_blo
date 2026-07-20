# OUSVR-BLO certified theorem

## 1. Scope and precise claim

This repository verifies a certificate-facing theorem for a safeguarded online
value-anchor method applied to a restricted/local fixed-penalty value-function
BLO surrogate.

The machine-learning-facing interpretation is:

> A learned updater may propose an arbitrary online response.  The proposal is
> used only when explicit residual-safety, calibrated proxy-improvement, and
> nonnegative-margin certificates pass.  Otherwise the method uses a safe base
> response and assigns zero certified gain to that round.

The theorem establishes fixed-penalty stationarity for the represented local
surrogate.  It does not establish general nonconvex BLO convergence, original
BLO KKT convergence, global lower-level optimality, or convergence of the
iterates to a unique point.

The accept/fallback selector is defined by deciding inequalities over real
numbers inside a `noncomputable` section.  It is a proof-level mathematical
selector, not an extracted floating-point implementation.

## 2. Restricted local value response

For every upper variable `x`, let `feasible x` be a represented local response
set.  The response interface stores

$$
\xi^\star(x)\in\mathcal Y(x),
$$

$$
h(x,\xi^\star(x))\le h(x,\xi)
\quad\text{for every }\xi\in\mathcal Y(x),
$$

and

$$
v(x)=h(x,\xi^\star(x)).
$$

This is a restricted/local value model.  An arbitrary local response is not
identified with the global minimizer of the original nonconvex lower problem.

The represented value-gradient interface is

$$
\nabla v(x)=\nabla_x h(x,\xi^\star(x)).
$$

The repository supports this identity in two ways.

First, it can be supplied as an abstract restricted value-gradient interface.
Second, a local differentiable-branch envelope theorem proves it from:

1. differentiability of `h` at `(x, response x)`;
2. differentiability of the selected response branch at `x`;
3. stationarity in every response-space direction.

If `dh` is the derivative of `h`, the vertical stationarity premise is

$$
dh(0,d\xi)=0
\quad\text{for every }d\xi.
$$

The chain rule then gives

$$
D\bigl[h(x,\xi^\star(x))\bigr]
=
 dh\circ
 \begin{pmatrix}I\\0\end{pmatrix}.
$$

This is a local differentiable-branch envelope theorem, not a general nonsmooth
or set-valued Danskin theorem.

Lean files:

- `OUSVRBLO/LocalSurrogate.lean`;
- `OUSVRBLO/RestrictedEnvelope.lean`.

## 3. Base and learned proposal data

At round `t`, the safe base response and learned proposal have residuals

$$
R_t^B,
\qquad
R_t^P,
$$

true squared value-gradient errors

$$
e_t^B,
\qquad
e_t^P,
$$

and calibrated computable proxies

$$
\widehat e_t^B,
\qquad
\widehat e_t^P.
$$

The vector-valued proposal layer can define the true errors rather than accepting
unrelated scalar fields.  Given

$$
g_t^v=\nabla v(x_t),
$$

$$
g_t^B=\nabla_xh(x_t,\xi_t^B),
\qquad
g_t^P=\nabla_xh(x_t,\xi_t^P),
$$

it sets

$$
e_t^B=\|g_t^v-g_t^B\|^2,
\qquad
e_t^P=\|g_t^v-g_t^P\|^2.
$$

`RestrictedValueProposalData` constructs these sequences directly from a
restricted value-gradient interface and feasible base/proposal response
sequences.

Lean files:

- `OUSVRBLO/RestrictedValueProposalData.lean`;
- `OUSVRBLO/ValueGradientErrorEmbedding.lean`.

## 4. Explicit certificate-generated acceptance

Define the uncertainty-adjusted proposal margin

$$
M_t
=
\widehat\Delta_t
-
\tau_t^e
-
\rho_t^P
-
\rho_t^B.
$$

The proposal is accepted exactly when all three tests hold:

$$
R_t^P\le R_t^B+\tau_t^R,
$$

$$
\widehat e_t^P
\le
\widehat e_t^B-\widehat\Delta_t+\tau_t^e,
$$

and

$$
0\le M_t.
$$

The selected residual, true error, and certified gain are

$$
R_t^O
=
\begin{cases}
R_t^P,&\text{if accepted},\\
R_t^B,&\text{if rejected},
\end{cases}
$$

$$
e_t^O
=
\begin{cases}
e_t^P,&\text{if accepted},\\
e_t^B,&\text{if rejected},
\end{cases}
$$

and

$$
\Gamma_t
=
\begin{cases}
M_t,&\text{if accepted},\\
0,&\text{if rejected}.
\end{cases}
$$

Thus fallback is part of the checked theorem rather than an informal convention.
Lean also checks

$$
R_t^O\ge0,
\qquad
e_t^O\ge0,
\qquad
\Gamma_t\ge0.
$$

Lean files:

- `OUSVRBLO/AcceptedResponseSelector.lean`;
- `OUSVRBLO/CertifiedProposalAcceptance.lean`;
- `OUSVRBLO/CertifiedGainFeasibility.lean`.

## 5. Residual safeguard envelope

Assume the safe base response contracts:

$$
R_t^B
\le
(1-\theta)R_t+\varepsilon_t^B,
\qquad
0<\theta\le1.
$$

Define

$$
Q_t:=R_t^B+\tau_t^R,
$$

and

$$
\varepsilon_t:=\varepsilon_t^B+\tau_t^R.
$$

The selector and nonnegativity of the residual tolerance imply

$$
R_t^B\le Q_t,
$$

$$
R_t^O\le Q_t,
$$

and

$$
\boxed{
Q_t\le(1-\theta)R_t+\varepsilon_t.
}
$$

Lean file: `OUSVRBLO/SafeguardCertificate.lean`.

## 6. Calibrated true gain and error-scale feasibility

Assume asymmetric calibration:

$$
|\widehat e_t^P-e_t^P|\le\rho_t^P,
$$

$$
|\widehat e_t^B-e_t^B|\le\rho_t^B.
$$

The selector proves in both branches that

$$
\boxed{
e_t^O\le e_t^B-\Gamma_t.
}
$$

Suppose the natural base-response certificate is

$$
e_t^B\le C_RR_t^B+b_t,
\qquad C_R>0.
$$

Since `Rbase_t <= Q_t`, Lean derives

$$
\boxed{
e_t^O\le C_RQ_t+b_t-\Gamma_t.
}
$$

The nonnegativity of the selected true squared error further gives

$$
\Gamma_t\le e_t^B,
$$

and

$$
\boxed{
0\le C_RQ_t+b_t-\Gamma_t.
}
$$

Therefore no separate effective-gain clipping operation is needed in the public
theorem.

The common notation `C_R Q_t+b_t` does not require two primitive analytic
interfaces to have identical constants.  If

$$
a_t\le C_1Q_t+b_t^{(1)},
$$

and

$$
c_t\le C_2Q_t+b_t^{(2)},
$$

with `Q_t >= 0`, then Lean verifies that both are bounded by

$$
\max\{C_1,C_2\}Q_t
+
\max\{b_t^{(1)},b_t^{(2)}\}.
$$

If both bias sequences are nonnegative and summable, their pointwise maximum is
also summable.

Lean files:

- `OUSVRBLO/ProxyCertificate.lean`;
- `OUSVRBLO/ProxySequenceCertificate.lean`;
- `OUSVRBLO/CertifiedGainFeasibility.lean`;
- `OUSVRBLO/CommonResidualScale.lean`.

## 7. Exact ambient inexact-gradient error

Let `embed` be an isometric linear embedding of the represented value-gradient
space into the ambient update space.  Define the selected response gradient

$$
g_t^O
=
\begin{cases}
g_t^P,&\text{if accepted},\\
g_t^B,&\text{if rejected},
\end{cases}
$$

and the signed value-gradient error

$$
\delta_t^v:=g_t^v-g_t^O.
$$

The ambient error is

$$
E_t:=\lambda\,\operatorname{embed}(\delta_t^v).
$$

Lean proves the exact identity

$$
\boxed{
\|E_t\|^2=\lambda^2e_t^O.
}
$$

Combining this with the calibrated residual certificate gives

$$
\boxed{
\|E_t\|^2
\le
\lambda^2(C_RQ_t+b_t-\Gamma_t).
}
$$

Lean files:

- `OUSVRBLO/ValueGradientErrorEmbedding.lean`;
- `OUSVRBLO/ValueGradientTrajectory.lean`.

## 8. Fixed-penalty gradient semantics and coupling

Let the represented fixed-penalty objective be

$$
P(z)
=
F(z)+\lambda\bigl(h(z)-v(z)\bigr).
$$

For component gradients

$$
g_t^F,
\qquad
g_t^h,
\qquad
g_t^v,
$$

Lean verifies

$$
\nabla P(z_t)
=
 g_t^F+\lambda(g_t^h-g_t^v).
$$

The trajectory theorem calls this exact gradient `G_t`.  The coupling
certificate requires the value-gradient component appearing in this decomposition
to be exactly the represented value gradient used by the proposal/error layer:

$$
G_t
=
 g_t^F
+
\lambda
\left(
 g_t^h-\operatorname{embed}(g_t^v)
\right).
$$

Since

$$
E_t
=
\lambda\operatorname{embed}(g_t^v-g_t^O),
$$

Lean derives

$$
\boxed{
G_t+E_t
=
 g_t^F
+
\lambda
\left(
 g_t^h-\operatorname{embed}(g_t^O)
\right).
}
$$

Thus the actual update direction is the fixed-penalty gradient in which the exact
value gradient is replaced by the response gradient selected by the certificates.
The theorem does not merely add an unrelated abstract error vector to an
unrelated descent vector.

Lean files:

- `OUSVRBLO/FixedPenaltyGradientSemantics.lean`;
- `OUSVRBLO/ValueGradientFixedPenaltyCoupling.lean`;
- `OUSVRBLO/TrajectoryGradientSemantics.lean`.

## 9. Trajectory and local analytic premises

The deterministic trajectory satisfies

$$
z_{t+1}-z_t=-\eta(G_t+E_t),
\qquad \eta>0.
$$

The local objective smoothness premise is stored before substituting the update:

$$
P_{t+1}
\le
P_t
+
\langle G_t,z_{t+1}-z_t\rangle
+
\frac{L_P}{2}\|z_{t+1}-z_t\|^2,
$$

with

$$
L_P\eta\le1.
$$

Let `projectX` be a contractive continuous linear map extracting the
upper-variable displacement:

$$
\|\operatorname{projectX}(u)\|\le\|u\|.
$$

Define

$$
\Delta x_t
=
\operatorname{projectX}(z_{t+1}-z_t).
$$

The update identity implies

$$
\boxed{
\|\Delta x_t\|
\le
\eta\|G_t+E_t\|.
}
$$

The residual smoothness premise starts from the response actually selected:

$$
R_{t+1}
\le
R_t^O
+
\langle r_t,\Delta x_t\rangle
+
\frac{L_R}{2}\|\Delta x_t\|^2
+d_t,
$$

where

$$
\|r_t\|^2\le C_RQ_t+b_t.
$$

Since `R_t^O <= Q_t`, Lean lifts this to the envelope-based residual smoothness
interface consumed by the drift proof.

The objective is assumed lower bounded along the trajectory:

$$
P_t\ge P_\star.
$$

Lean files:

- `OUSVRBLO/TrajectoryCertifiedProposalGain.lean`;
- `OUSVRBLO/ResidualSmoothnessCertificate.lean`;
- `OUSVRBLO/SelectedEndToEndCertifiedGain.lean`.

## 10. Manuscript parameterization

Set

$$
\mu=\frac{1}{\sqrt2\lambda},
$$

$$
A_\eta
=
\frac{\eta\mu}{2}
+
\frac{L_R\eta^2}{2}
=
\frac{\eta}{2\sqrt2\lambda}
+
\frac{L_R\eta^2}{2},
$$

and

$$
\beta_\eta
=
2A_\eta\lambda^2+
\frac{\eta}{2\mu}
=
\sqrt2\lambda\eta
+
\lambda^2L_R\eta^2.
$$

Assume

$$
\boxed{
C_R\beta_\eta\le\frac\theta4.
}
$$

Define

$$
\alpha
=
\frac{\eta\lambda^2C_R}{\theta},
$$

and

$$
\Psi_t=P_t+\alpha R_t.
$$

The checked error coefficients are

$$
C_\varepsilon
=
\eta\lambda^2C_R
\left(
\frac34+rac1\theta
\right),
$$

$$
C_b=\frac34\eta\lambda^2,
$$

and

$$
C_d=\alpha
=
\frac{\eta\lambda^2C_R}{\theta}.
$$

The exact favorable gain coefficient is

$$
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+
2\alpha A_\eta\lambda^2.
$$

Lean derives rather than assumes

$$
2\alpha A_\eta\le\frac\eta4,
$$

$$
\alpha-(1-\theta)
\left[
\frac{\eta\lambda^2C_R}{2}
+
\alpha(1+C_R\beta_\eta)
\right]
\ge
\frac{\eta\lambda^2C_R}{4},
$$

and

$$
\boxed{
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2.
}
$$

Lean files:

- `OUSVRBLO/ManuscriptParameters.lean`;
- `OUSVRBLO/ParameterBounds.lean`.

## 11. Transparent sufficient step-size conditions

The small-step condition can be split into a linear and a quadratic budget:

$$
C_R\sqrt2\lambda\eta\le\frac\theta8,
$$

and

$$
C_R\lambda^2L_R\eta^2\le\frac\theta8.
$$

Lean verifies that these imply

$$
C_R\beta_\eta\le\frac\theta4.
$$

A direct sufficient bound for the linear part is

$$
\eta
\le
\frac{\theta}
{8C_R\sqrt2\lambda}.
$$

When `L_R>0`, a direct sufficient bound for the quadratic part is

$$
\eta^2
\le
\frac{\theta}
{8C_R\lambda^2L_R}.
$$

When `L_R=0`, the quadratic part is automatic.  These are combined with the
objective-smoothness condition

$$
L_P\eta\le1.
$$

Lean file: `OUSVRBLO/ExplicitStepSize.lean`.

## 12. Inexact objective descent

The smoothness inequality and trajectory update give

$$
P_{t+1}
\le
P_t
-
\eta\langle G_t,G_t+E_t\rangle
+
\frac{L_P\eta^2}{2}\|G_t+E_t\|^2.
$$

Using the polarization identity and `L_P eta <= 1`, Lean proves

$$
P_{t+1}
\le
P_t
-
\frac\eta2\|G_t\|^2
+
\frac\eta2\|E_t\|^2.
$$

The certified error bound therefore yields

$$
\boxed{
\begin{aligned}
P_{t+1}
\le{}&
P_t
-
\frac\eta2\|G_t\|^2
+
\frac{\eta\lambda^2}{2}(C_RQ_t+b_t)
\\
&-
\frac{\eta\lambda^2}{2}\Gamma_t.
\end{aligned}
}
$$

Lean file: `OUSVRBLO/InexactDescent.lean`.

## 13. Gain-aware residual drift

Define

$$
H_t:=\sqrt{C_RQ_t+b_t}.
$$

The canonical theorem constructs this quantity internally and proves

$$
H_t\ge0,
\qquad
H_t^2=C_RQ_t+b_t.
$$

It also defines

$$
s_t:=\|G_t+E_t\|,
$$

and verifies

$$
s_t^2
\le
2\|G_t\|^2+2\|E_t\|^2.
$$

Residual smoothness, Cauchy--Schwarz, Young's inequality, and the certified
error bound yield

$$
\boxed{
\begin{aligned}
R_{t+1}
\le{}&
(1+C_R\beta_\eta)Q_t
+
2A_\eta\|G_t\|^2
+
\beta_\eta b_t
\\
&-
2A_\eta\lambda^2\Gamma_t
+
d_t.
\end{aligned}
}
$$

The favorable gain is retained in both objective descent and residual drift.

Lean files:

- `OUSVRBLO/ResidualSmoothnessCertificate.lean`;
- `OUSVRBLO/ResidualDrift.lean`;
- `OUSVRBLO/CanonicalSelectedEndToEndCertifiedGain.lean`.

## 14. Exact finite-horizon theorem

For every finite horizon `T`, the complete certificate chain proves

$$
\boxed{
\begin{aligned}
&\frac\eta4\sum_{t<T}\|G_t\|^2
+
C_\Gamma\sum_{t<T}\Gamma_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\\
&\le
\Psi_0-P_\star
+
C_\varepsilon\sum_{t<T}\varepsilon_t
+
C_b\sum_{t<T}b_t
+
C_d\sum_{t<T}d_t.
\end{aligned}
}
$$

The conventional simplified form replaces `C_Gamma` by its checked lower bound:

$$
\boxed{
\begin{aligned}
&\frac\eta4\sum_{t<T}\|G_t\|^2
+
\frac{\eta\lambda^2}{2}\sum_{t<T}\Gamma_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\\
&\le
\Psi_0-P_\star
+
C_\varepsilon\sum_{t<T}\varepsilon_t
+
C_b\sum_{t<T}b_t
+
C_d\sum_{t<T}d_t.
\end{aligned}
}
$$

The highest-level trajectory API derives rather than assumes:

- the accept/fallback decision;
- selected response residual, true error, and gain;
- residual envelope contraction;
- gain-aware error-scale feasibility;
- the exact ambient error norm identity;
- post-substitution objective smoothness;
- upper-block displacement control;
- the residual drift recursion;
- every final Lyapunov coefficient bound.

Principal Lean files:

- `OUSVRBLO/EndToEndCertifiedGain.lean`;
- `OUSVRBLO/SelectedEndToEndCertifiedGain.lean`;
- `OUSVRBLO/CanonicalSelectedEndToEndCertifiedGain.lean`;
- `OUSVRBLO/TrajectoryCertifiedProposalGain.lean`;
- `OUSVRBLO/ValueGradientTrajectory.lean`.

## 15. Finite-time same-iterate certificates

Define the nonnegative performance measure

$$
\mathcal J_t
:=
\|G_t\|^2+
\lambda^2C_RR_t.
$$

The favorable gain is not included because it is not an error quantity that
should be made small.

For every `T>0`, Lean proves

$$
\boxed{
\exists t<T:\quad
\|G_t\|^2+
\lambda^2C_RR_t
\le
\frac{4\mathcal B_T}{\eta T},
}
$$

where

$$
\mathcal B_T
=
\Psi_0-P_\star
+
C_\varepsilon\sum_{t<T}\varepsilon_t
+
C_b\sum_{t<T}b_t
+
C_d\sum_{t<T}d_t.
$$

This is a same-iterate statement: stationarity and response control hold on one
and the same accepted-response round.

The exact gain-accounting density

$$
\|G_t\|^2
+
2\lambda^2\Gamma_t
+
\lambda^2C_RR_t
$$

is retained separately for budget accounting, but it is not called a performance
metric.

Lean files:

- `OUSVRBLO/FiniteTimeCorollaries.lean`;
- `OUSVRBLO/JointCertificates.lean`.

## 16. Summable perturbations and pointwise convergence

Assume the nonnegative sequences

$$
\varepsilon_t^B,
\qquad
\tau_t^R,
\qquad
b_t,
\qquad
d_t
$$

are summable.  Since

$$
\varepsilon_t=\varepsilon_t^B+\tau_t^R,
$$

`eps_t` is summable as well.

Define

$$
\mathcal B_\infty
=
\Psi_0-P_\star
+
C_\varepsilon\sum_{t=0}^{\infty}\varepsilon_t
+
C_b\sum_{t=0}^{\infty}b_t
+
C_d\sum_{t=0}^{\infty}d_t.
$$

Lean proves the explicit same-iterate rate

$$
\boxed{
\exists t<T:\quad
\|G_t\|^2+
\lambda^2C_RR_t
\le
\frac{4\mathcal B_\infty}{\eta T}.
}
$$

It also proves

$$
\sum_t\|G_t\|^2<\infty,
$$

$$
\sum_tR_t<\infty,
$$

and

$$
\sum_t\Gamma_t<\infty.
$$

Consequently

$$
\boxed{
\|G_t\|\to0,
\qquad
R_t\to0,
\qquad
\Gamma_t\to0.
}
$$

The gain limit is a consequence of a finite nonnegative favorable budget.  It
does not make small gain an optimization objective.

If `G_t` is certified as the actual objective gradient and

$$
4\mathcal B_\infty
\le
\epsilon^2\eta T,
$$

then some `t<T` satisfies

$$
\boxed{
\|\nabla P(z_t)\|\le\epsilon,
\qquad
R_t\le
\frac{\epsilon^2}{\lambda^2C_R}.
}
$$

Thus the checked gradient-norm stationarity dependence is

$$
O(\epsilon^{-2}).
$$

Lean files:

- `OUSVRBLO/SummableCorollaries.lean`;
- `OUSVRBLO/SummableRates.lean`;
- `OUSVRBLO/PointwiseAsymptotics.lean`;
- `OUSVRBLO/AnalyticPointwise.lean`;
- `OUSVRBLO/IterationComplexity.lean`;
- `OUSVRBLO/TrajectoryIterationComplexity.lean`;
- `OUSVRBLO/TrajectoryCertifiedProposalCorollaries.lean`;
- `OUSVRBLO/TrajectoryGradientSemantics.lean`.

## 17. Persistent bounded perturbations and error floors

Summability is not appropriate for every stochastic or fixed-tolerance regime.
Define the one-round weighted perturbation

$$
\delta_t
:=
C_\varepsilon\varepsilon_t
+
C_bb_t
+
C_dd_t.
$$

Suppose

$$
\delta_t\le\bar\delta
\quad\text{for every }t.
$$

Then the accumulated right-hand side grows at most linearly:

$$
\mathcal B_T
\le
\Psi_0-P_\star+T\bar\delta.
$$

Lean derives the average neighborhood bound

$$
\boxed{
\frac1T\sum_{t<T}
\left(
\|G_t\|^2+
\lambda^2C_RR_t
\right)
\le
\frac{4(\Psi_0-P_\star)}{\eta T}
+
\frac{4\bar\delta}{\eta}.
}
$$

It also proves the same-iterate version

$$
\boxed{
\exists t<T:\quad
\|G_t\|^2+
\lambda^2C_RR_t
\le
\frac{4(\Psi_0-P_\star)}{\eta T}
+
\frac{4\bar\delta}{\eta}.
}
$$

Thus the theory distinguishes:

$$
\text{summable perturbations}
\Longrightarrow
O(1/T)\text{ and pointwise convergence},
$$

from

$$
\text{persistent bounded perturbations}
\Longrightarrow
\text{a certified stationarity/residual neighborhood}.
$$

Separate uniform bounds

$$
\varepsilon_t\le\bar\varepsilon,
\qquad
b_t\le\bar b,
\qquad
d_t\le\bar d
$$

supply

$$
\bar\delta
=
C_\varepsilon\bar\varepsilon
+
C_b\bar b
+
C_d\bar d.
$$

Lean file: `OUSVRBLO/PersistentErrorFloor.lean`.

## 18. Local sufficient conditions for the base R2 certificate

The theorem-facing baseline condition is

$$
e_t^B\le C_RR_t^B+b_t.
$$

The repository checks several local sufficient conditions.

### 18.1 Response-gradient Lipschitzness and a distance error bound

If

$$
\|\nabla_xh(x,\xi)-\nabla_xh(x,\xi^\star)\|
\le
L\,d(\xi,\xi^\star),
$$

and

$$
d(\xi,\xi^\star)^2
\le
C_{\rm EB}R+\nu,
$$

then

$$
\|\nabla_xh(x,\xi)-\nabla v(x)\|^2
\le
L^2C_{\rm EB}R+L^2\nu.
$$

### 18.2 Positive quadratic growth

If

$$
m\,d(\xi,\xi^\star)^2
\le
h(x,\xi)-v(x),
\qquad m>0,
$$

then

$$
\|\nabla_xh(x,\xi)-\nabla v(x)\|^2
\le
\frac{L^2}{m}
\bigl(h(x,\xi)-v(x)\bigr).
$$

Positive quadratic growth also makes the represented exact minimizer unique.

### 18.3 Strongly monotone lower-gradient residual

If the lower-gradient map is strongly monotone with modulus `m>0` around a
stationary response, then

$$
\|\xi-\xi^\star\|^2
\le
\frac1{m^2}\|g_{\rm lower}(\xi)\|^2,
$$

and hence

$$
\|\nabla_xh(x,\xi)-\nabla v(x)\|^2
\le
\frac{L^2}{m^2}\|g_{\rm lower}(\xi)\|^2.
$$

### 18.4 Proximal domination of local negative curvature

Let

$$
g_\rho(\xi)
=
g(\xi)+\rho(\xi-\bar\xi).
$$

If the base lower-gradient map is locally `c`-hypomonotone and

$$
\rho>c,
$$

then the proximal map is strongly monotone with modulus

$$
\rho-c.
$$

The resulting R2 certificate is

$$
\|\nabla_xh(x,\xi)-\nabla v(x)\|^2
\le
\frac{L^2}{(\rho-c)^2}
\|g_\rho(\xi)\|^2.
$$

### 18.5 Contractive fixed-point response residual

If `step` has fixed point `xi_star` and contraction factor `0<=q<1`, then

$$
d(\xi,\xi^\star)
\le
\frac1{1-q}
d(\xi,\operatorname{step}(\xi)),
$$

and

$$
\|\nabla_xh(x,\xi)-\nabla v(x)\|^2
\le
\frac{L^2}{(1-q)^2}
 d(\xi,\operatorname{step}(\xi))^2.
$$

Lean files:

- `OUSVRBLO/ResponseErrorBound.lean`;
- `OUSVRBLO/StrongMonotonicityCertificate.lean`;
- `OUSVRBLO/ProximalResponseCertificate.lean`;
- `OUSVRBLO/ContractionResidualCertificate.lean`;
- `OUSVRBLO/QuadraticResponseExample.lean`.

## 19. Concrete non-vacuous model

The scalar quadratic example uses

$$
h(k,x,\xi)
=
\frac12(\xi-kx)^2,
$$

$$
\xi^\star(x)=kx,
$$

and

$$
v(x)=0.
$$

Its upper partial gradient is

$$
\nabla_xh(k,x,\xi)
=-k(\xi-kx).
$$

Lean proves the exact identity

$$
\boxed{
\|\nabla_xh(k,x,\xi)-\nabla v(x)\|^2
=
2k^2\bigl(h(k,x,\xi)-v(x)\bigr).
}
$$

It also proves quadratic growth and uniqueness of the represented response.  The
example demonstrates that the restricted response and R2 interfaces are jointly
satisfiable.

Lean file: `OUSVRBLO/QuadraticResponseExample.lean`.

## 20. Remaining analytic and algorithmic boundary

The following remain explicit local interfaces for a concrete LLM/LoRA model:

1. local smoothness and lower boundedness of the concrete fixed-penalty
   surrogate;
2. a trajectory region on which quadratic growth, hypomonotonicity, strong
   monotonicity, or contraction holds with calibrated constants;
3. differentiability and regularity of the selected restricted response branch;
4. a general nonsmooth or set-valued nonconvex Danskin theorem;
5. calibration of response-gradient, residual-gradient, and proxy constants;
6. stochastic mini-batch analogues of the deterministic local inequalities;
7. projected or proximal main-variable gradient-mapping theory;
8. original BLO KKT convergence or general nonconvex BLO global convergence;
9. convergence of the iterates to a unique point;
10. extraction and numerical robustness of the proof-level real-valued selector.

The precise checked claim is:

> Under explicit local response, residual, calibration, trajectory, and
> small-step certificates, an arbitrary learned online response proposal can be
> routed through a certificate-generated fallback without invalidating
> fixed-penalty stationarity.  Accepted uncertainty-adjusted value-gradient
> improvement enters the Lyapunov budget as a nonnegative favorable term, while
> persistent bounded certificate errors lead to an explicit stationarity and
> residual neighborhood rather than an unjustified zero-error limit.
