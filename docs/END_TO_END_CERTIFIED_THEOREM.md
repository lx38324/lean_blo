# End-to-end certified online value-anchor theorem

This note states the highest-level theorem-facing API in the repository. The
claim concerns a restricted/local value-function fixed-penalty surrogate. It
preserves the machine-learning interpretation that a learned updater may propose
an arbitrary online response, while the proof depends only on certificates for
the response actually accepted by the algorithm.

## 1. Residual safeguard certificate

Let `R_t` be the current response residual, `R_t^B` the certifiable base-response
residual, and `R_t^O` the accepted-response residual. Assume

$$
R_t^B\le (1-\theta)R_t+\varepsilon_t^B,
$$

and

$$
R_t^O\le R_t^B+\tau_t^R.
$$

Define

$$
Q_t:=R_t^B+\tau_t^R,
\qquad
\varepsilon_t:=\varepsilon_t^B+\tau_t^R.
$$

Then

$$
R_t^B\le Q_t,
\qquad
R_t^O\le Q_t,
\qquad
Q_t\le(1-\theta)R_t+\varepsilon_t.
$$

This closure is represented by `ResidualSafeguardSystem`.

## 2. Sequence-level calibrated gain certificate

Let `e_t^B` and `e_t^O` be the true value-gradient approximation errors of the
base and accepted responses. Assume asymmetric proxy calibration

$$
|\widehat e_t^O-e_t^O|\le\rho_t^O,
\qquad
|\widehat e_t^B-e_t^B|\le\rho_t^B,
$$

and proxy acceptance

$$
\widehat e_t^O
\le
\widehat e_t^B-\widehat\Delta_t+\tau_t^e.
$$

Define the uncertainty-adjusted gain

$$
\Gamma_t
:=
\widehat\Delta_t-\tau_t^e-\rho_t^O-\rho_t^B.
$$

The certified-gain branch requires `Gamma_t >= 0`. If the condition fails, the
theorem-facing enhanced certificate falls back to the base response and uses
`Gamma_t = 0`. Lean proves

$$
e_t^O\le e_t^B-\Gamma_t.
$$

If

$$
e_t^B\le C_RQ_t+b_t,
$$

then

$$
\boxed{
 e_t^O\le C_RQ_t+b_t-\Gamma_t.
}
$$

If the actual inexact-gradient vector satisfies

$$
\|E_t\|^2\le\lambda^2e_t^O,
$$

then the sequence-level certificate produces

$$
\boxed{
\|E_t\|^2
\le
\lambda^2(C_RQ_t+b_t-\Gamma_t).
}
$$

These statements are implemented by `ProxyGainSequence` and
`ProxyResidualCertificate` in `OUSVRBLO/ProxySequenceCertificate.lean`.

## 3. Analytic premises

The end-to-end structure stores the local surrogate smoothness inequality

$$
P_{t+1}
\le
P_t-\eta\langle G_t,G_t+E_t\rangle
+\frac{L_P\eta^2}{2}\|G_t+E_t\|^2,
$$

with

$$
L_P\eta\le1.
$$

For the response residual it stores the local smoothness inequality

$$
R_{t+1}
\le
Q_t+\langle\nabla R_t,\Delta x_t\rangle
+\frac{L_R}{2}\|\Delta x_t\|^2+d_t,
$$

along with

$$
\|\nabla R_t\|^2\le C_RQ_t+b_t,
$$

$$
H_t^2=C_RQ_t+b_t,
\qquad H_t\ge0,
$$

$$
\|\Delta x_t\|\le\eta s_t,
$$

and

$$
s_t^2\le2\|G_t\|^2+2\|E_t\|^2.
$$

Cauchy--Schwarz, Young's inequality, and the certified error bound then produce

$$
\begin{aligned}
R_{t+1}
\le{}&(1+C_R\beta)Q_t
+2A_\eta\|G_t\|^2
+\beta b_t
\\
&-2A_\eta\lambda^2\Gamma_t+d_t.
\end{aligned}
$$

## 4. Parameter package

For `mu > 0`, define

$$
A_\eta=\frac{\eta\mu}{2}+\frac{L_R\eta^2}{2},
\qquad
\beta=2A_\eta\lambda^2+\frac{\eta}{2\mu}.
$$

The manuscript choice

$$
\mu=\frac{1}{\sqrt2\lambda}
$$

gives

$$
A_\eta
=
\frac{\eta}{2\sqrt2\lambda}
+
\frac{L_R\eta^2}{2},
$$

and

$$
\beta_\eta
=
\sqrt2\lambda\eta+\lambda^2L_R\eta^2.
$$

Assume

$$
C_R\beta\le\frac\theta4,
\qquad
0<\theta\le1,
$$

and set

$$
\alpha=\frac{\eta\lambda^2C_R}{\theta}.
$$

Lean derives all final Lyapunov coefficient inequalities from these premises.
They are not independent fields of the end-to-end system.

## 5. Exact finite-horizon theorem

Define

$$
\Psi_t=P_t+\alpha R_t,
$$

and

$$
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2.
$$

Then

$$
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac34\eta\lambda^2,
$$

and for every finite horizon `T`,

$$
\boxed{
\begin{aligned}
&\frac\eta4\sum_{t<T}\|G_t\|^2
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

The conventional simplified version replaces `C_Gamma` by its checked lower
bound `eta * lambda^2 / 2`.

Lean declarations:

- `EndToEndCertifiedGainSystem.certified_error_bound`;
- `EndToEndCertifiedGainSystem.toSmoothResidualAnalyticGainSystem`;
- `EndToEndCertifiedGainSystem.toCertifiedGainStepSystem`;
- `EndToEndCertifiedGainSystem.cumulative_budget`;
- `EndToEndCertifiedGainSystem.cumulative_budget_simple`.

## 6. Same-iterate and pointwise consequences

The favorable gain term is not an error quantity, so the same-iterate
performance measure is

$$
\|G_t\|^2+\lambda^2C_RR_t.
$$

For every `T > 0`, Lean obtains

$$
\boxed{
\exists t<T:\quad
\|G_t\|^2+\lambda^2C_RR_t
\le
\frac{4\mathcal B_T}{\eta T},
}
$$

where `B_T` is the accumulated right-hand-side budget.

If the nonnegative sequences `epsBase`, `tau`, `b`, and `d` are summable, then

$$
\varepsilon_t=\varepsilon_t^B+\tau_t^R
$$

is summable, and the same-iterate rate becomes

$$
\exists t<T:\quad
\|G_t\|^2+\lambda^2C_RR_t
\le
\frac{4\mathcal B_\infty}{\eta T}.
$$

The same assumptions imply

$$
\|G_t\|^2\to0,
\qquad
R_t\to0,
\qquad
\Gamma_t\to0.
$$

The last limit is a finite-budget consequence for a nonnegative favorable term;
it does not make small gain a performance objective.

Lean declarations in `OUSVRBLO/EndToEndCorollaries.lean`:

- `ResidualSafeguardSystem.eps_summable`;
- `EndToEndCertifiedGainSystem.exists_joint_certificate`;
- `EndToEndCertifiedGainSystem.exists_joint_certificate_of_summable`;
- `EndToEndCertifiedGainSystem.gradient_tendsto_zero_of_summable`;
- `EndToEndCertifiedGainSystem.residual_tendsto_zero_of_summable`;
- `EndToEndCertifiedGainSystem.gain_tendsto_zero_of_summable`.

## 7. Claim boundary

The theorem is an interface theorem for a restricted/local fixed-penalty value
surrogate. It does not prove that a concrete LLM/LoRA system automatically
satisfies the stated smoothness, response regularity, residual-gradient,
contraction, or proxy-calibration premises. It also does not prove global
nonconvex lower optimality, original BLO KKT convergence, projected/stochastic
main-variable correctness, or convergence of the iterates to a unique point.
