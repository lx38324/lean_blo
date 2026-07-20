# Revised certified theorem and Lean map

This document states the current proof claim and maps each mathematical layer
to its Lean implementation. The theorem concerns a restricted/local
value-function fixed-penalty surrogate. It preserves the machine-learning
meaning of an arbitrary learned response proposal protected by a certifiable
fallback.

## 1. Residual certificate envelope

Let `R_t^B` be the safe-base residual and `R_t^O` the accepted-response
residual. If

$$
R_t^B \le (1-\theta)R_t+\varepsilon_t^B,
$$

and the acceptance rule guarantees

$$
R_t^O \le R_t^B+\tau_t^R,
$$

define

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

Lean file: `OUSVRBLO/SafeguardCertificate.lean`.

Main declarations:

- `ResidualSafeguardSystem.base_le_envelope`;
- `ResidualSafeguardSystem.online_le_envelope`;
- `ResidualSafeguardSystem.envelope_contract`.

## 2. Uncertainty-adjusted certified gain

Suppose the online and baseline proxy errors satisfy

$$
|\widehat e_t^O-e_t^O|\le\rho_t^O,
\qquad
|\widehat e_t^B-e_t^B|\le\rho_t^B,
$$

and the accepted proposal satisfies

$$
\widehat e_t^O
\le
\widehat e_t^B-\widehat\Delta_t+\tau_t^e.
$$

Define

$$
\Gamma_t
:=
\widehat\Delta_t-\tau_t^e-\rho_t^O-\rho_t^B.
$$

Only `Gamma_t >= 0` is accepted as a certified gain; fallback is represented by
`Gamma_t = 0`. Lean proves

$$
e_t^O\le e_t^B-\Gamma_t.
$$

Combining this with

$$
e_t^B\le C_RQ_t+b_t
$$

gives

$$
\boxed{e_t^O\le C_RQ_t+b_t-\Gamma_t.}
$$

Lean file: `OUSVRBLO/ProxyCertificate.lean`.

Main declarations:

- `CalibratedProxyGain.true_error_improves`;
- `CertifiedGainInterface.r2_certified`.

## 3. Exact manuscript parameters

For a positive Young parameter `mu`, define

$$
A_\eta
=
\frac{\eta\mu}{2}+\frac{L_R\eta^2}{2},
\qquad
\beta
=
2A_\eta\lambda^2+\frac{\eta}{2\mu}.
$$

The manuscript choice

$$
\mu=\frac{1}{\sqrt{2}\lambda}
$$

gives exactly

$$
A_\eta
=
\frac{\eta}{2\sqrt{2}\lambda}
+
\frac{L_R\eta^2}{2},
$$

and

$$
\beta_\eta
=
\sqrt{2}\lambda\eta
+
\lambda^2L_R\eta^2.
$$

Lean files:

- `OUSVRBLO/ManuscriptParameters.lean`;
- `OUSVRBLO/ParameterBounds.lean`.

The exact identities are checked by
`ManuscriptDriftParameters.parameterization_Aeta` and
`ManuscriptDriftParameters.parameterization_beta`.

Assume

$$
C_R\beta\le\frac{\theta}{4},
\qquad
0<\theta\le1,
$$

and define

$$
\alpha=\frac{\eta\lambda^2C_R}{\theta}.
$$

Lean derives, rather than assumes,

$$
2\alpha A_\eta\le\frac{\eta}{4},
$$

$$
\alpha-(1-\theta)
\left[
\frac{\eta\lambda^2C_R}{2}
+
\alpha(1+C_R\beta)
\right]
\ge
\frac{\eta\lambda^2C_R}{4},
$$

and all advertised error-coefficient bounds.

## 4. Hilbert-space inexact descent

Let `G_t` and `E_t` be vectors in a real Hilbert space. After substituting the
algorithmic update into local smoothness, assume

$$
P_{t+1}
\le
P_t-
\eta\langle G_t,G_t+E_t\rangle
+
\frac{L_P\eta^2}{2}\|G_t+E_t\|^2,
$$

with `L_P * eta <= 1`.

Lean verifies

$$
\langle G,G+E\rangle
=
\frac{1}{2}
\left(
\|G\|^2+\|G+E\|^2-\|E\|^2
\right),
$$

and derives

$$
P_{t+1}
\le
P_t-
\frac{\eta}{2}\|G_t\|^2
+
\frac{\eta}{2}\|E_t\|^2.
$$

Thus the safety error interface

$$
\|E_t\|^2\le\lambda^2(C_RQ_t+b_t)
$$

implies

$$
P_{t+1}
\le
P_t-
\frac{\eta}{2}\|G_t\|^2
+
\frac{\eta\lambda^2}{2}(C_RQ_t+b_t),
$$

while the certified interface

$$
\|E_t\|^2
\le
\lambda^2(C_RQ_t+b_t-\Gamma_t)
$$

implies

$$
P_{t+1}
\le
P_t-
\frac{\eta}{2}\|G_t\|^2
+
\frac{\eta\lambda^2}{2}(C_RQ_t+b_t)
-
\frac{\eta\lambda^2}{2}\Gamma_t.
$$

Lean file: `OUSVRBLO/InexactDescent.lean`.

## 5. Residual drift

Assume the raw compatibility inequality

$$
R_{t+1}
\le
Q_t+\eta H_ts_t
+
\frac{L_R\eta^2}{2}s_t^2+d_t,
$$

where

$$
H_t^2=C_RQ_t+b_t,
\qquad
s_t^2\le2\|G_t\|^2+2\|E_t\|^2.
$$

Young's inequality and the safety error bound yield

$$
R_{t+1}
\le
(1+C_R\beta)Q_t
+2A_\eta\|G_t\|^2
+\beta b_t+d_t.
$$

The certified error bound retains the favorable term

$$
R_{t+1}
\le
(1+C_R\beta)Q_t
+2A_\eta\|G_t\|^2
+\beta b_t
-2A_\eta\lambda^2\Gamma_t
+d_t.
$$

Lean file: `OUSVRBLO/ResidualDrift.lean`.

Main declarations:

- `young_product_with_parameter`;
- `SafeResidualDriftScalar.drift`;
- `CertifiedResidualDriftScalar.certified_drift`.

## 6. Composed analytic closure

`OUSVRBLO/AnalyticClosure.lean` stores the Hilbert-space smoothness premise,
squared error bound, raw residual compatibility, step-square bound, envelope
contraction, and small-step condition in one `AnalyticSafetySystem`. Lean checks

```text
analytic safety premises
  => scalar descent and drift
  => CertifiedSafetySystem
  => finite-horizon fallback-safe budget.
```

The principal declarations are:

- `AnalyticSafetySystem.descent_interface`;
- `AnalyticSafetySystem.drift_interface`;
- `AnalyticSafetySystem.toCertifiedSafetySystem`;
- `AnalyticSafetySystem.cumulative_budget`.

`OUSVRBLO/AnalyticGainClosure.lean` performs the same composition for the
uncertainty-adjusted gain:

- `AnalyticGainSystem.descent_interface`;
- `AnalyticGainSystem.drift_interface`;
- `AnalyticGainSystem.toCertifiedGainStepSystem`;
- `AnalyticGainSystem.cumulative_budget`;
- `AnalyticGainSystem.cumulative_budget_simple`.

Thus the public chain no longer begins by assuming already-collected one-step
descent and drift inequalities. It starts from the analytic scalar and
Hilbert-space premises used in the proof.

## 7. Fallback-safe finite-horizon theorem

Define

$$
\Psi_t=P_t+\alpha R_t.
$$

Lean checks

$$
\boxed{
\frac{\eta}{4}\sum_{t<T}Gsq_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
}
$$

Public theorem: `CertifiedSafetySystem.cumulative_budget`.

## 8. Certified-gain finite-horizon theorem

Define

$$
C_\Gamma
=
\frac{\eta\lambda^2}{2}
+2\alpha A_\eta\lambda^2.
$$

Lean checks

$$
\boxed{
\frac{\eta}{4}\sum_{t<T}Gsq_t
+
\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
+C_\Gamma\sum_{t<T}\Gamma_t
\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t,
}
$$

with

$$
\frac{\eta\lambda^2}{2}
\le C_\Gamma
\le\frac{3}{4}\eta\lambda^2.
$$

Public theorems:

- `CertifiedGainStepSystem.cumulative_budget`;
- `CertifiedGainStepSystem.cumulative_budget_simple`.

## 9. Best-iterate finite-time consequences

`OUSVRBLO/FiniteTimeCorollaries.lean` checks that every nonempty finite horizon
contains an iterate no larger than its arithmetic average. Hence some `t < T`
satisfies

$$
\begin{aligned}
Gsq_t\le&
\frac{4(\Psi_0-P_\star)}{\eta T}
+
\frac{4C_\varepsilon}{\eta T}
\sum_{s<T}\varepsilon_s
\\
&+
\frac{4C_b}{\eta T}\sum_{s<T}b_s
+
\frac{4C_d}{\eta T}\sum_{s<T}d_s.
\end{aligned}
$$

The corresponding Lean declarations are:

- `CertifiedSafetySystem.exists_stationary_iterate`;
- `CertifiedSafetySystem.exists_small_residual_iterate`;
- `CertifiedGainStepSystem.exists_stationary_iterate`;
- `CertifiedGainStepSystem.exists_small_residual_iterate`.

This is the direct finite-time epsilon-stationarity interpretation: when the
right-hand side is at most `epsilon`, one of the first `T` iterates satisfies
`Gsq_t <= epsilon`.

## 10. Bounded-budget asymptotics

`OUSVRBLO/Asymptotics.lean` checks the generic implication

$$
\left(\forall T,\ \sum_{t<T}a_t\le M\right),
\quad a_t\ge0
\quad\Longrightarrow\quad
\frac{1}{T}\sum_{t<T}a_t\longrightarrow0.
$$

If the accumulated safety right-hand side is uniformly bounded by `M`, Lean
derives

$$
\sum_{t<T}Gsq_t\le\frac{4M}{\eta},
\qquad
\sum_{t<T}R_t\le\frac{4M}{\eta\lambda^2C_R},
$$

and hence both averages converge to zero.

For the certified-gain system Lean additionally proves

$$
\sum_{t<T}\Gamma_t
\le
\frac{2M}{\eta\lambda^2},
\qquad
\frac{1}{T}\sum_{t<T}\Gamma_t\longrightarrow0.
$$

## 11. Summable-error closure

`OUSVRBLO/SummableCorollaries.lean` closes the standard manuscript premise
explicitly. If the nonnegative sequences `eps`, `b`, and `d` are summable, Lean
uses finite-sum monotonicity to prove

$$
\begin{aligned}
\operatorname{Rhs}_T
\le&
\Psi_0-P_\star
+C_\varepsilon\sum_{t=0}^{\infty}\varepsilon_t
\\
&+
C_b\sum_{t=0}^{\infty}b_t
+C_d\sum_{t=0}^{\infty}d_t.
\end{aligned}
$$

This is the uniform bound required by the previous section. Therefore Lean
directly derives:

- fallback-safe stationarity average tends to zero;
- fallback-safe residual average tends to zero;
- certified-gain stationarity average tends to zero;
- certified-gain residual average tends to zero;
- uncertainty-adjusted certified-gain average tends to zero.

The main declarations are the two
`accumulatedRhs_le_summableRhs` theorems and the five
`average_tendsto_zero_of_summable` corollaries.

## 12. Claim boundary

The theorem concerns a restricted/local value-function fixed-penalty surrogate.
The following remain explicit analytic interfaces for a concrete neural model:

1. local smoothness and lower boundedness of the concrete surrogate;
2. existence and regularity of the restricted lower response;
3. a general nonconvex Danskin/envelope theorem;
4. concrete residual-to-value-gradient error control;
5. raw residual compatibility for a stochastic training system;
6. projected or stochastic main-variable updates.

The project does not prove global nonconvex lower optimality, original BLO KKT
convergence, or convergence of the iterates to a unique point.
