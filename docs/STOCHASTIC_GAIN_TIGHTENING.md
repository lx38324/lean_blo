# Stochastic expected-gain tightening

This note records the expectation-level counterpart of the deterministic
selected-trajectory gain-adjusted theorem.

For a `StochasticExpectedGainSystem`, define

$$
\mathcal B_T^{\mathrm{stoch}}
:=
\mathbb E\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\mathbb E\varepsilon_t
+C_b\sum_{t<T}\mathbb E b_t
+C_d\sum_{t<T}\mathbb E d_t
+C_\sigma\sum_{t<T}\sigma_t^2,
$$

and

$$
\mathcal B_{T,\mathrm{gain}}^{\mathrm{stoch}}
:=
\mathcal B_T^{\mathrm{stoch}}
-C_\Gamma\sum_{t<T}\mathbb E\Gamma_t.
$$

The checked stochastic finite-horizon theorem implies

$$
\frac{\eta}{4}\sum_{t<T}
\left(
\mathbb E\|G_t\|^2+\lambda^2C_R\mathbb ER_t
\right)
\le
\mathcal B_{T,\mathrm{gain}}^{\mathrm{stoch}}.
$$

Hence

$$
\frac1T\sum_{t<T}
\left(
\mathbb E\|G_t\|^2+\lambda^2C_R\mathbb ER_t
\right)
\le
\frac{4\mathcal B_{T,\mathrm{gain}}^{\mathrm{stoch}}}{\eta T},
$$

and some index on the same horizon satisfies the same upper bound.

Because $C_\Gamma>0$ and $\mathbb E\Gamma_t\ge0$, Lean verifies

$$
\mathcal B_{T,\mathrm{gain}}^{\mathrm{stoch}}
\le
\mathcal B_T^{\mathrm{stoch}},
$$

with strict inequality whenever

$$
\sum_{t<T}\mathbb E\Gamma_t>0.
$$

This is an expected selected-trajectory tightening statement. It is not a
comparison between two counterfactual stochastic trajectories.

Stable Lean declarations:

```text
OUSVRBLO.ICMLTheoryPackage.stochastic_expected_same_iterate
OUSVRBLO.ICMLTheoryPackage.stochastic_positive_gain_strictly_tightens
```

Underlying checked declarations:

```text
StochasticExpectedGainSystem.exists_joint_certificate_with_gain
StochasticExpectedGainSystem.gainAdjustedRhs_lt_accumulatedRhs_of_positive_gain
```

The claim boundary is unchanged: the stochastic layer is an expectation-level
interface theorem and does not formalize a concrete neural mini-batch filtration
or high-probability concentration result.
