# Objective-gradient semantics for the deterministic theorem

The trajectory theorem stores a descent-vector sequence `G_t` together with the
local smoothness inequality used by the Lyapunov proof. Calling the resulting
bound an objective-stationarity theorem additionally requires a
`TrajectoryGradientCertificate` identifying

$$
G_t=\nabla P(z_t).
$$

The stable vector-level finite-horizon theorem is

```text
OUSVRBLO.ICMLTheoryPackage.fallback_safe_finite_horizon
```

and the explicit objective-gradient version is

```text
OUSVRBLO.ICMLTheoryPackage.fallback_safe_objective_gradient_finite_horizon
```

The latter requires a `TrajectoryGradientCertificate` and rewrites the complete
finite-horizon budget as

$$
\begin{aligned}
&\frac{\eta}{4}\sum_{t<T}\|\nabla P(z_t)\|^2
+C_\Gamma\sum_{t<T}\Gamma_t
+\frac{\eta\lambda^2C_R}{4}\sum_{t<T}R_t
\\
&\le
\Psi_0-P_\star
+C_\varepsilon\sum_{t<T}\varepsilon_t
+C_b\sum_{t<T}b_t
+C_d\sum_{t<T}d_t.
\end{aligned}
$$

This distinction prevents an arbitrary descent vector from being silently
presented as the gradient of the represented fixed-penalty objective. The
certificate can be constructed from the component-gradient theorem for

$$
P(z)=F(z)+\lambda\bigl(h(z)-v(z)\bigr)
$$

and the checked value-gradient coupling layer.
