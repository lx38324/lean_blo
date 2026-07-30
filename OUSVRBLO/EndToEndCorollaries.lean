import OUSVRBLO.EndToEndCertifiedGain
import OUSVRBLO.JointCertificates
import OUSVRBLO.PointwiseAsymptotics

open BigOperators Filter Topology
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/-- Summability of the base contraction error and residual-acceptance tolerance
implies summability of the common envelope error. -/
theorem ResidualSafeguardSystem.eps_summable
    (S : ResidualSafeguardSystem)
    (hepsBase : Summable S.epsBase) (htau : Summable S.tau) :
    Summable S.eps := by
  change Summable (fun t => S.epsBase t + S.tau t)
  exact hepsBase.add htau

/-- One accepted round simultaneously has small stationarity and response
residual, directly from the end-to-end certificate system. -/
theorem EndToEndCertifiedGainSystem.exists_joint_certificate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖S.G t‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.safeguard.R t
        ≤ 4 * S.toCertifiedGainStepSystem.accumulatedRhs T /
            (S.driftParameters.eta * (T : ℝ)) := by
  simpa [EndToEndCertifiedGainSystem.toCertifiedGainStepSystem,
    EndToEndCertifiedGainSystem.toSmoothResidualAnalyticGainSystem,
    SmoothResidualAnalyticGainSystem.toAnalyticGainSystem,
    AnalyticGainSystem.toCertifiedGainStepSystem,
    AnalyticGainSystem.parameters,
    DriftParameterization.toSafetyParameters] using
    S.toCertifiedGainStepSystem.exists_joint_certificate hT

/-- Summable certificate perturbations give the same-iterate `O(1/T)`
stationarity/residual certificate. -/
theorem EndToEndCertifiedGainSystem.exists_joint_certificate_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X)
    (hepsBase : Summable S.safeguard.epsBase)
    (htau : Summable S.safeguard.tau)
    (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖S.G t‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.safeguard.R t
        ≤ 4 * S.toCertifiedGainStepSystem.summableRhs /
            (S.driftParameters.eta * (T : ℝ)) := by
  have heps : Summable S.safeguard.eps :=
    S.safeguard.eps_summable hepsBase htau
  simpa [EndToEndCertifiedGainSystem.toCertifiedGainStepSystem,
    EndToEndCertifiedGainSystem.toSmoothResidualAnalyticGainSystem,
    SmoothResidualAnalyticGainSystem.toAnalyticGainSystem,
    AnalyticGainSystem.toCertifiedGainStepSystem,
    AnalyticGainSystem.parameters,
    DriftParameterization.toSafetyParameters] using
    S.toCertifiedGainStepSystem.exists_joint_certificate_of_summable
      heps hb hd hT

/-- Pointwise squared stationarity convergence under summable end-to-end
certificate perturbations. -/
theorem EndToEndCertifiedGainSystem.gradient_tendsto_zero_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X)
    (hepsBase : Summable S.safeguard.epsBase)
    (htau : Summable S.safeguard.tau)
    (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun t => ‖S.G t‖ ^ 2) atTop (𝓝 0) := by
  have heps : Summable S.safeguard.eps :=
    S.safeguard.eps_summable hepsBase htau
  simpa [EndToEndCertifiedGainSystem.toCertifiedGainStepSystem,
    EndToEndCertifiedGainSystem.toSmoothResidualAnalyticGainSystem,
    SmoothResidualAnalyticGainSystem.toAnalyticGainSystem,
    AnalyticGainSystem.toCertifiedGainStepSystem,
    AnalyticGainSystem.parameters,
    DriftParameterization.toSafetyParameters] using
    S.toCertifiedGainStepSystem.gradient_tendsto_zero_of_summable heps hb hd

/-- Pointwise response-residual convergence under summable end-to-end
certificate perturbations. -/
theorem EndToEndCertifiedGainSystem.residual_tendsto_zero_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X)
    (hepsBase : Summable S.safeguard.epsBase)
    (htau : Summable S.safeguard.tau)
    (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.safeguard.R atTop (𝓝 0) := by
  have heps : Summable S.safeguard.eps :=
    S.safeguard.eps_summable hepsBase htau
  simpa [EndToEndCertifiedGainSystem.toCertifiedGainStepSystem,
    EndToEndCertifiedGainSystem.toSmoothResidualAnalyticGainSystem,
    SmoothResidualAnalyticGainSystem.toAnalyticGainSystem,
    AnalyticGainSystem.toCertifiedGainStepSystem,
    AnalyticGainSystem.parameters,
    DriftParameterization.toSafetyParameters] using
    S.toCertifiedGainStepSystem.residual_tendsto_zero_of_summable heps hb hd

/-- The per-round nonnegative certified gain also vanishes when the total
Lyapunov and perturbation budget is finite. -/
theorem EndToEndCertifiedGainSystem.gain_tendsto_zero_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X)
    (hepsBase : Summable S.safeguard.epsBase)
    (htau : Summable S.safeguard.tau)
    (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.proxy.Gamma atTop (𝓝 0) := by
  have heps : Summable S.safeguard.eps :=
    S.safeguard.eps_summable hepsBase htau
  simpa [EndToEndCertifiedGainSystem.toCertifiedGainStepSystem,
    EndToEndCertifiedGainSystem.toSmoothResidualAnalyticGainSystem,
    SmoothResidualAnalyticGainSystem.toAnalyticGainSystem,
    AnalyticGainSystem.toCertifiedGainStepSystem,
    AnalyticGainSystem.parameters,
    DriftParameterization.toSafetyParameters] using
    S.toCertifiedGainStepSystem.gain_tendsto_zero_of_summable heps hb hd

end

end OUSVRBLO
