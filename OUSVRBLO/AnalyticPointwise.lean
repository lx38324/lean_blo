import OUSVRBLO.PointwiseAsymptotics
import OUSVRBLO.AnalyticClosure
import OUSVRBLO.AnalyticGainClosure
import Mathlib.Analysis.Real.Sqrt

open Filter Topology

namespace OUSVRBLO

noncomputable section

/-- Convergence of squared norms to zero implies convergence of the norms. -/
theorem tendsto_norm_zero_of_tendsto_norm_sq_zero
    {E : Type*} [NormedAddCommGroup E]
    (g : ℕ → E)
    (h : Tendsto (fun t => ‖g t‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun t => ‖g t‖) atTop (𝓝 0) := by
  have hsqrt :
      Tendsto (fun t => Real.sqrt (‖g t‖ ^ 2)) atTop
        (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- Under summable perturbations, the analytic safety gradient norm vanishes. -/
theorem AnalyticSafetySystem.gradient_norm_tendsto_zero_of_summable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticSafetySystem E)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun t => ‖S.G t‖) atTop (𝓝 0) := by
  apply tendsto_norm_zero_of_tendsto_norm_sq_zero S.G
  simpa [AnalyticSafetySystem.toCertifiedSafetySystem] using
    S.toCertifiedSafetySystem.gradient_tendsto_zero_of_summable heps hb hd

/-- Under summable perturbations, the analytic safety response residual vanishes. -/
theorem AnalyticSafetySystem.residual_tendsto_zero_of_summable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticSafetySystem E)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.R atTop (𝓝 0) := by
  simpa [AnalyticSafetySystem.toCertifiedSafetySystem] using
    S.toCertifiedSafetySystem.residual_tendsto_zero_of_summable heps hb hd

/-- Under summable perturbations, the analytic gain-system gradient norm vanishes. -/
theorem AnalyticGainSystem.gradient_norm_tendsto_zero_of_summable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun t => ‖S.G t‖) atTop (𝓝 0) := by
  apply tendsto_norm_zero_of_tendsto_norm_sq_zero S.G
  simpa [AnalyticGainSystem.toCertifiedGainStepSystem] using
    S.toCertifiedGainStepSystem.gradient_tendsto_zero_of_summable heps hb hd

/-- Pointwise response-residual convergence for the analytic gain system. -/
theorem AnalyticGainSystem.residual_tendsto_zero_of_summable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.R atTop (𝓝 0) := by
  simpa [AnalyticGainSystem.toCertifiedGainStepSystem] using
    S.toCertifiedGainStepSystem.residual_tendsto_zero_of_summable heps hb hd

/-- The per-round analytic certified gain vanishes as a finite-budget consequence. -/
theorem AnalyticGainSystem.gain_tendsto_zero_of_summable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.Gamma atTop (𝓝 0) := by
  simpa [AnalyticGainSystem.toCertifiedGainStepSystem] using
    S.toCertifiedGainStepSystem.gain_tendsto_zero_of_summable heps hb hd

end

end OUSVRBLO
