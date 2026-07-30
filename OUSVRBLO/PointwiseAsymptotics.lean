import OUSVRBLO.SummableCorollaries
import Mathlib.Topology.Algebra.InfiniteSum.Real

open BigOperators Filter Topology
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- Summable perturbations make the fallback-safe stationarity measure summable. -/
theorem CertifiedSafetySystem.gradient_summable_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Summable S.Gsq := by
  apply summable_of_sum_range_le S.Gsq_nonneg
  intro T
  have hbound := S.gradient_partial_sums_bounded S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd) T
  simpa [SeqSum] using hbound

/-- Summable perturbations make the fallback-safe response residual summable. -/
theorem CertifiedSafetySystem.residual_summable_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Summable S.R := by
  apply summable_of_sum_range_le S.R_nonneg
  intro T
  have hbound := S.residual_partial_sums_bounded S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd) T
  simpa [SeqSum] using hbound

/-- The squared stationarity measure converges pointwise to zero. -/
theorem CertifiedSafetySystem.gradient_tendsto_zero_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.Gsq atTop (𝓝 0) :=
  (S.gradient_summable_of_summable heps hb hd).tendsto_atTop_zero

/-- The response residual converges pointwise to zero. -/
theorem CertifiedSafetySystem.residual_tendsto_zero_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.R atTop (𝓝 0) :=
  (S.residual_summable_of_summable heps hb hd).tendsto_atTop_zero

/-- Summable perturbations make the gain-system stationarity measure summable. -/
theorem CertifiedGainStepSystem.gradient_summable_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Summable S.Gsq := by
  apply summable_of_sum_range_le S.Gsq_nonneg
  intro T
  have hbound := S.gradient_partial_sums_bounded S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd) T
  simpa [SeqSum] using hbound

/-- Summable perturbations make the gain-system residual summable. -/
theorem CertifiedGainStepSystem.residual_summable_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Summable S.R := by
  apply summable_of_sum_range_le S.R_nonneg
  intro T
  have hbound := S.residual_partial_sums_bounded S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd) T
  simpa [SeqSum] using hbound

/-- The nonnegative certified-gain sequence is summable under the same budget. -/
theorem CertifiedGainStepSystem.gain_summable_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Summable S.Gamma := by
  apply summable_of_sum_range_le S.Gamma_nonneg
  intro T
  have hbound := S.gain_partial_sums_bounded S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd) T
  simpa [SeqSum] using hbound

/-- Pointwise stationarity convergence for the certified-gain theorem. -/
theorem CertifiedGainStepSystem.gradient_tendsto_zero_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.Gsq atTop (𝓝 0) :=
  (S.gradient_summable_of_summable heps hb hd).tendsto_atTop_zero

/-- Pointwise residual convergence for the certified-gain theorem. -/
theorem CertifiedGainStepSystem.residual_tendsto_zero_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.R atTop (𝓝 0) :=
  (S.residual_summable_of_summable heps hb hd).tendsto_atTop_zero

/--
The per-round uncertainty-adjusted gain must vanish when its cumulative
nonnegative budget is finite. This is a budget consequence, not a statement that
small gain is a performance objective.
-/
theorem CertifiedGainStepSystem.gain_tendsto_zero_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.Gamma atTop (𝓝 0) :=
  (S.gain_summable_of_summable heps hb hd).tendsto_atTop_zero

end

end OUSVRBLO
