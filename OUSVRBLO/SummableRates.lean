import OUSVRBLO.SummableCorollaries
import OUSVRBLO.FiniteTimeCorollaries

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- Explicit `O(1 / T)` stationarity bound under summable safety perturbations. -/
theorem CertifiedSafetySystem.gradient_average_bound_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.Gsq ≤
      4 * S.summableRhs / (S.eta * (T : ℝ)) := by
  have hsum := S.gradient_partial_sums_bounded S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd) T
  have hscale : 0 ≤ 1 / (T : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hscale
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  calc
    (1 / (T : ℝ)) * SeqSum T S.Gsq
        ≤ (1 / (T : ℝ)) * (4 * S.summableRhs / S.eta) := hscaled
    _ = 4 * S.summableRhs / (S.eta * (T : ℝ)) := by
          field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]
          ring

/-- Explicit `O(1 / T)` residual bound under summable safety perturbations. -/
theorem CertifiedSafetySystem.residual_average_bound_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.R ≤
      4 * S.summableRhs /
        (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  have hsum := S.residual_partial_sums_bounded S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd) T
  have hscale : 0 ≤ 1 / (T : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hscale
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  calc
    (1 / (T : ℝ)) * SeqSum T S.R
        ≤ (1 / (T : ℝ)) *
            (4 * S.summableRhs / (S.eta * S.lam ^ 2 * S.CR)) := hscaled
    _ = 4 * S.summableRhs /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
            field_simp [ne_of_gt S.eta_pos, ne_of_gt S.lam_pos,
              ne_of_gt S.CR_pos, ne_of_gt hTreal]
            ring

/-- Best-iterate finite-time stationarity under summable safety perturbations. -/
theorem CertifiedSafetySystem.exists_stationary_iterate_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t ≤ 4 * S.summableRhs / (S.eta * (T : ℝ)) := by
  exact exists_le_of_seq_average_le hT S.Gsq _
    (S.gradient_average_bound_of_summable heps hb hd hT)

/-- Exact joint stationarity/certified-gain `O(1 / T)` rate under summable errors. -/
theorem CertifiedGainStepSystem.gradient_gain_average_bound_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.Gsq
      + 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Gamma)
      ≤ 4 * S.summableRhs / (S.eta * (T : ℝ)) := by
  have hRsum : 0 ≤ SeqSum T S.R := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.R_nonneg t)
  have hRcoef : 0 ≤ S.eta * S.lam ^ 2 * S.CR / 4 := by positivity
  have hRterm :
      0 ≤ (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R :=
    mul_nonneg hRcoef hRsum
  have hbudget := S.cumulative_budget_simple T
  have hupper := S.accumulatedRhs_le_summableRhs heps hb hd T
  have hjoint :
      (S.eta / 4) * SeqSum T S.Gsq
        + (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma
        ≤ S.summableRhs := by
    dsimp [CertifiedGainStepSystem.accumulatedRhs] at hupper
    nlinarith [hbudget, hRterm, hupper]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hjoint hscale
  calc
    (1 / (T : ℝ)) * SeqSum T S.Gsq
        + 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Gamma)
        = (4 / (S.eta * (T : ℝ))) *
            ((S.eta / 4) * SeqSum T S.Gsq
              + (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma) := by
                field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]
                ring
    _ ≤ (4 / (S.eta * (T : ℝ))) * S.summableRhs := hscaled
    _ = 4 * S.summableRhs / (S.eta * (T : ℝ)) := by ring

/-- Explicit certified-gain residual rate under summable errors. -/
theorem CertifiedGainStepSystem.residual_average_bound_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.R ≤
      4 * S.summableRhs /
        (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  have hsum := S.residual_partial_sums_bounded S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd) T
  have hscale : 0 ≤ 1 / (T : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hscale
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  calc
    (1 / (T : ℝ)) * SeqSum T S.R
        ≤ (1 / (T : ℝ)) *
            (4 * S.summableRhs / (S.eta * S.lam ^ 2 * S.CR)) := hscaled
    _ = 4 * S.summableRhs /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
            field_simp [ne_of_gt S.eta_pos, ne_of_gt S.lam_pos,
              ne_of_gt S.CR_pos, ne_of_gt hTreal]
            ring

/-- Best-iterate stationarity for the certified-gain system under summable errors. -/
theorem CertifiedGainStepSystem.exists_stationary_iterate_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t ≤ 4 * S.summableRhs / (S.eta * (T : ℝ)) := by
  have hjoint := S.gradient_gain_average_bound_of_summable heps hb hd hT
  have hGammaSum : 0 ≤ SeqSum T S.Gamma := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gamma_nonneg t)
  have hGammaAverage :
      0 ≤ 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Gamma) := by
    positivity
  have havg :
      (1 / (T : ℝ)) * SeqSum T S.Gsq ≤
        4 * S.summableRhs / (S.eta * (T : ℝ)) := by
    nlinarith
  exact exists_le_of_seq_average_le hT S.Gsq _ havg

end

end OUSVRBLO
