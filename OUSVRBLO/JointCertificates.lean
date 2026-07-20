import OUSVRBLO.SummableRates

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- Joint stationarity-and-response measure for the fallback-safe theorem. -/
def CertifiedSafetySystem.jointMeasure
    (S : CertifiedSafetySystem) (t : ℕ) : ℝ :=
  S.Gsq t + S.lam ^ 2 * S.CR * S.R t

/-- The average of the joint safety measure separates into its two components. -/
theorem CertifiedSafetySystem.joint_average_eq
    (S : CertifiedSafetySystem) (T : ℕ) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure =
      (1 / (T : ℝ)) * SeqSum T S.Gsq
        + S.lam ^ 2 * S.CR * ((1 / (T : ℝ)) * SeqSum T S.R) := by
  simp [CertifiedSafetySystem.jointMeasure, SeqSum,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- Finite-horizon joint stationarity and response-residual average bound. -/
theorem CertifiedSafetySystem.joint_average_bound
    (S : CertifiedSafetySystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by
  have hbudget := S.cumulative_budget T
  have hbudget' :
      (S.eta / 4) * SeqSum T S.Gsq
        + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
        ≤ S.accumulatedRhs T := by
    simpa [CertifiedSafetySystem.accumulatedRhs] using hbudget
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden_pos : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) :=
    le_of_lt (div_pos (by norm_num) hden_pos)
  have hscaled := mul_le_mul_of_nonneg_left hbudget' hscale
  rw [S.joint_average_eq T]
  calc
    (1 / (T : ℝ)) * SeqSum T S.Gsq
        + S.lam ^ 2 * S.CR * ((1 / (T : ℝ)) * SeqSum T S.R)
        = (4 / (S.eta * (T : ℝ))) *
            ((S.eta / 4) * SeqSum T S.Gsq
              + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R) := by
                field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]
                ring
    _ ≤ (4 / (S.eta * (T : ℝ))) * S.accumulatedRhs T := hscaled
    _ = 4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by ring

/-- One iterate simultaneously satisfies the stationarity and residual bound. -/
theorem CertifiedSafetySystem.exists_joint_certificate
    (S : CertifiedSafetySystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t + S.lam ^ 2 * S.CR * S.R t ≤
        4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by
  exact exists_le_of_seq_average_le hT S.jointMeasure _
    (S.joint_average_bound hT)

/-- Explicit joint `O(1/T)` certificate under summable perturbations. -/
theorem CertifiedSafetySystem.exists_joint_certificate_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t + S.lam ^ 2 * S.CR * S.R t ≤
        4 * S.summableRhs / (S.eta * (T : ℝ)) := by
  have havg :
      (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
        4 * S.summableRhs / (S.eta * (T : ℝ)) := by
    have hbase := S.joint_average_bound hT
    have hRhs := S.accumulatedRhs_le_summableRhs heps hb hd T
    have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
    have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hRhs hscale
    nlinarith
  exact exists_le_of_seq_average_le hT S.jointMeasure _ havg

/-- Joint stationarity, residual, and certified-gain measure. -/
def CertifiedGainStepSystem.jointMeasure
    (S : CertifiedGainStepSystem) (t : ℕ) : ℝ :=
  S.Gsq t + 2 * S.lam ^ 2 * S.Gamma t
    + S.lam ^ 2 * S.CR * S.R t

/-- Component expansion of the gain-aware joint average. -/
theorem CertifiedGainStepSystem.joint_average_eq
    (S : CertifiedGainStepSystem) (T : ℕ) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure =
      (1 / (T : ℝ)) * SeqSum T S.Gsq
        + 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Gamma)
        + S.lam ^ 2 * S.CR * ((1 / (T : ℝ)) * SeqSum T S.R) := by
  simp [CertifiedGainStepSystem.jointMeasure, SeqSum,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- Finite-horizon joint bound retaining stationarity, gain, and residual. -/
theorem CertifiedGainStepSystem.joint_average_bound
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by
  have hbudget := S.cumulative_budget_simple T
  have hbudget' :
      (S.eta / 4) * SeqSum T S.Gsq
        + (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma
        + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
        ≤ S.accumulatedRhs T := by
    simpa [CertifiedGainStepSystem.accumulatedRhs] using hbudget
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden_pos : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) :=
    le_of_lt (div_pos (by norm_num) hden_pos)
  have hscaled := mul_le_mul_of_nonneg_left hbudget' hscale
  rw [S.joint_average_eq T]
  calc
    (1 / (T : ℝ)) * SeqSum T S.Gsq
        + 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Gamma)
        + S.lam ^ 2 * S.CR * ((1 / (T : ℝ)) * SeqSum T S.R)
        = (4 / (S.eta * (T : ℝ))) *
            ((S.eta / 4) * SeqSum T S.Gsq
              + (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma
              + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R) := by
                field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]
                ring
    _ ≤ (4 / (S.eta * (T : ℝ))) * S.accumulatedRhs T := hscaled
    _ = 4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by ring

/-- One iterate satisfies the complete gain-aware joint certificate. -/
theorem CertifiedGainStepSystem.exists_joint_certificate
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t + 2 * S.lam ^ 2 * S.Gamma t
          + S.lam ^ 2 * S.CR * S.R t ≤
        4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by
  exact exists_le_of_seq_average_le hT S.jointMeasure _
    (S.joint_average_bound hT)

/-- Complete joint `O(1/T)` certificate under summable perturbations. -/
theorem CertifiedGainStepSystem.exists_joint_certificate_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t + 2 * S.lam ^ 2 * S.Gamma t
          + S.lam ^ 2 * S.CR * S.R t ≤
        4 * S.summableRhs / (S.eta * (T : ℝ)) := by
  have havg :
      (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
        4 * S.summableRhs / (S.eta * (T : ℝ)) := by
    have hbase := S.joint_average_bound hT
    have hRhs := S.accumulatedRhs_le_summableRhs heps hb hd T
    have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
    have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hRhs hscale
    nlinarith
  exact exists_le_of_seq_average_le hT S.jointMeasure _ havg

end

end OUSVRBLO
