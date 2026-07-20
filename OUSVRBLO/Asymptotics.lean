import OUSVRBLO.CertifiedSafety
import OUSVRBLO.CertifiedGainDescent

open BigOperators Filter Topology
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- A nonnegative sequence with uniformly bounded partial sums has arithmetic
averages converging to zero. -/
theorem seq_average_tendsto_zero_of_bounded_partial_sums
    (a : ℕ → ℝ) (M : ℝ)
    (ha : ∀ t, 0 ≤ a t)
    (hbound : ∀ T, SeqSum T a ≤ M) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T a)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T => by
      have hsum : 0 ≤ SeqSum T a := by
        simpa [SeqSum] using Finset.sum_nonneg (fun t _ => ha t)
      exact mul_nonneg (by positivity) hsum
  · exact Filter.Eventually.of_forall fun T => by
      have hscale : 0 ≤ 1 / (T : ℝ) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left (hbound T) hscale
      simpa [div_eq_mul_inv, mul_comm] using hscaled
  · exact tendsto_const_div_atTop_nhds_zero_nat M

/-- Accumulated right-hand side of the public fallback-safe budget. -/
def CertifiedSafetySystem.accumulatedRhs
    (S : CertifiedSafetySystem) (T : ℕ) : ℝ :=
  S.Psi 0 - S.Pstar
    + S.Ceps * SeqSum T S.eps
    + S.Cb * SeqSum T S.b
    + S.Cd * SeqSum T S.d

/-- A uniform bound on the accumulated safety budget bounds stationarity partial
sums. -/
theorem CertifiedSafetySystem.gradient_partial_sums_bounded
    (S : CertifiedSafetySystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    ∀ T, SeqSum T S.Gsq ≤ 4 * M / S.eta := by
  intro T
  have hRsum : 0 ≤ SeqSum T S.R := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.R_nonneg t)
  have hRcoef : 0 ≤ S.eta * S.lam ^ 2 * S.CR / 4 := by
    positivity
  have hRterm :
      0 ≤ (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R :=
    mul_nonneg hRcoef hRsum
  have hbudget := S.cumulative_budget T
  have hupper := hM T
  have hmain : (S.eta / 4) * SeqSum T S.Gsq ≤ M := by
    dsimp [CertifiedSafetySystem.accumulatedRhs] at hupper
    nlinarith [hbudget, hRterm, hupper]
  have hscale : 0 ≤ 4 / S.eta := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain hscale
  calc
    SeqSum T S.Gsq
        = (4 / S.eta) * ((S.eta / 4) * SeqSum T S.Gsq) := by
            field_simp [ne_of_gt S.eta_pos]
    _ ≤ (4 / S.eta) * M := hscaled
    _ = 4 * M / S.eta := by ring

/-- A uniform bound on the accumulated safety budget also bounds residual
partial sums. -/
theorem CertifiedSafetySystem.residual_partial_sums_bounded
    (S : CertifiedSafetySystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    ∀ T, SeqSum T S.R ≤ 4 * M / (S.eta * S.lam ^ 2 * S.CR) := by
  intro T
  have hGsum : 0 ≤ SeqSum T S.Gsq := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gsq_nonneg t)
  have hGcoef : 0 ≤ S.eta / 4 := by positivity
  have hGterm : 0 ≤ (S.eta / 4) * SeqSum T S.Gsq :=
    mul_nonneg hGcoef hGsum
  have hbudget := S.cumulative_budget T
  have hupper := hM T
  have hmain :
      (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R ≤ M := by
    dsimp [CertifiedSafetySystem.accumulatedRhs] at hupper
    nlinarith [hbudget, hGterm, hupper]
  have hscale : 0 ≤ 4 / (S.eta * S.lam ^ 2 * S.CR) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain hscale
  calc
    SeqSum T S.R
        = (4 / (S.eta * S.lam ^ 2 * S.CR)) *
            ((S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R) := by
              field_simp [ne_of_gt S.eta_pos, ne_of_gt S.lam_pos,
                ne_of_gt S.CR_pos]
    _ ≤ (4 / (S.eta * S.lam ^ 2 * S.CR)) * M := hscaled
    _ = 4 * M / (S.eta * S.lam ^ 2 * S.CR) := by ring

/-- Under a uniformly bounded accumulated perturbation budget, the fallback-safe
average stationarity measure converges to zero. -/
theorem CertifiedSafetySystem.gradient_average_tendsto_zero
    (S : CertifiedSafetySystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.Gsq)
      atTop (𝓝 0) :=
  seq_average_tendsto_zero_of_bounded_partial_sums S.Gsq (4 * M / S.eta)
    S.Gsq_nonneg (S.gradient_partial_sums_bounded M hM)

/-- Under the same bounded-budget premise, the average response residual
converges to zero. -/
theorem CertifiedSafetySystem.residual_average_tendsto_zero
    (S : CertifiedSafetySystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.R)
      atTop (𝓝 0) :=
  seq_average_tendsto_zero_of_bounded_partial_sums S.R
    (4 * M / (S.eta * S.lam ^ 2 * S.CR))
    S.R_nonneg (S.residual_partial_sums_bounded M hM)

/-- Accumulated right-hand side of the uncertainty-adjusted certified-gain
budget. -/
def CertifiedGainStepSystem.accumulatedRhs
    (S : CertifiedGainStepSystem) (T : ℕ) : ℝ :=
  S.Psi 0 - S.Pstar
    + S.Ceps * SeqSum T S.eps
    + S.Cb * SeqSum T S.b
    + S.Cd * SeqSum T S.d

/-- Uniform boundedness of the certified-gain right-hand side bounds gradient
partial sums. -/
theorem CertifiedGainStepSystem.gradient_partial_sums_bounded
    (S : CertifiedGainStepSystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    ∀ T, SeqSum T S.Gsq ≤ 4 * M / S.eta := by
  intro T
  have hGammaSum : 0 ≤ SeqSum T S.Gamma := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gamma_nonneg t)
  have hRsum : 0 ≤ SeqSum T S.R := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.R_nonneg t)
  have hGammaCoef : 0 ≤ S.eta * S.lam ^ 2 / 2 := by positivity
  have hRcoef : 0 ≤ S.eta * S.lam ^ 2 * S.CR / 4 := by positivity
  have hGammaTerm :
      0 ≤ (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma :=
    mul_nonneg hGammaCoef hGammaSum
  have hRterm :
      0 ≤ (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R :=
    mul_nonneg hRcoef hRsum
  have hbudget := S.cumulative_budget_simple T
  have hupper := hM T
  have hmain : (S.eta / 4) * SeqSum T S.Gsq ≤ M := by
    dsimp [CertifiedGainStepSystem.accumulatedRhs] at hupper
    nlinarith [hbudget, hGammaTerm, hRterm, hupper]
  have hscale : 0 ≤ 4 / S.eta := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain hscale
  calc
    SeqSum T S.Gsq
        = (4 / S.eta) * ((S.eta / 4) * SeqSum T S.Gsq) := by
            field_simp [ne_of_gt S.eta_pos]
    _ ≤ (4 / S.eta) * M := hscaled
    _ = 4 * M / S.eta := by ring

/-- Uniform boundedness of the certified-gain right-hand side bounds response
residual partial sums. -/
theorem CertifiedGainStepSystem.residual_partial_sums_bounded
    (S : CertifiedGainStepSystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    ∀ T, SeqSum T S.R ≤ 4 * M / (S.eta * S.lam ^ 2 * S.CR) := by
  intro T
  have hGsum : 0 ≤ SeqSum T S.Gsq := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gsq_nonneg t)
  have hGammaSum : 0 ≤ SeqSum T S.Gamma := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gamma_nonneg t)
  have hGcoef : 0 ≤ S.eta / 4 := by positivity
  have hGammaCoef : 0 ≤ S.eta * S.lam ^ 2 / 2 := by positivity
  have hGterm : 0 ≤ (S.eta / 4) * SeqSum T S.Gsq :=
    mul_nonneg hGcoef hGsum
  have hGammaTerm :
      0 ≤ (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma :=
    mul_nonneg hGammaCoef hGammaSum
  have hbudget := S.cumulative_budget_simple T
  have hupper := hM T
  have hmain :
      (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R ≤ M := by
    dsimp [CertifiedGainStepSystem.accumulatedRhs] at hupper
    nlinarith [hbudget, hGterm, hGammaTerm, hupper]
  have hscale : 0 ≤ 4 / (S.eta * S.lam ^ 2 * S.CR) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain hscale
  calc
    SeqSum T S.R
        = (4 / (S.eta * S.lam ^ 2 * S.CR)) *
            ((S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R) := by
              field_simp [ne_of_gt S.eta_pos, ne_of_gt S.lam_pos,
                ne_of_gt S.CR_pos]
    _ ≤ (4 / (S.eta * S.lam ^ 2 * S.CR)) * M := hscaled
    _ = 4 * M / (S.eta * S.lam ^ 2 * S.CR) := by ring

/-- The same bounded right-hand side also bounds cumulative certified gain. -/
theorem CertifiedGainStepSystem.gain_partial_sums_bounded
    (S : CertifiedGainStepSystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    ∀ T, SeqSum T S.Gamma ≤ 2 * M / (S.eta * S.lam ^ 2) := by
  intro T
  have hGsum : 0 ≤ SeqSum T S.Gsq := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gsq_nonneg t)
  have hRsum : 0 ≤ SeqSum T S.R := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.R_nonneg t)
  have hGcoef : 0 ≤ S.eta / 4 := by positivity
  have hRcoef : 0 ≤ S.eta * S.lam ^ 2 * S.CR / 4 := by positivity
  have hGterm : 0 ≤ (S.eta / 4) * SeqSum T S.Gsq :=
    mul_nonneg hGcoef hGsum
  have hRterm :
      0 ≤ (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R :=
    mul_nonneg hRcoef hRsum
  have hbudget := S.cumulative_budget_simple T
  have hupper := hM T
  have hmain :
      (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma ≤ M := by
    dsimp [CertifiedGainStepSystem.accumulatedRhs] at hupper
    nlinarith [hbudget, hGterm, hRterm, hupper]
  have hscale : 0 ≤ 2 / (S.eta * S.lam ^ 2) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain hscale
  calc
    SeqSum T S.Gamma
        = (2 / (S.eta * S.lam ^ 2)) *
            ((S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma) := by
              field_simp [ne_of_gt S.eta_pos, ne_of_gt S.lam_pos]
    _ ≤ (2 / (S.eta * S.lam ^ 2)) * M := hscaled
    _ = 2 * M / (S.eta * S.lam ^ 2) := by ring

/-- Average stationarity converges to zero for the certified-gain system under a
uniformly bounded accumulated perturbation budget. -/
theorem CertifiedGainStepSystem.gradient_average_tendsto_zero
    (S : CertifiedGainStepSystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.Gsq)
      atTop (𝓝 0) :=
  seq_average_tendsto_zero_of_bounded_partial_sums S.Gsq (4 * M / S.eta)
    S.Gsq_nonneg (S.gradient_partial_sums_bounded M hM)

/-- Average response residual converges to zero for the certified-gain system. -/
theorem CertifiedGainStepSystem.residual_average_tendsto_zero
    (S : CertifiedGainStepSystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.R)
      atTop (𝓝 0) :=
  seq_average_tendsto_zero_of_bounded_partial_sums S.R
    (4 * M / (S.eta * S.lam ^ 2 * S.CR))
    S.R_nonneg (S.residual_partial_sums_bounded M hM)

/-- The average nonnegative certified gain also converges to zero when the
Lyapunov right-hand side is uniformly bounded. -/
theorem CertifiedGainStepSystem.gain_average_tendsto_zero
    (S : CertifiedGainStepSystem) (M : ℝ)
    (hM : ∀ T, S.accumulatedRhs T ≤ M) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.Gamma)
      atTop (𝓝 0) :=
  seq_average_tendsto_zero_of_bounded_partial_sums S.Gamma
    (2 * M / (S.eta * S.lam ^ 2))
    S.Gamma_nonneg (S.gain_partial_sums_bounded M hM)

end

end OUSVRBLO
