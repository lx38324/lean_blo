import OUSVRBLO.JointCertificates
import OUSVRBLO.TrajectoryGradientSemantics

open BigOperators
open scoped BigOperators InnerProductSpace Gradient

namespace OUSVRBLO

noncomputable section

/-- The finite-horizon right-hand side after retaining, rather than dropping,
the exact accumulated certified gain. -/
def CertifiedGainStepSystem.gainAdjustedRhs
    (S : CertifiedGainStepSystem) (T : ℕ) : ℝ :=
  S.accumulatedRhs T - S.Cgain * SeqSum T S.Gamma

/-- The exact certified-gain coefficient is strictly positive. -/
theorem CertifiedGainStepSystem.gain_coefficient_pos
    (S : CertifiedGainStepSystem) :
    0 < S.Cgain := by
  have hlamSq : 0 < S.lam ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt S.lam_pos)
  have hbase : 0 < S.eta * S.lam ^ 2 / 2 :=
    div_pos (mul_pos S.eta_pos hlamSq) (by norm_num)
  exact lt_of_lt_of_le hbase S.Cgain_lower

/-- The scaled joint stationarity/residual sum is bounded by the Lyapunov budget
minus the exact accumulated certified gain. -/
theorem CertifiedGainStepSystem.joint_scaled_sum_le_gainAdjustedRhs
    (S : CertifiedGainStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.jointMeasure ≤ S.gainAdjustedRhs T := by
  have hbudget :
      (S.eta / 4) * SeqSum T S.Gsq
        + S.Cgain * SeqSum T S.Gamma
        + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
        ≤ S.accumulatedRhs T := by
    simpa [CertifiedGainStepSystem.accumulatedRhs] using S.cumulative_budget T
  have hjoint :
      (S.eta / 4) * SeqSum T S.jointMeasure =
        (S.eta / 4) * SeqSum T S.Gsq
          + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R := by
    simp only [CertifiedGainStepSystem.jointMeasure, SeqSum,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    ring
  rw [hjoint]
  dsimp [CertifiedGainStepSystem.gainAdjustedRhs]
  linarith

/-- The gain-adjusted right-hand side is automatically nonnegative, since it
upper-bounds a nonnegative joint stationarity/residual quantity. -/
theorem CertifiedGainStepSystem.gainAdjustedRhs_nonneg
    (S : CertifiedGainStepSystem) (T : ℕ) :
    0 ≤ S.gainAdjustedRhs T := by
  have hsum : 0 ≤ SeqSum T S.jointMeasure := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => by
      exact add_nonneg (S.Gsq_nonneg t)
        (mul_nonneg
          (mul_nonneg (sq_nonneg S.lam) (le_of_lt S.CR_pos))
          (S.R_nonneg t)))
  have hcoef : 0 ≤ S.eta / 4 :=
    div_nonneg (le_of_lt S.eta_pos) (by norm_num)
  have hleft : 0 ≤ (S.eta / 4) * SeqSum T S.jointMeasure :=
    mul_nonneg hcoef hsum
  exact hleft.trans (S.joint_scaled_sum_le_gainAdjustedRhs T)

/-- Retaining certified gain never weakens the safety-only numerator. -/
theorem CertifiedGainStepSystem.gainAdjustedRhs_le_accumulatedRhs
    (S : CertifiedGainStepSystem) (T : ℕ) :
    S.gainAdjustedRhs T ≤ S.accumulatedRhs T := by
  have hsum : 0 ≤ SeqSum T S.Gamma := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gamma_nonneg t)
  have hgain : 0 ≤ S.Cgain * SeqSum T S.Gamma :=
    mul_nonneg S.gain_coefficient_pos.le hsum
  dsimp [CertifiedGainStepSystem.gainAdjustedRhs]
  linarith

/-- The gain-adjusted numerator is strictly smaller exactly when a positive
amount of certified gain has accumulated on the horizon. -/
theorem CertifiedGainStepSystem.gainAdjustedRhs_lt_accumulatedRhs_of_positive_gain
    (S : CertifiedGainStepSystem) (T : ℕ)
    (hgainSum : 0 < SeqSum T S.Gamma) :
    S.gainAdjustedRhs T < S.accumulatedRhs T := by
  have hgain : 0 < S.Cgain * SeqSum T S.Gamma :=
    mul_pos S.gain_coefficient_pos hgainSum
  dsimp [CertifiedGainStepSystem.gainAdjustedRhs]
  linarith

/-- Gain-adjusted average performance bound. Relative to the safety-only
bound, positive accumulated certified gain tightens the numerator by
`Cgain * sum Gamma`. -/
theorem CertifiedGainStepSystem.joint_average_bound_with_gain
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by
  have hbase := S.joint_scaled_sum_le_gainAdjustedRhs T
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) :=
    le_of_lt (div_pos (by norm_num) hden)
  have hscaled := mul_le_mul_of_nonneg_left hbase hscale
  calc
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure
        = (4 / (S.eta * (T : ℝ))) *
            ((S.eta / 4) * SeqSum T S.jointMeasure) := by
              field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]
    _ ≤ (4 / (S.eta * (T : ℝ))) * S.gainAdjustedRhs T := hscaled
    _ = 4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by ring

/-- Some iterate on the horizon satisfies the gain-adjusted joint certificate. -/
theorem CertifiedGainStepSystem.exists_joint_certificate_with_gain
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t + S.lam ^ 2 * S.CR * S.R t ≤
        4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by
  exact exists_le_of_seq_average_le hT S.jointMeasure _
    (S.joint_average_bound_with_gain hT)

/-- Trajectory-facing gain-adjusted same-iterate certificate. -/
theorem TrajectoryCertifiedProposalGainSystem.exists_joint_certificate_with_gain
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖S.G t‖ ^ 2 + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t ≤
        4 * S.toCertifiedGainStepSystem.gainAdjustedRhs T /
          (S.driftParameters.eta * (T : ℝ)) := by
  change ∃ t < T,
    S.toCertifiedGainStepSystem.Gsq t
        + S.toCertifiedGainStepSystem.lam ^ 2
          * S.toCertifiedGainStepSystem.CR * S.toCertifiedGainStepSystem.R t ≤
      4 * S.toCertifiedGainStepSystem.gainAdjustedRhs T /
        (S.toCertifiedGainStepSystem.eta * (T : ℝ))
  exact S.toCertifiedGainStepSystem.exists_joint_certificate_with_gain hT

/-- Gain-adjusted same-iterate certificate written with the actual objective
gradient. -/
theorem TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_joint_certificate_with_gain
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖gradient S.objective (S.z t)‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t ≤
        4 * S.toCertifiedGainStepSystem.gainAdjustedRhs T /
          (S.driftParameters.eta * (T : ℝ)) := by
  obtain ⟨t, ht, hcert⟩ := S.exists_joint_certificate_with_gain hT
  refine ⟨t, ht, ?_⟩
  rw [C.gradient_eq t]
  exact hcert

end

end OUSVRBLO
