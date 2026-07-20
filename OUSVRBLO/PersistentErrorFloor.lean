import OUSVRBLO.JointCertificates
import OUSVRBLO.TrajectoryCertifiedProposalGain

open BigOperators
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/-- Weighted one-round perturbation in the certified-gain Lyapunov budget. -/
def CertifiedGainStepSystem.weightedPerturbation
    (S : CertifiedGainStepSystem) (t : ℕ) : ℝ :=
  S.Ceps * S.eps t + S.Cb * S.b t + S.Cd * S.d t

/-- The weighted perturbation is nonnegative. -/
theorem CertifiedGainStepSystem.weightedPerturbation_nonneg
    (S : CertifiedGainStepSystem) (t : ℕ) :
    0 ≤ S.weightedPerturbation t := by
  have hCeps : 0 ≤ S.Ceps := by
    simpa [CertifiedGainStepSystem.Ceps] using
      S.toSafetyParameters.Ceps_nonneg
  have hCb : 0 ≤ S.Cb := by
    simpa [CertifiedGainStepSystem.Cb] using
      S.toSafetyParameters.Cb_nonneg
  have hCd : 0 ≤ S.Cd := by
    simpa [CertifiedGainStepSystem.Cd] using
      S.toSafetyParameters.Cd_nonneg
  exact add_nonneg
    (add_nonneg (mul_nonneg hCeps (S.eps_nonneg t))
      (mul_nonneg hCb (S.b_nonneg t)))
    (mul_nonneg hCd (S.d_nonneg t))

/-- A uniform one-round perturbation bound yields linear growth of the
accumulated right-hand side. -/
theorem CertifiedGainStepSystem.accumulatedRhs_le_gap_add_error_floor
    (S : CertifiedGainStepSystem) (floor : ℝ)
    (hfloor : ∀ t, S.weightedPerturbation t ≤ floor)
    (T : ℕ) :
    S.accumulatedRhs T ≤
      S.Psi 0 - S.Pstar + (T : ℝ) * floor := by
  have hsum :
      SeqSum T S.weightedPerturbation ≤
        SeqSum T (fun _ => floor) := by
    apply Finset.sum_le_sum
    intro t ht
    exact hfloor t
  have hexpand :
      SeqSum T S.weightedPerturbation =
        S.Ceps * SeqSum T S.eps
          + S.Cb * SeqSum T S.b
          + S.Cd * SeqSum T S.d := by
    simp only [CertifiedGainStepSystem.weightedPerturbation, SeqSum,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hconst : SeqSum T (fun _ => floor) = (T : ℝ) * floor := by
    simp [SeqSum]
  rw [hexpand, hconst] at hsum
  dsimp [CertifiedGainStepSystem.accumulatedRhs]
  linarith

/-- Persistent bounded perturbations yield a finite joint
stationarity/residual average neighborhood. -/
theorem CertifiedGainStepSystem.joint_average_bound_of_error_floor
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T)
    (floor : ℝ)
    (hfloor : ∀ t, S.weightedPerturbation t ≤ floor) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + 4 * floor / S.eta := by
  have hbase := S.joint_average_bound hT
  have hrhs := S.accumulatedRhs_le_gap_add_error_floor floor hfloor T
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) :=
    le_of_lt (div_pos (by norm_num) hden)
  have hscaled := mul_le_mul_of_nonneg_left hrhs hscale
  calc
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure
        ≤ 4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := hbase
    _ ≤ 4 * (S.Psi 0 - S.Pstar + (T : ℝ) * floor) /
          (S.eta * (T : ℝ)) := by
        simpa [div_eq_mul_inv, mul_assoc] using hscaled
    _ = 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + 4 * floor / S.eta := by
        field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]
        ring

/-- Some iterate on the same horizon satisfies the same neighborhood bound. -/
theorem CertifiedGainStepSystem.exists_joint_certificate_of_error_floor
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T)
    (floor : ℝ)
    (hfloor : ∀ t, S.weightedPerturbation t ≤ floor) :
    ∃ t < T,
      S.Gsq t + S.lam ^ 2 * S.CR * S.R t ≤
        4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + 4 * floor / S.eta := by
  exact exists_le_of_seq_average_le hT S.jointMeasure _
    (S.joint_average_bound_of_error_floor hT floor hfloor)

/-- Separate uniform bounds on the three perturbations supply the weighted
one-round bound used by the error-floor theorem. -/
theorem CertifiedGainStepSystem.weightedPerturbation_le_of_uniform_bounds
    (S : CertifiedGainStepSystem)
    (epsBar bBar dBar : ℝ)
    (heps : ∀ t, S.eps t ≤ epsBar)
    (hb : ∀ t, S.b t ≤ bBar)
    (hd : ∀ t, S.d t ≤ dBar)
    (t : ℕ) :
    S.weightedPerturbation t ≤
      S.Ceps * epsBar + S.Cb * bBar + S.Cd * dBar := by
  have hCeps : 0 ≤ S.Ceps := by
    simpa [CertifiedGainStepSystem.Ceps] using
      S.toSafetyParameters.Ceps_nonneg
  have hCb : 0 ≤ S.Cb := by
    simpa [CertifiedGainStepSystem.Cb] using
      S.toSafetyParameters.Cb_nonneg
  have hCd : 0 ≤ S.Cd := by
    simpa [CertifiedGainStepSystem.Cd] using
      S.toSafetyParameters.Cd_nonneg
  have heps' := mul_le_mul_of_nonneg_left (heps t) hCeps
  have hb' := mul_le_mul_of_nonneg_left (hb t) hCb
  have hd' := mul_le_mul_of_nonneg_left (hd t) hCd
  dsimp [CertifiedGainStepSystem.weightedPerturbation]
  linarith

/-- Trajectory-facing same-iterate neighborhood theorem. -/
theorem TrajectoryCertifiedProposalGainSystem.exists_joint_certificate_of_error_floor
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    {T : ℕ} (hT : 0 < T) (floor : ℝ)
    (hfloor : ∀ t,
      S.toCertifiedGainStepSystem.weightedPerturbation t ≤ floor) :
    ∃ t < T,
      ‖S.G t‖ ^ 2 +
          S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t ≤
        4 * (S.toCertifiedGainStepSystem.Psi 0 - S.Pstar) /
            (S.driftParameters.eta * (T : ℝ))
          + 4 * floor / S.driftParameters.eta := by
  change ∃ t < T,
    S.toCertifiedGainStepSystem.Gsq t +
        S.toCertifiedGainStepSystem.lam ^ 2 *
          S.toCertifiedGainStepSystem.CR *
          S.toCertifiedGainStepSystem.R t ≤
      4 * (S.toCertifiedGainStepSystem.Psi 0 -
        S.toCertifiedGainStepSystem.Pstar) /
          (S.toCertifiedGainStepSystem.eta * (T : ℝ))
        + 4 * floor / S.toCertifiedGainStepSystem.eta
  exact S.toCertifiedGainStepSystem.exists_joint_certificate_of_error_floor
    hT floor hfloor

end

end OUSVRBLO
