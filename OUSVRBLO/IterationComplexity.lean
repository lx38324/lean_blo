import OUSVRBLO.JointCertificates
import OUSVRBLO.SummableCorollaries

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/--
Cross-multiplied horizon condition for an explicit joint
stationarity/response tolerance. This form avoids rounding choices in the
abstract theorem. For positive `eta` and `tolerance`, it is the manuscript
condition `T >= 4 * summableRhs / (eta * tolerance)`.
-/
def CertifiedSafetySystem.JointToleranceHorizon
    (S : CertifiedSafetySystem) (T : ℕ) (tolerance : ℝ) : Prop :=
  4 * S.summableRhs ≤ tolerance * S.eta * (T : ℝ)

/-- The familiar divided horizon bound implies the cross-multiplied condition. -/
theorem CertifiedSafetySystem.jointToleranceHorizon_of_div_bound
    (S : CertifiedSafetySystem) {T : ℕ} {tolerance : ℝ}
    (htolerance : 0 < tolerance)
    (horizon :
      4 * S.summableRhs / (S.eta * tolerance) ≤ (T : ℝ)) :
    S.JointToleranceHorizon T tolerance := by
  have hden : 0 < S.eta * tolerance := mul_pos S.eta_pos htolerance
  have h := (div_le_iff₀ hden).1 horizon
  simpa [CertifiedSafetySystem.JointToleranceHorizon,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- Summable perturbations plus the explicit horizon condition produce one
iterate whose joint stationarity/residual measure is at most `tolerance`. -/
theorem CertifiedSafetySystem.exists_joint_certificate_le_tolerance_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) {tolerance : ℝ}
    (horizon : S.JointToleranceHorizon T tolerance) :
    ∃ t < T,
      S.Gsq t + S.lam ^ 2 * S.CR * S.R t ≤ tolerance := by
  obtain ⟨t, ht, hcert⟩ :=
    S.exists_joint_certificate_of_summable heps hb hd hT
  refine ⟨t, ht, hcert.trans ?_⟩
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  apply (div_le_iff₀ hden).2
  simpa [CertifiedSafetySystem.JointToleranceHorizon,
    mul_comm, mul_left_comm, mul_assoc] using horizon

/-- Component form of the safety same-iterate certificate. -/
theorem CertifiedSafetySystem.exists_stationarity_and_scaled_residual_le_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) {tolerance : ℝ}
    (horizon : S.JointToleranceHorizon T tolerance) :
    ∃ t < T,
      S.Gsq t ≤ tolerance ∧
      S.R t ≤ tolerance / (S.lam ^ 2 * S.CR) := by
  obtain ⟨t, ht, hjoint⟩ :=
    S.exists_joint_certificate_le_tolerance_of_summable
      heps hb hd hT horizon
  have hlamSq : 0 < S.lam ^ 2 := by
    simpa [pow_two] using mul_pos S.lam_pos S.lam_pos
  have hcoef : 0 < S.lam ^ 2 * S.CR :=
    mul_pos hlamSq S.CR_pos
  have hresTerm : 0 ≤ S.lam ^ 2 * S.CR * S.R t :=
    mul_nonneg hcoef.le (S.R_nonneg t)
  have hG : S.Gsq t ≤ tolerance :=
    (le_add_of_nonneg_right hresTerm).trans hjoint
  have hgradTerm : 0 ≤ S.Gsq t := S.Gsq_nonneg t
  have hscaled : S.lam ^ 2 * S.CR * S.R t ≤ tolerance := by
    nlinarith
  have hR : S.R t ≤ tolerance / (S.lam ^ 2 * S.CR) := by
    apply (le_div_iff₀ hcoef).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  exact ⟨t, ht, hG, hR⟩

/-- Gain-system version of the explicit joint tolerance horizon. -/
def CertifiedGainStepSystem.JointToleranceHorizon
    (S : CertifiedGainStepSystem) (T : ℕ) (tolerance : ℝ) : Prop :=
  4 * S.summableRhs ≤ tolerance * S.eta * (T : ℝ)

/-- The familiar divided horizon bound implies the gain-system condition. -/
theorem CertifiedGainStepSystem.jointToleranceHorizon_of_div_bound
    (S : CertifiedGainStepSystem) {T : ℕ} {tolerance : ℝ}
    (htolerance : 0 < tolerance)
    (horizon :
      4 * S.summableRhs / (S.eta * tolerance) ≤ (T : ℝ)) :
    S.JointToleranceHorizon T tolerance := by
  have hden : 0 < S.eta * tolerance := mul_pos S.eta_pos htolerance
  have h := (div_le_iff₀ hden).1 horizon
  simpa [CertifiedGainStepSystem.JointToleranceHorizon,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- One iterate simultaneously has small stationarity measure and response
residual under the certified-gain theorem. -/
theorem CertifiedGainStepSystem.exists_joint_certificate_le_tolerance_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) {tolerance : ℝ}
    (horizon : S.JointToleranceHorizon T tolerance) :
    ∃ t < T,
      S.Gsq t + S.lam ^ 2 * S.CR * S.R t ≤ tolerance := by
  obtain ⟨t, ht, hcert⟩ :=
    S.exists_joint_certificate_of_summable heps hb hd hT
  refine ⟨t, ht, hcert.trans ?_⟩
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  apply (div_le_iff₀ hden).2
  simpa [CertifiedGainStepSystem.JointToleranceHorizon,
    mul_comm, mul_left_comm, mul_assoc] using horizon

/-- Component form for the gain system. The favorable gain remains in the
Lyapunov accounting and is not treated as an error tolerance. -/
theorem CertifiedGainStepSystem.exists_stationarity_and_scaled_residual_le_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) {tolerance : ℝ}
    (horizon : S.JointToleranceHorizon T tolerance) :
    ∃ t < T,
      S.Gsq t ≤ tolerance ∧
      S.R t ≤ tolerance / (S.lam ^ 2 * S.CR) := by
  obtain ⟨t, ht, hjoint⟩ :=
    S.exists_joint_certificate_le_tolerance_of_summable
      heps hb hd hT horizon
  have hlamSq : 0 < S.lam ^ 2 := by
    simpa [pow_two] using mul_pos S.lam_pos S.lam_pos
  have hcoef : 0 < S.lam ^ 2 * S.CR :=
    mul_pos hlamSq S.CR_pos
  have hresTerm : 0 ≤ S.lam ^ 2 * S.CR * S.R t :=
    mul_nonneg hcoef.le (S.R_nonneg t)
  have hG : S.Gsq t ≤ tolerance :=
    (le_add_of_nonneg_right hresTerm).trans hjoint
  have hgradTerm : 0 ≤ S.Gsq t := S.Gsq_nonneg t
  have hscaled : S.lam ^ 2 * S.CR * S.R t ≤ tolerance := by
    nlinarith
  have hR : S.R t ≤ tolerance / (S.lam ^ 2 * S.CR) := by
    apply (le_div_iff₀ hcoef).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  exact ⟨t, ht, hG, hR⟩

end

end OUSVRBLO
