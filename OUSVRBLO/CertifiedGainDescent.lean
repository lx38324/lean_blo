import OUSVRBLO.ParameterBounds
import OUSVRBLO.ImprovementDescent

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/--
Public one-step system for an uncertainty-adjusted certified gain.

`Gamma t` is nonnegative and already subtracts proxy tolerance and calibration
uncertainty. Consequently it appears as a favorable term in both surrogate
descent and residual drift, with no separate positive `zeta` budget.
-/
structure CertifiedGainStepSystem extends SafetyParameters where
  Pstar : ℝ
  P : ℕ → ℝ
  R : ℕ → ℝ
  Q : ℕ → ℝ
  Gsq : ℕ → ℝ
  Gamma : ℕ → ℝ
  eps : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  Gsq_nonneg : ∀ t, 0 ≤ Gsq t
  R_nonneg : ∀ t, 0 ≤ R t
  Gamma_nonneg : ∀ t, 0 ≤ Gamma t
  eps_nonneg : ∀ t, 0 ≤ eps t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  P_lower : ∀ t, Pstar ≤ P t
  certified_descent :
    ∀ t,
      P (t + 1) ≤ P t
        - eta / 2 * Gsq t
        + eta * lam ^ 2 / 2 * (CR * Q t + b t)
        - eta * lam ^ 2 / 2 * Gamma t
  certified_drift :
    ∀ t,
      R (t + 1) ≤
        (1 + CR * beta) * Q t
          + 2 * Aeta * Gsq t
          + beta * b t
          - 2 * Aeta * lam ^ 2 * Gamma t
          + d t
  envelope_contraction :
    ∀ t, Q t ≤ (1 - theta) * R t + eps t

def CertifiedGainStepSystem.Psi
    (S : CertifiedGainStepSystem) (t : ℕ) : ℝ :=
  S.P t + S.alpha * S.R t

def CertifiedGainStepSystem.Ceps (S : CertifiedGainStepSystem) : ℝ :=
  S.toSafetyParameters.Ceps

def CertifiedGainStepSystem.Cb (S : CertifiedGainStepSystem) : ℝ :=
  S.toSafetyParameters.Cb

def CertifiedGainStepSystem.Cd (S : CertifiedGainStepSystem) : ℝ :=
  S.toSafetyParameters.Cd

def CertifiedGainStepSystem.Cgain (S : CertifiedGainStepSystem) : ℝ :=
  S.toSafetyParameters.Cgain

theorem CertifiedGainStepSystem.Psi_lower
    (S : CertifiedGainStepSystem) (t : ℕ) :
    S.Pstar ≤ S.Psi t := by
  have hR : 0 ≤ S.alpha * S.R t := by
    exact mul_nonneg S.toSafetyParameters.alpha_nonneg (S.R_nonneg t)
  dsimp [CertifiedGainStepSystem.Psi]
  nlinarith [S.P_lower t, hR]

/-- Exact gain-aware one-step Lyapunov inequality. -/
theorem CertifiedGainStepSystem.one_step_lyapunov
    (S : CertifiedGainStepSystem) (t : ℕ) :
    S.Psi (t + 1) ≤ S.Psi t
      - S.eta / 4 * S.Gsq t
      - S.eta * S.lam ^ 2 * S.CR / 4 * S.R t
      - S.Cgain * S.Gamma t
      + S.Ceps * S.eps t
      + S.Cb * S.b t
      + S.Cd * S.d t := by
  dsimp [CertifiedGainStepSystem.Psi, CertifiedGainStepSystem.Cgain,
    CertifiedGainStepSystem.Ceps, CertifiedGainStepSystem.Cb,
    CertifiedGainStepSystem.Cd, SafetyParameters.Cgain,
    SafetyParameters.Ceps, SafetyParameters.Cb, SafetyParameters.Cd]
  have hdes := S.certified_descent t
  have hdrift := S.certified_drift t
  have hcontr := S.envelope_contraction t
  have hdrift_scaled :=
    mul_le_mul_of_nonneg_left hdrift S.toSafetyParameters.alpha_nonneg
  have hcombined :
      S.P (t + 1) + S.alpha * S.R (t + 1) ≤
        S.P t
          - (S.eta / 2 - 2 * S.alpha * S.Aeta) * S.Gsq t
          + (S.eta * S.lam ^ 2 * S.CR / 2
            + S.alpha * (1 + S.CR * S.beta)) * S.Q t
          + (S.eta * S.lam ^ 2 / 2
            + S.alpha * S.beta) * S.b t
          + S.alpha * S.d t
          - (S.eta * S.lam ^ 2 / 2
            + 2 * S.alpha * S.Aeta * S.lam ^ 2) * S.Gamma t := by
    nlinarith [hdes, hdrift_scaled]
  have hcontr_scaled :=
    mul_le_mul_of_nonneg_left hcontr
      S.toSafetyParameters.envelope_coeff_nonneg
  have htwo := S.toSafetyParameters.two_alpha_Aeta_le
  have hdrop := S.toSafetyParameters.residual_drop_coeff
  have heps :
      S.eta * S.lam ^ 2 * S.CR / 2
        + S.alpha * (1 + S.CR * S.beta)
        ≤ S.eta * S.lam ^ 2 * S.CR * (3 / 4 + 1 / S.theta) := by
    simpa [CertifiedGainStepSystem.Ceps, SafetyParameters.Ceps] using
      S.toSafetyParameters.eps_coeff_bound
  have hb :
      S.eta * S.lam ^ 2 / 2 + S.alpha * S.beta
        ≤ 3 / 4 * S.eta * S.lam ^ 2 := by
    simpa [CertifiedGainStepSystem.Cb, SafetyParameters.Cb] using
      S.toSafetyParameters.b_coeff_bound
  have htwo_scaled :=
    mul_le_mul_of_nonneg_right htwo (S.Gsq_nonneg t)
  have hdrop_scaled :=
    mul_le_mul_of_nonneg_right hdrop (S.R_nonneg t)
  have heps_scaled :=
    mul_le_mul_of_nonneg_right heps (S.eps_nonneg t)
  have hb_scaled :=
    mul_le_mul_of_nonneg_right hb (S.b_nonneg t)
  ring_nf at hcombined hcontr_scaled htwo_scaled hdrop_scaled heps_scaled hb_scaled ⊢
  linarith [hcombined, hcontr_scaled, htwo_scaled, hdrop_scaled,
    heps_scaled, hb_scaled]

theorem CertifiedGainStepSystem.Cgain_lower
    (S : CertifiedGainStepSystem) :
    S.eta * S.lam ^ 2 / 2 ≤ S.Cgain := by
  exact S.toSafetyParameters.Cgain_lower

theorem CertifiedGainStepSystem.Cgain_upper
    (S : CertifiedGainStepSystem) :
    S.Cgain ≤ 3 / 4 * S.eta * S.lam ^ 2 := by
  exact S.toSafetyParameters.Cgain_upper

theorem CertifiedGainStepSystem.cumulative_budget_to_time
    (S : CertifiedGainStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + S.Cgain * SeqSum T S.Gamma
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Psi T
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d := by
  induction T with
  | zero =>
      simp [SeqSum]
  | succ T ih =>
      simp [SeqSum] at ih
      simp [SeqSum, Finset.sum_range_succ]
      have hstep := S.one_step_lyapunov T
      ring_nf at ih hstep ⊢
      nlinarith [ih, hstep]

/-- Strong finite-horizon budget retaining the exact certified-gain
coefficient. -/
theorem CertifiedGainStepSystem.cumulative_budget
    (S : CertifiedGainStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + S.Cgain * SeqSum T S.Gamma
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Pstar
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d := by
  have hbudget := S.cumulative_budget_to_time T
  have hlower := S.Psi_lower T
  nlinarith [hbudget, hlower]

/-- Conventional statement using the simpler lower coefficient
`eta * lam^2 / 2`. -/
theorem CertifiedGainStepSystem.cumulative_budget_simple
    (S : CertifiedGainStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Gamma
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Pstar
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d := by
  have hsum : 0 ≤ SeqSum T S.Gamma := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gamma_nonneg t)
  have hcoef := S.Cgain_lower
  have hscaled := mul_le_mul_of_nonneg_right hcoef hsum
  have hbudget := S.cumulative_budget T
  nlinarith [hbudget, hscaled]

/-- Reuse the existing averaged-budget algebra with zero comparison-error
sequence; all proxy uncertainty has already been subtracted inside `Gamma`. -/
def CertifiedGainStepSystem.toBudget
    (S : CertifiedGainStepSystem) (T : ℕ) : ImprovementBudget T where
  eta := S.eta
  lam := S.lam
  CR := S.CR
  Psi0 := S.Psi 0
  Pstar := S.Pstar
  Ceps := S.Ceps
  Cb := S.Cb
  Cd := S.Cd
  Czeta := 0
  Gsq := S.Gsq
  R := S.R
  Delta := S.Gamma
  eps := S.eps
  b := S.b
  d := S.d
  zeta := fun _ => 0
  eta_pos := S.eta_pos
  lam_pos := S.lam_pos
  CR_pos := S.CR_pos
  Gsq_nonneg := S.Gsq_nonneg
  R_nonneg := S.R_nonneg
  Delta_nonneg := S.Gamma_nonneg
  cumulative_budget := by
    simpa [SeqSum] using S.cumulative_budget_simple T

/-- Finite-horizon stationarity plus uncertainty-adjusted gain bound. -/
theorem CertifiedGainStepSystem.gradient_gain_average_bound
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.Gsq
      + 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Gamma)
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ)) := by
  simpa [CertifiedGainStepSystem.toBudget] using
    ImprovementBudget.gradient_improvement_average_bound hT (S.toBudget T)

theorem CertifiedGainStepSystem.residual_average_bound
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.R
      ≤ 4 * (S.Psi 0 - S.Pstar) /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  simpa [CertifiedGainStepSystem.toBudget] using
    ImprovementBudget.residual_average_bound hT (S.toBudget T)

end

end OUSVRBLO
