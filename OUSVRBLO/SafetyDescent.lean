import OUSVRBLO.LyapunovBudget
import OUSVRBLO.ScalarFacts

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/--
One-step scalar interface for the fallback-safe theorem.

The analytic estimates from the manuscript enter as hypotheses. This structure
checks the algebraic Lyapunov accounting from one-step descent and residual
drift to the finite-horizon `SafetyBudget`.
-/
structure SafetyStepSystem where
  eta : ℝ
  lam : ℝ
  CR : ℝ
  theta : ℝ
  beta : ℝ
  Aeta : ℝ
  alpha : ℝ
  Pstar : ℝ
  P : ℕ → ℝ
  R : ℕ → ℝ
  Rhat : ℕ → ℝ
  Gsq : ℕ → ℝ
  eps : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  CR_pos : 0 < CR
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  alpha_eq : alpha = eta * lam ^ 2 * CR / theta
  alpha_nonneg : 0 ≤ alpha
  Gsq_nonneg : ∀ t, 0 ≤ Gsq t
  R_nonneg : ∀ t, 0 ≤ R t
  eps_nonneg : ∀ t, 0 ≤ eps t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  P_lower : ∀ t, Pstar ≤ P t
  two_alpha_Aeta_le : 2 * alpha * Aeta ≤ eta / 4
  residual_drop_coeff :
    alpha
      - (1 - theta) *
        (eta * lam ^ 2 * CR / 2
          + alpha * (1 + CR * beta))
      ≥ eta * lam ^ 2 * CR / 4
  rhat_coeff_nonneg :
    0 ≤ eta * lam ^ 2 * CR / 2
      + alpha * (1 + CR * beta)
  eps_coeff_bound :
    eta * lam ^ 2 * CR / 2
      + alpha * (1 + CR * beta)
      ≤ eta * lam ^ 2 * CR * (3 / 4 + 1 / theta)
  b_coeff_bound :
    eta * lam ^ 2 / 2 + alpha * beta
      ≤ 3 / 4 * eta * lam ^ 2
  descent :
    ∀ t,
      P (t + 1) ≤ P t
        - eta / 2 * Gsq t
        + eta * lam ^ 2 / 2 * (CR * Rhat t + b t)
  drift :
    ∀ t,
      R (t + 1) ≤
        (1 + CR * beta) * Rhat t
          + 2 * Aeta * Gsq t
          + beta * b t
          + d t
  contraction :
    ∀ t, Rhat t ≤ (1 - theta) * R t + eps t

def SafetyStepSystem.Psi (S : SafetyStepSystem) (t : ℕ) : ℝ :=
  S.P t + S.alpha * S.R t

def SafetyStepSystem.Ceps (S : SafetyStepSystem) : ℝ :=
  S.eta * S.lam ^ 2 * S.CR * (3 / 4 + 1 / S.theta)

def SafetyStepSystem.Cb (S : SafetyStepSystem) : ℝ :=
  3 / 4 * S.eta * S.lam ^ 2

def SafetyStepSystem.Cd (S : SafetyStepSystem) : ℝ :=
  S.alpha

theorem SafetyStepSystem.Psi_lower (S : SafetyStepSystem) (t : ℕ) :
    S.Pstar ≤ S.Psi t := by
  have hR : 0 ≤ S.alpha * S.R t := by
    exact mul_nonneg S.alpha_nonneg (S.R_nonneg t)
  dsimp [SafetyStepSystem.Psi]
  nlinarith [S.P_lower t, hR]

theorem SafetyStepSystem.one_step_lyapunov
    (S : SafetyStepSystem) (t : ℕ) :
    S.Psi (t + 1) ≤ S.Psi t
      - S.eta / 4 * S.Gsq t
      - S.eta * S.lam ^ 2 * S.CR / 4 * S.R t
      + S.Ceps * S.eps t
      + S.Cb * S.b t
      + S.Cd * S.d t := by
  dsimp [SafetyStepSystem.Psi,
    SafetyStepSystem.Ceps, SafetyStepSystem.Cb, SafetyStepSystem.Cd]
  have hdes := S.descent t
  have hdrift := S.drift t
  have hcontr := S.contraction t
  have hdrift_scaled := mul_le_mul_of_nonneg_left hdrift S.alpha_nonneg
  have hcombined :
      S.P (t + 1) + S.alpha * S.R (t + 1) ≤
        S.P t
          - (S.eta / 2 - 2 * S.alpha * S.Aeta) *
            S.Gsq t
          + (S.eta * S.lam ^ 2 * S.CR / 2
            + S.alpha * (1 + S.CR * S.beta)) *
            S.Rhat t
          + (S.eta * S.lam ^ 2 / 2
            + S.alpha * S.beta) *
            S.b t
          + S.alpha * S.d t := by
    nlinarith [hdes, hdrift_scaled]
  have hcontr_scaled := mul_le_mul_of_nonneg_left hcontr S.rhat_coeff_nonneg
  have htwo := S.two_alpha_Aeta_le
  have hdrop := S.residual_drop_coeff
  have heps := S.eps_coeff_bound
  have hb := S.b_coeff_bound
  have htwo_scaled := mul_le_mul_of_nonneg_right htwo (S.Gsq_nonneg t)
  have hdrop_scaled := mul_le_mul_of_nonneg_right hdrop (S.R_nonneg t)
  have heps_scaled := mul_le_mul_of_nonneg_right heps (S.eps_nonneg t)
  have hb_scaled := mul_le_mul_of_nonneg_right hb (S.b_nonneg t)
  ring_nf at hcombined hcontr_scaled htwo_scaled hdrop_scaled heps_scaled hb_scaled ⊢
  nlinarith [hcombined, hcontr_scaled, htwo_scaled, hdrop_scaled, heps_scaled, hb_scaled]

theorem SafetyStepSystem.cumulative_budget_to_time
    (S : SafetyStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
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

theorem SafetyStepSystem.cumulative_budget
    (S : SafetyStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Pstar
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d := by
  have hbudget := S.cumulative_budget_to_time T
  have hlower := S.Psi_lower T
  nlinarith [hbudget, hlower]

def SafetyStepSystem.toBudget (S : SafetyStepSystem) (T : ℕ) :
    SafetyBudget T where
  eta := S.eta
  lam := S.lam
  CR := S.CR
  Psi0 := S.Psi 0
  Pstar := S.Pstar
  Ceps := S.Ceps
  Cb := S.Cb
  Cd := S.Cd
  Gsq := S.Gsq
  R := S.R
  eps := S.eps
  b := S.b
  d := S.d
  eta_pos := S.eta_pos
  lam_pos := S.lam_pos
  CR_pos := S.CR_pos
  Gsq_nonneg := S.Gsq_nonneg
  R_nonneg := S.R_nonneg
  cumulative_budget := S.cumulative_budget T

theorem SafetyStepSystem.gradient_average_bound
    (S : SafetyStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.Gsq
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ)) := by
  exact SafetyBudget.gradient_average_bound hT (S.toBudget T)

theorem SafetyStepSystem.residual_average_bound
    (S : SafetyStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.R
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  exact SafetyBudget.residual_average_bound hT (S.toBudget T)

end

end OUSVRBLO
