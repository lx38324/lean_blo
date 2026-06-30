import OUSVRBLO.SafetyDescent

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/--
One-step scalar interface for the upper-gradient-improvement theorem.

This extends `SafetyStepSystem` with the certified improvement `Delta` and
proxy/comparison error `zeta`. The corrected residual drift contribution of
`zeta` is represented in `improved_drift`.
-/
structure ImprovementStepSystem extends SafetyStepSystem where
  Delta : ℕ → ℝ
  zeta : ℕ → ℝ
  Delta_nonneg : ∀ t, 0 ≤ Delta t
  zeta_nonneg : ∀ t, 0 ≤ zeta t
  improved_descent :
    ∀ t,
      P (t + 1) ≤ P t
        - eta / 2 * Gsq t
        + eta * lam ^ 2 / 2 * (CR * Rhat t + b t)
        - eta * lam ^ 2 / 2 * Delta t
        + eta * lam ^ 2 / 2 * zeta t
  improved_drift :
    ∀ t,
      R (t + 1) ≤
        (1 + CR * beta) * Rhat t
          + 2 * Aeta * Gsq t
          + beta * b t
          + 2 * Aeta * lam ^ 2 * zeta t
          + d t

def ImprovementStepSystem.Czeta (S : ImprovementStepSystem) : ℝ :=
  S.eta * S.lam ^ 2 / 2 + 2 * S.alpha * S.Aeta * S.lam ^ 2

theorem ImprovementStepSystem.one_step_lyapunov
    (S : ImprovementStepSystem) (t : ℕ) :
    S.Psi (t + 1) ≤ S.Psi t
      - S.eta / 4 * S.Gsq t
      - S.eta * S.lam ^ 2 * S.CR / 4 * S.R t
      - S.eta * S.lam ^ 2 / 2 * S.Delta t
      + S.Ceps * S.eps t
      + S.Cb * S.b t
      + S.Cd * S.d t
      + S.Czeta * S.zeta t := by
  dsimp [SafetyStepSystem.Psi, SafetyStepSystem.Ceps, SafetyStepSystem.Cb,
    SafetyStepSystem.Cd, ImprovementStepSystem.Czeta]
  have hdes := S.improved_descent t
  have hdrift := S.improved_drift t
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
          + S.alpha * S.d t
          - S.eta * S.lam ^ 2 / 2 * S.Delta t
          + (S.eta * S.lam ^ 2 / 2
            + 2 * S.alpha * S.Aeta * S.lam ^ 2) *
            S.zeta t := by
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

theorem ImprovementStepSystem.Czeta_le
    (S : ImprovementStepSystem) :
    S.Czeta ≤ 3 / 4 * S.eta * S.lam ^ 2 := by
  dsimp [ImprovementStepSystem.Czeta]
  have hscaled := mul_le_mul_of_nonneg_right S.two_alpha_Aeta_le (sq_nonneg S.lam)
  nlinarith [hscaled]

theorem ImprovementStepSystem.cumulative_budget_to_time
    (S : ImprovementStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Delta
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Psi T
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d
        + S.Czeta * SeqSum T S.zeta := by
  induction T with
  | zero =>
      simp [SeqSum]
  | succ T ih =>
      simp [SeqSum] at ih
      simp [SeqSum, Finset.sum_range_succ]
      have hstep := S.one_step_lyapunov T
      ring_nf at ih hstep ⊢
      nlinarith [ih, hstep]

theorem ImprovementStepSystem.cumulative_budget
    (S : ImprovementStepSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + (S.eta * S.lam ^ 2 / 2) * SeqSum T S.Delta
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Pstar
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d
        + S.Czeta * SeqSum T S.zeta := by
  have hbudget := S.cumulative_budget_to_time T
  have hlower := S.Psi_lower T
  nlinarith [hbudget, hlower]

def ImprovementStepSystem.toBudget (S : ImprovementStepSystem) (T : ℕ) :
    ImprovementBudget T where
  eta := S.eta
  lam := S.lam
  CR := S.CR
  Psi0 := S.Psi 0
  Pstar := S.Pstar
  Ceps := S.Ceps
  Cb := S.Cb
  Cd := S.Cd
  Czeta := S.Czeta
  Gsq := S.Gsq
  R := S.R
  Delta := S.Delta
  eps := S.eps
  b := S.b
  d := S.d
  zeta := S.zeta
  eta_pos := S.eta_pos
  lam_pos := S.lam_pos
  CR_pos := S.CR_pos
  Gsq_nonneg := S.Gsq_nonneg
  R_nonneg := S.R_nonneg
  Delta_nonneg := S.Delta_nonneg
  cumulative_budget := S.cumulative_budget T

theorem ImprovementStepSystem.gradient_improvement_average_bound
    (S : ImprovementStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.Gsq
      + 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Delta)
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ))
        + 4 * S.Czeta * SeqSum T S.zeta / (S.eta * (T : ℝ)) := by
  exact ImprovementBudget.gradient_improvement_average_bound hT (S.toBudget T)

theorem ImprovementStepSystem.residual_average_bound
    (S : ImprovementStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.R
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Czeta * SeqSum T S.zeta / (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  exact ImprovementBudget.residual_average_bound hT (S.toBudget T)

end

end OUSVRBLO
