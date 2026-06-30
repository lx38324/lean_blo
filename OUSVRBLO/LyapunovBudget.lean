import Mathlib

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- Finite-horizon sum shorthand. -/
def SeqSum (T : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, a t

/--
A cumulative Lyapunov budget for the fallback-safe fixed-penalty theorem.

This is the formally checked part after the analytic assumptions have yielded
one finite-horizon inequality. The analytic objects `Gsq` and `R` stand for
`‖G_t‖^2` and the anchor residual. The terms `eps`, `b`, and `d` are the
safeguard, value-gradient, and drift error sequences.
-/
structure SafetyBudget (T : ℕ) where
  eta : ℝ
  lam : ℝ
  CR : ℝ
  Psi0 : ℝ
  Pstar : ℝ
  Ceps : ℝ
  Cb : ℝ
  Cd : ℝ
  Gsq : ℕ → ℝ
  R : ℕ → ℝ
  eps : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  CR_pos : 0 < CR
  Gsq_nonneg : ∀ t, 0 ≤ Gsq t
  R_nonneg : ∀ t, 0 ≤ R t
  cumulative_budget :
    (eta / 4) * SeqSum T Gsq +
      (eta * lam ^ 2 * CR / 4) * SeqSum T R
      ≤ Psi0 - Pstar + Ceps * SeqSum T eps + Cb * SeqSum T b + Cd * SeqSum T d

/-- Right-hand side of the safety budget. -/
def SafetyBudget.rhs {T : ℕ} (B : SafetyBudget T) : ℝ :=
  B.Psi0 - B.Pstar + B.Ceps * SeqSum T B.eps +
    B.Cb * SeqSum T B.b + B.Cd * SeqSum T B.d

/--
From the cumulative safety budget, derive the averaged stationarity bound.

This corresponds to equation (3) in the informal proof after summing the
Lyapunov descent inequality and dropping the nonnegative residual term.
-/
theorem SafetyBudget.gradient_average_bound {T : ℕ} (hT : 0 < T)
    (B : SafetyBudget T) :
    (1 / (T : ℝ)) * SeqSum T B.Gsq
      ≤ 4 * (B.Psi0 - B.Pstar) / (B.eta * (T : ℝ))
        + 4 * B.Ceps * SeqSum T B.eps / (B.eta * (T : ℝ))
        + 4 * B.Cb * SeqSum T B.b / (B.eta * (T : ℝ))
        + 4 * B.Cd * SeqSum T B.d / (B.eta * (T : ℝ)) := by
  have hRsum_nonneg : 0 ≤ SeqSum T B.R := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => B.R_nonneg t)
  have hcoefR_nonneg : 0 ≤ B.eta * B.lam ^ 2 * B.CR / 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt B.eta_pos) (sq_nonneg B.lam))
        (le_of_lt B.CR_pos))
      (by norm_num)
  have hres_nonneg : 0 ≤ (B.eta * B.lam ^ 2 * B.CR / 4) * SeqSum T B.R := by
    exact mul_nonneg hcoefR_nonneg hRsum_nonneg
  have hG_budget : (B.eta / 4) * SeqSum T B.Gsq ≤ B.rhs := by
    dsimp [SafetyBudget.rhs]
    nlinarith [B.cumulative_budget, hres_nonneg]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden_pos : 0 < B.eta * (T : ℝ) := mul_pos B.eta_pos hTreal
  have hscale_nonneg : 0 ≤ 4 / (B.eta * (T : ℝ)) := by
    exact le_of_lt (div_pos (by norm_num) hden_pos)
  have hscaled := mul_le_mul_of_nonneg_left hG_budget hscale_nonneg
  calc
    (1 / (T : ℝ)) * SeqSum T B.Gsq
        = (4 / (B.eta * (T : ℝ))) * ((B.eta / 4) * SeqSum T B.Gsq) := by
          field_simp [ne_of_gt B.eta_pos, ne_of_gt hTreal]
    _ ≤ (4 / (B.eta * (T : ℝ))) * B.rhs := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    _ = 4 * (B.Psi0 - B.Pstar) / (B.eta * (T : ℝ))
        + 4 * B.Ceps * SeqSum T B.eps / (B.eta * (T : ℝ))
        + 4 * B.Cb * SeqSum T B.b / (B.eta * (T : ℝ))
        + 4 * B.Cd * SeqSum T B.d / (B.eta * (T : ℝ)) := by
          dsimp [SafetyBudget.rhs]
          ring

/--
From the same cumulative budget, derive the averaged residual bound.

This corresponds to equation (4) in the informal proof after dropping the
nonnegative stationarity term.
-/
theorem SafetyBudget.residual_average_bound {T : ℕ} (hT : 0 < T)
    (B : SafetyBudget T) :
    (1 / (T : ℝ)) * SeqSum T B.R
      ≤ 4 * (B.Psi0 - B.Pstar) / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Ceps * SeqSum T B.eps / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Cb * SeqSum T B.b / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Cd * SeqSum T B.d / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ)) := by
  have hGsum_nonneg : 0 ≤ SeqSum T B.Gsq := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => B.Gsq_nonneg t)
  have hcoefG_nonneg : 0 ≤ B.eta / 4 := by
    exact div_nonneg (le_of_lt B.eta_pos) (by norm_num)
  have hstat_nonneg : 0 ≤ (B.eta / 4) * SeqSum T B.Gsq := by
    exact mul_nonneg hcoefG_nonneg hGsum_nonneg
  have hR_budget : (B.eta * B.lam ^ 2 * B.CR / 4) * SeqSum T B.R ≤ B.rhs := by
    dsimp [SafetyBudget.rhs]
    nlinarith [B.cumulative_budget, hstat_nonneg]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden_pos : 0 < B.eta * B.lam ^ 2 * B.CR * (T : ℝ) := by
    have hlam_sq_pos : 0 < B.lam ^ 2 := sq_pos_of_ne_zero (ne_of_gt B.lam_pos)
    exact mul_pos (mul_pos (mul_pos B.eta_pos hlam_sq_pos) B.CR_pos) hTreal
  have hscale_nonneg : 0 ≤ 4 / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ)) := by
    exact le_of_lt (div_pos (by norm_num) hden_pos)
  have hscaled := mul_le_mul_of_nonneg_left hR_budget hscale_nonneg
  calc
    (1 / (T : ℝ)) * SeqSum T B.R
        = (4 / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))) *
            ((B.eta * B.lam ^ 2 * B.CR / 4) * SeqSum T B.R) := by
          field_simp [ne_of_gt B.eta_pos, ne_of_gt B.lam_pos, ne_of_gt B.CR_pos,
            ne_of_gt hTreal]
    _ ≤ (4 / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))) * B.rhs := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    _ = 4 * (B.Psi0 - B.Pstar) / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Ceps * SeqSum T B.eps / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Cb * SeqSum T B.b / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Cd * SeqSum T B.d / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ)) := by
          dsimp [SafetyBudget.rhs]
          ring

/--
Cumulative budget for the upper-gradient-improvement theorem.

`Delta` is the certified improvement of the accepted online anchor over the
lower-only anchor. `zeta` is the proxy-calibration or comparison error. The
coefficient `Czeta` is intentionally abstract: the revised informal proof can
set it to `eta * lam^2 / 2 + 2 * alpha * A_eta * lam^2`, and then upper-bound it
by `3/4 * eta * lam^2` under the small-step condition.
-/
structure ImprovementBudget (T : ℕ) where
  eta : ℝ
  lam : ℝ
  CR : ℝ
  Psi0 : ℝ
  Pstar : ℝ
  Ceps : ℝ
  Cb : ℝ
  Cd : ℝ
  Czeta : ℝ
  Gsq : ℕ → ℝ
  R : ℕ → ℝ
  Delta : ℕ → ℝ
  eps : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  zeta : ℕ → ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  CR_pos : 0 < CR
  Gsq_nonneg : ∀ t, 0 ≤ Gsq t
  R_nonneg : ∀ t, 0 ≤ R t
  Delta_nonneg : ∀ t, 0 ≤ Delta t
  cumulative_budget :
    (eta / 4) * SeqSum T Gsq +
      (eta * lam ^ 2 / 2) * SeqSum T Delta +
      (eta * lam ^ 2 * CR / 4) * SeqSum T R
      ≤ Psi0 - Pstar + Ceps * SeqSum T eps + Cb * SeqSum T b +
        Cd * SeqSum T d + Czeta * SeqSum T zeta

/-- Right-hand side of the improvement budget. -/
def ImprovementBudget.rhs {T : ℕ} (B : ImprovementBudget T) : ℝ :=
  B.Psi0 - B.Pstar + B.Ceps * SeqSum T B.eps +
    B.Cb * SeqSum T B.b + B.Cd * SeqSum T B.d +
    B.Czeta * SeqSum T B.zeta

/--
Averaged stationarity plus upper-gradient-improvement bound.

This is the Lean analogue of the revised enhanced theorem after summing the
Lyapunov descent inequality and dropping the nonnegative residual term.
-/
theorem ImprovementBudget.gradient_improvement_average_bound {T : ℕ} (hT : 0 < T)
    (B : ImprovementBudget T) :
    (1 / (T : ℝ)) * SeqSum T B.Gsq
      + 2 * B.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T B.Delta)
      ≤ 4 * (B.Psi0 - B.Pstar) / (B.eta * (T : ℝ))
        + 4 * B.Ceps * SeqSum T B.eps / (B.eta * (T : ℝ))
        + 4 * B.Cb * SeqSum T B.b / (B.eta * (T : ℝ))
        + 4 * B.Cd * SeqSum T B.d / (B.eta * (T : ℝ))
        + 4 * B.Czeta * SeqSum T B.zeta / (B.eta * (T : ℝ)) := by
  have hRsum_nonneg : 0 ≤ SeqSum T B.R := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => B.R_nonneg t)
  have hcoefR_nonneg : 0 ≤ B.eta * B.lam ^ 2 * B.CR / 4 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt B.eta_pos) (sq_nonneg B.lam))
        (le_of_lt B.CR_pos))
      (by norm_num)
  have hres_nonneg : 0 ≤ (B.eta * B.lam ^ 2 * B.CR / 4) * SeqSum T B.R := by
    exact mul_nonneg hcoefR_nonneg hRsum_nonneg
  have hmain_budget :
      (B.eta / 4) * SeqSum T B.Gsq +
        (B.eta * B.lam ^ 2 / 2) * SeqSum T B.Delta ≤ B.rhs := by
    dsimp [ImprovementBudget.rhs]
    nlinarith [B.cumulative_budget, hres_nonneg]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden_pos : 0 < B.eta * (T : ℝ) := mul_pos B.eta_pos hTreal
  have hscale_nonneg : 0 ≤ 4 / (B.eta * (T : ℝ)) := by
    exact le_of_lt (div_pos (by norm_num) hden_pos)
  have hscaled := mul_le_mul_of_nonneg_left hmain_budget hscale_nonneg
  calc
    (1 / (T : ℝ)) * SeqSum T B.Gsq
      + 2 * B.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T B.Delta)
        = (4 / (B.eta * (T : ℝ))) *
            ((B.eta / 4) * SeqSum T B.Gsq +
              (B.eta * B.lam ^ 2 / 2) * SeqSum T B.Delta) := by
          field_simp [ne_of_gt B.eta_pos, ne_of_gt hTreal]
          ring_nf
    _ ≤ (4 / (B.eta * (T : ℝ))) * B.rhs := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    _ = 4 * (B.Psi0 - B.Pstar) / (B.eta * (T : ℝ))
        + 4 * B.Ceps * SeqSum T B.eps / (B.eta * (T : ℝ))
        + 4 * B.Cb * SeqSum T B.b / (B.eta * (T : ℝ))
        + 4 * B.Cd * SeqSum T B.d / (B.eta * (T : ℝ))
        + 4 * B.Czeta * SeqSum T B.zeta / (B.eta * (T : ℝ)) := by
          dsimp [ImprovementBudget.rhs]
          ring

/--
Averaged residual bound for the improvement theorem.
-/
theorem ImprovementBudget.residual_average_bound {T : ℕ} (hT : 0 < T)
    (B : ImprovementBudget T) :
    (1 / (T : ℝ)) * SeqSum T B.R
      ≤ 4 * (B.Psi0 - B.Pstar) / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Ceps * SeqSum T B.eps / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Cb * SeqSum T B.b / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Cd * SeqSum T B.d / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Czeta * SeqSum T B.zeta / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ)) := by
  have hGsum_nonneg : 0 ≤ SeqSum T B.Gsq := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => B.Gsq_nonneg t)
  have hDsum_nonneg : 0 ≤ SeqSum T B.Delta := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => B.Delta_nonneg t)
  have hcoefG_nonneg : 0 ≤ B.eta / 4 := by
    exact div_nonneg (le_of_lt B.eta_pos) (by norm_num)
  have hcoefD_nonneg : 0 ≤ B.eta * B.lam ^ 2 / 2 := by
    exact div_nonneg
      (mul_nonneg (le_of_lt B.eta_pos) (sq_nonneg B.lam))
      (by norm_num)
  have hstat_nonneg : 0 ≤ (B.eta / 4) * SeqSum T B.Gsq := by
    exact mul_nonneg hcoefG_nonneg hGsum_nonneg
  have hdelta_nonneg : 0 ≤ (B.eta * B.lam ^ 2 / 2) * SeqSum T B.Delta := by
    exact mul_nonneg hcoefD_nonneg hDsum_nonneg
  have hR_budget : (B.eta * B.lam ^ 2 * B.CR / 4) * SeqSum T B.R ≤ B.rhs := by
    dsimp [ImprovementBudget.rhs]
    nlinarith [B.cumulative_budget, hstat_nonneg, hdelta_nonneg]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden_pos : 0 < B.eta * B.lam ^ 2 * B.CR * (T : ℝ) := by
    have hlam_sq_pos : 0 < B.lam ^ 2 := sq_pos_of_ne_zero (ne_of_gt B.lam_pos)
    exact mul_pos (mul_pos (mul_pos B.eta_pos hlam_sq_pos) B.CR_pos) hTreal
  have hscale_nonneg : 0 ≤ 4 / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ)) := by
    exact le_of_lt (div_pos (by norm_num) hden_pos)
  have hscaled := mul_le_mul_of_nonneg_left hR_budget hscale_nonneg
  calc
    (1 / (T : ℝ)) * SeqSum T B.R
        = (4 / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))) *
            ((B.eta * B.lam ^ 2 * B.CR / 4) * SeqSum T B.R) := by
          field_simp [ne_of_gt B.eta_pos, ne_of_gt B.lam_pos, ne_of_gt B.CR_pos,
            ne_of_gt hTreal]
    _ ≤ (4 / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))) * B.rhs := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    _ = 4 * (B.Psi0 - B.Pstar) / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Ceps * SeqSum T B.eps / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Cb * SeqSum T B.b / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Cd * SeqSum T B.d / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ))
        + 4 * B.Czeta * SeqSum T B.zeta / (B.eta * B.lam ^ 2 * B.CR * (T : ℝ)) := by
          dsimp [ImprovementBudget.rhs]
          ring

end

end OUSVRBLO
