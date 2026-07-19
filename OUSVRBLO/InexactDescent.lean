import Mathlib

namespace OUSVRBLO

open scoped RealInnerProductSpace

noncomputable section

/-- Polarization identity in the exact form used by the inexact-gradient proof. -/
theorem real_inner_self_add_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G Err : E) :
    ⟪G, G + Err⟫_ℝ =
      (‖G‖ ^ 2 + ‖G + Err‖ ^ 2 - ‖Err‖ ^ 2) / 2 := by
  have hGG : ⟪G, G⟫_ℝ = ‖G‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) G)
  have hEE : ⟪Err, Err⟫_ℝ = ‖Err‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) Err)
  have hsumSelf : ⟪G + Err, G + Err⟫_ℝ = ‖G + Err‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (G + Err))
  have hadd := real_inner_add_add_self G Err
  have hright : ⟪G, G + Err⟫_ℝ = ⟪G, G⟫_ℝ + ⟪G, Err⟫_ℝ := by
    exact inner_add_right G G Err
  rw [hGG] at hright
  rw [hGG, hEE, hsumSelf] at hadd
  nlinarith [hright, hadd]

/--
Hilbert-space inexact descent from a smoothness inequality and the update
`z⁺ = z - eta * (G + Err)` after the update has been substituted into the
smoothness bound.

The theorem checks the polarization identity and the step-size argument that
removes the nonpositive squared-step term.
-/
theorem inexact_gradient_descent_of_smoothness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Pnow Pnext eta LP : ℝ) (G Err : E)
    (heta : 0 ≤ eta)
    (hstep : LP * eta ≤ 1)
    (hsmooth :
      Pnext ≤ Pnow
        - eta * ⟪G, G + Err⟫_ℝ
        + LP * eta ^ 2 / 2 * ‖G + Err‖ ^ 2) :
    Pnext ≤ Pnow
      - eta / 2 * ‖G‖ ^ 2
      + eta / 2 * ‖Err‖ ^ 2 := by
  have hinner := real_inner_self_add_identity G Err
  have hcoef : 0 ≤ eta / 2 * (1 - LP * eta) := by
    have hetaHalf : 0 ≤ eta / 2 := div_nonneg heta (by norm_num)
    have hrest : 0 ≤ 1 - LP * eta := by linarith
    exact mul_nonneg hetaHalf hrest
  have hterm :
      0 ≤ eta / 2 * (1 - LP * eta) * ‖G + Err‖ ^ 2 := by
    exact mul_nonneg hcoef (sq_nonneg ‖G + Err‖)
  rw [hinner] at hsmooth
  nlinarith [hsmooth, hterm]

/-- Squared error control converts the Hilbert-space descent theorem into the
scalar interface used by the safety theorem. -/
theorem inexact_gradient_descent_with_error_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Pnow Pnext eta LP lam CR Q b : ℝ) (G Err : E)
    (heta : 0 ≤ eta)
    (hlam : 0 ≤ lam)
    (hstep : LP * eta ≤ 1)
    (hsmooth :
      Pnext ≤ Pnow
        - eta * ⟪G, G + Err⟫_ℝ
        + LP * eta ^ 2 / 2 * ‖G + Err‖ ^ 2)
    (herror : ‖Err‖ ^ 2 ≤ lam ^ 2 * (CR * Q + b)) :
    Pnext ≤ Pnow
      - eta / 2 * ‖G‖ ^ 2
      + eta * lam ^ 2 / 2 * (CR * Q + b) := by
  have hdes := inexact_gradient_descent_of_smoothness
    Pnow Pnext eta LP G Err heta hstep hsmooth
  have hetaHalf : 0 ≤ eta / 2 := div_nonneg heta (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left herror hetaHalf
  nlinarith [hdes, hscaled]

/-- Certified-error specialization retaining the favorable gain term. -/
theorem inexact_gradient_descent_with_certified_gain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Pnow Pnext eta LP lam CR Q b Gamma : ℝ) (G Err : E)
    (heta : 0 ≤ eta)
    (hlam : 0 ≤ lam)
    (hstep : LP * eta ≤ 1)
    (hsmooth :
      Pnext ≤ Pnow
        - eta * ⟪G, G + Err⟫_ℝ
        + LP * eta ^ 2 / 2 * ‖G + Err‖ ^ 2)
    (herror : ‖Err‖ ^ 2 ≤ lam ^ 2 * (CR * Q + b - Gamma)) :
    Pnext ≤ Pnow
      - eta / 2 * ‖G‖ ^ 2
      + eta * lam ^ 2 / 2 * (CR * Q + b)
      - eta * lam ^ 2 / 2 * Gamma := by
  have hdes := inexact_gradient_descent_of_smoothness
    Pnow Pnext eta LP G Err heta hstep hsmooth
  have hetaHalf : 0 ≤ eta / 2 := div_nonneg heta (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left herror hetaHalf
  nlinarith [hdes, hscaled]

end

end OUSVRBLO
