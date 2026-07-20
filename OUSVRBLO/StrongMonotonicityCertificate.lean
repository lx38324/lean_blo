import OUSVRBLO.ResponseErrorBound
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace

namespace OUSVRBLO

noncomputable section

/--
A strongly monotone lower-gradient map gives a response-distance error bound in
terms of its computable gradient residual.

This is a local sufficient condition for using
`R(x, xi) = ‖∇_xi h(x, xi)‖^2` in the main theorem.
-/
theorem distance_sq_le_gradient_residual_of_strong_monotonicity
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (lowerGrad : Y → Y) (xi xistar : Y) (modulus : ℝ)
    (hmodulus : 0 < modulus)
    (hstationary : lowerGrad xistar = 0)
    (hstrong :
      modulus * ‖xi - xistar‖ ^ 2 ≤
        ⟪lowerGrad xi - lowerGrad xistar, xi - xistar⟫_ℝ) :
    ‖xi - xistar‖ ^ 2 ≤
      (1 / modulus ^ 2) * ‖lowerGrad xi‖ ^ 2 := by
  have hcauchy := real_inner_le_norm
    (lowerGrad xi - lowerGrad xistar) (xi - xistar)
  have hmain :
      modulus * ‖xi - xistar‖ ^ 2 ≤
        ‖lowerGrad xi‖ * ‖xi - xistar‖ := by
    rw [hstationary, sub_zero] at hcauchy hstrong
    exact hstrong.trans hcauchy
  by_cases hdist_zero : ‖xi - xistar‖ = 0
  · simp [hdist_zero]
  · have hdist_pos : 0 < ‖xi - xistar‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hdist_zero)
    have hlinear : modulus * ‖xi - xistar‖ ≤ ‖lowerGrad xi‖ := by
      apply (mul_le_mul_right hdist_pos).mp
      simpa [pow_two, mul_assoc] using hmain
    have hleft_nonneg : 0 ≤ modulus * ‖xi - xistar‖ :=
      mul_nonneg (le_of_lt hmodulus) (norm_nonneg _)
    have hsquare :
        (modulus * ‖xi - xistar‖) ^ 2 ≤ ‖lowerGrad xi‖ ^ 2 := by
      nlinarith [hlinear, hleft_nonneg, norm_nonneg (lowerGrad xi)]
    have hmsquare :
        modulus ^ 2 * ‖xi - xistar‖ ^ 2 ≤ ‖lowerGrad xi‖ ^ 2 := by
      simpa [mul_pow] using hsquare
    have hscale : 0 ≤ 1 / modulus ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hmsquare hscale
    calc
      ‖xi - xistar‖ ^ 2
          = (1 / modulus ^ 2) *
              (modulus ^ 2 * ‖xi - xistar‖ ^ 2) := by
                field_simp [ne_of_gt hmodulus]
      _ ≤ (1 / modulus ^ 2) * ‖lowerGrad xi‖ ^ 2 := hscaled

/-- Two stationary points of a strongly monotone lower-gradient map coincide. -/
theorem eq_of_strong_monotonicity_and_stationarity
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (lowerGrad : Y → Y) (xi xistar : Y) (modulus : ℝ)
    (hmodulus : 0 < modulus)
    (hxi : lowerGrad xi = 0)
    (hxistar : lowerGrad xistar = 0)
    (hstrong :
      modulus * ‖xi - xistar‖ ^ 2 ≤
        ⟪lowerGrad xi - lowerGrad xistar, xi - xistar⟫_ℝ) :
    xi = xistar := by
  have herror := distance_sq_le_gradient_residual_of_strong_monotonicity
    lowerGrad xi xistar modulus hmodulus hxistar hstrong
  rw [hxi, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at herror
  have hnorm_zero : ‖xi - xistar‖ = 0 := by
    nlinarith [sq_nonneg ‖xi - xistar‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

/--
Strong monotonicity of the lower-gradient map and Lipschitz dependence of the
upper/value gradient on the response give an explicit R2 certificate with
constant `L^2 / modulus^2`.
-/
theorem value_gradient_error_sq_le_lower_gradient_residual
    {Y G : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup G]
    (lowerGrad : Y → Y) (upperGrad : Y → G)
    (xi xistar : Y) (modulus L : ℝ)
    (hmodulus : 0 < modulus) (hL : 0 ≤ L)
    (hstationary : lowerGrad xistar = 0)
    (hstrong :
      modulus * ‖xi - xistar‖ ^ 2 ≤
        ⟪lowerGrad xi - lowerGrad xistar, xi - xistar⟫_ℝ)
    (hlipschitz :
      ‖upperGrad xi - upperGrad xistar‖ ≤ L * ‖xi - xistar‖) :
    ‖upperGrad xi - upperGrad xistar‖ ^ 2 ≤
      (L ^ 2 / modulus ^ 2) * ‖lowerGrad xi‖ ^ 2 := by
  have herror := distance_sq_le_gradient_residual_of_strong_monotonicity
    lowerGrad xi xistar modulus hmodulus hstationary hstrong
  have herror_dist :
      dist xi xistar ^ 2 ≤
        (1 / modulus ^ 2) * ‖lowerGrad xi‖ ^ 2 + 0 := by
    simpa [dist_eq_norm] using herror
  have hlipschitz_dist :
      ‖upperGrad xi - upperGrad xistar‖ ≤ L * dist xi xistar := by
    simpa [dist_eq_norm] using hlipschitz
  have hbound := gradient_error_sq_le_of_lipschitz_and_error_bound
    upperGrad xi xistar L (1 / modulus ^ 2) ‖lowerGrad xi‖ ^ 2 0
      hL hlipschitz_dist herror_dist
  simpa [div_eq_mul_inv, mul_assoc] using hbound

end

end OUSVRBLO
