import OUSVRBLO.StrongMonotonicityCertificate
import Mathlib.Tactic.Module

open scoped InnerProductSpace

namespace OUSVRBLO

noncomputable section

/-- Gradient of a lower surrogate after adding a quadratic proximal term. -/
def proximalLowerGradient
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (baseGrad : Y → Y) (rho : ℝ) (reference xi : Y) : Y :=
  baseGrad xi + rho • (xi - reference)

/-- Difference identity for the proximal lower-gradient map. -/
theorem proximalLowerGradient_sub
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (baseGrad : Y → Y) (rho : ℝ) (reference xi zeta : Y) :
    proximalLowerGradient baseGrad rho reference xi -
        proximalLowerGradient baseGrad rho reference zeta =
      (baseGrad xi - baseGrad zeta) + rho • (xi - zeta) := by
  dsimp [proximalLowerGradient]
  module

/-- Exact inner-product contribution of quadratic proximal regularization. -/
theorem proximalLowerGradient_inner_sub
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (baseGrad : Y → Y) (rho : ℝ) (reference xi zeta : Y) :
    ⟪proximalLowerGradient baseGrad rho reference xi -
        proximalLowerGradient baseGrad rho reference zeta,
      xi - zeta⟫_ℝ =
      ⟪baseGrad xi - baseGrad zeta, xi - zeta⟫_ℝ
        + rho * ‖xi - zeta‖ ^ 2 := by
  rw [proximalLowerGradient_sub]
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/--
If the unregularized lower-gradient map is locally `curvature`-hypomonotone,
then adding a quadratic proximal term of strength `rho` makes the regularized
map `(rho - curvature)`-strongly monotone.
-/
theorem proximalLowerGradient_strong_monotone
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (baseGrad : Y → Y) (rho curvature : ℝ) (reference xi zeta : Y)
    (hhypo :
      -curvature * ‖xi - zeta‖ ^ 2 ≤
        ⟪baseGrad xi - baseGrad zeta, xi - zeta⟫_ℝ) :
    (rho - curvature) * ‖xi - zeta‖ ^ 2 ≤
      ⟪proximalLowerGradient baseGrad rho reference xi -
          proximalLowerGradient baseGrad rho reference zeta,
        xi - zeta⟫_ℝ := by
  rw [proximalLowerGradient_inner_sub]
  nlinarith

/--
When `rho > curvature`, a stationary point of the proximal lower-gradient map is
unique inside any region on which the hypomonotonicity premise holds.
-/
theorem proximalLowerGradient_stationary_unique
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (baseGrad : Y → Y) (rho curvature : ℝ) (reference xi zeta : Y)
    (hrho : curvature < rho)
    (hhypo :
      ∀ u w,
        -curvature * ‖u - w‖ ^ 2 ≤
          ⟪baseGrad u - baseGrad w, u - w⟫_ℝ)
    (hxi : proximalLowerGradient baseGrad rho reference xi = 0)
    (hzeta : proximalLowerGradient baseGrad rho reference zeta = 0) :
    xi = zeta := by
  exact eq_of_strong_monotonicity_and_stationarity
    (proximalLowerGradient baseGrad rho reference) xi zeta
    (rho - curvature) (sub_pos.mpr hrho) hxi hzeta
    (proximalLowerGradient_strong_monotone
      baseGrad rho curvature reference xi zeta (hhypo xi zeta))

/--
Proximal regularization gives a computable residual-to-value-gradient bound.
If the upper/value gradient is `L`-Lipschitz in the response and the base lower
gradient is `curvature`-hypomonotone, then the squared value-gradient error is
controlled by the squared proximal lower-gradient residual with constant
`L^2 / (rho - curvature)^2`.
-/
theorem value_gradient_error_sq_le_proximal_residual
    {Y G : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup G]
    (baseGrad : Y → Y) (upperGrad : Y → G)
    (rho curvature L : ℝ) (reference xi xistar : Y)
    (hrho : curvature < rho) (hL : 0 ≤ L)
    (hstationary : proximalLowerGradient baseGrad rho reference xistar = 0)
    (hhypo :
      -curvature * ‖xi - xistar‖ ^ 2 ≤
        ⟪baseGrad xi - baseGrad xistar, xi - xistar⟫_ℝ)
    (hlipschitz :
      ‖upperGrad xi - upperGrad xistar‖ ≤ L * ‖xi - xistar‖) :
    ‖upperGrad xi - upperGrad xistar‖ ^ 2 ≤
      (L ^ 2 / (rho - curvature) ^ 2) *
        ‖proximalLowerGradient baseGrad rho reference xi‖ ^ 2 := by
  exact value_gradient_error_sq_le_lower_gradient_residual
    (proximalLowerGradient baseGrad rho reference) upperGrad xi xistar
    (rho - curvature) L (sub_pos.mpr hrho) hL hstationary
    (proximalLowerGradient_strong_monotone
      baseGrad rho curvature reference xi xistar hhypo)
    hlipschitz

end

end OUSVRBLO
