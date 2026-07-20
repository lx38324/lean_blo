import OUSVRBLO.RestrictedEnvelope
import OUSVRBLO.ResponseErrorBound

namespace OUSVRBLO

noncomputable section

namespace ScalarQuadraticResponse

/-- A one-dimensional regularized response model with center `k * x`. -/
def h (k x xi : ℝ) : ℝ :=
  (xi - k * x) ^ 2 / 2

/-- The exact restricted lower response. -/
def response (k x : ℝ) : ℝ :=
  k * x

/-- The represented restricted value is zero. -/
def v (_k _x : ℝ) : ℝ :=
  0

/-- Partial derivative of `h` with respect to the upper variable `x`. -/
def gradXH (k x xi : ℝ) : ℝ :=
  -k * (xi - k * x)

/-- A fully explicit restricted value and value-gradient interface. -/
def valueGradientInterface (k : ℝ) : RestrictedValueGradientInterface where
  X := ℝ
  Y := ℝ
  feasible := fun _ => Set.univ
  h := h k
  v := v k
  response := response k
  response_mem := by
    intro x
    simp
  response_minimizes := by
    intro x xi _
    dsimp [h, response]
    nlinarith [sq_nonneg (xi - k * x)]
  value_eq_response := by
    intro x
    simp [v, h, response]
  G := ℝ
  gradV := fun _ => 0
  gradXH := gradXH k
  gradient_eq_response := by
    intro x
    simp [gradXH, response]

/-- The model has exact quadratic growth with modulus `1 / 2`. -/
theorem quadratic_growth (k x xi : ℝ) :
    (1 / 2 : ℝ) * dist xi (response k x) ^ 2 ≤
      h k x xi - v k x := by
  rw [Real.dist_eq]
  simp only [h, response, v, sub_zero, sq_abs]
  ring_nf

/-- The represented response is the unique exact restricted minimizer. -/
theorem unique_minimizer (k x xi : ℝ)
    (hxi :
      (valueGradientInterface k).toRestrictedValueResponseInterface.IsMinimizer
        x xi) :
    xi = response k x := by
  refine RestrictedValueResponseInterface.eq_response_of_quadratic_growth
    (valueGradientInterface k).toRestrictedValueResponseInterface
    (1 / 2) (by norm_num) ?_ hxi
  intro x' xi' _
  have hq := quadratic_growth k x' xi'
  simpa [valueGradientInterface, h, response, v] using hq

/-- Exact norm identity behind response-Lipschitzness. -/
theorem gradXH_error_norm_eq (k x xi : ℝ) :
    ‖gradXH k x xi - gradXH k x (response k x)‖ =
      |k| * dist xi (response k x) := by
  rw [Real.dist_eq]
  simp [gradXH, response, Real.norm_eq_abs]

/-- The upper/value-gradient map is Lipschitz in the response with constant `|k|`. -/
theorem gradXH_lipschitz (k x xi : ℝ) :
    ‖gradXH k x xi - gradXH k x (response k x)‖ ≤
      |k| * dist xi (response k x) := by
  rw [gradXH_error_norm_eq]

/-- Exact value-gradient error identity for the quadratic model. -/
theorem gradient_error_sq_eq (k x xi : ℝ) :
    ‖gradXH k x xi - gradXH k x (response k x)‖ ^ 2 =
      k ^ 2 * dist xi (response k x) ^ 2 := by
  rw [gradXH_error_norm_eq, mul_pow, sq_abs]

/--
The residual-to-value-gradient inequality is non-vacuous: in this concrete model
the squared gradient error is exactly `2 * k^2` times the restricted objective
gap.
-/
theorem exact_r2_gap (k x xi : ℝ) :
    ‖gradXH k x xi - gradXH k x (response k x)‖ ^ 2 =
      2 * k ^ 2 * (h k x xi - v k x) := by
  rw [gradient_error_sq_eq]
  rw [Real.dist_eq]
  simp only [h, response, v, sub_zero, sq_abs]
  ring

/-- The generic quadratic-growth/Lipschitz argument recovers the same R2 scale. -/
theorem certified_r2_gap (k x xi : ℝ) :
    ‖gradXH k x xi - gradXH k x (response k x)‖ ^ 2 ≤
      2 * |k| ^ 2 * (h k x xi - v k x) := by
  have herror :
      dist xi (response k x) ^ 2 ≤
        2 * (h k x xi - v k x) + 0 := by
    have hq := quadratic_growth k x xi
    nlinarith
  have hbound := gradient_error_sq_le_of_lipschitz_and_error_bound
    (gradXH k x) xi (response k x) |k| 2
      (h k x xi - v k x) 0 (abs_nonneg k)
      (gradXH_lipschitz k x xi) herror
  nlinarith

end ScalarQuadraticResponse

end

end OUSVRBLO
