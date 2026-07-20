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
    intro x xi hxi
    simp only [h, response]
    positivity
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
  simp [h, response, v, Real.dist_eq, sq_abs]

/-- The represented response is the unique exact restricted minimizer. -/
theorem unique_minimizer (k x xi : ℝ)
    (hxi : (valueGradientInterface k).toRestrictedValueResponseInterface.IsMinimizer x xi) :
    xi = response k x := by
  apply (valueGradientInterface k).toRestrictedValueResponseInterface.
    eq_response_of_quadratic_growth (1 / 2) (by norm_num)
  · intro x' xi' hmem
    have hq := quadratic_growth k x' xi'
    simpa [valueGradientInterface, h, response, v] using hq
  · exact hxi

/-- The upper/value-gradient map is Lipschitz in the response with constant `|k|`. -/
theorem gradXH_lipschitz (k x xi : ℝ) :
    ‖gradXH k x xi - gradXH k x (response k x)‖ ≤
      |k| * dist xi (response k x) := by
  simp [gradXH, response, Real.norm_eq_abs, Real.dist_eq, abs_mul]

/-- Exact value-gradient error identity for the quadratic model. -/
theorem gradient_error_sq_eq (k x xi : ℝ) :
    ‖gradXH k x xi - gradXH k x (response k x)‖ ^ 2 =
      k ^ 2 * dist xi (response k x) ^ 2 := by
  simp [gradXH, response, Real.norm_eq_abs, Real.dist_eq, abs_mul, sq_abs]
  ring

/--
The residual-to-value-gradient inequality is non-vacuous: in this concrete model
the squared gradient error is exactly `2 * k^2` times the restricted objective
gap.
-/
theorem exact_r2_gap (k x xi : ℝ) :
    ‖(valueGradientInterface k).gradXH x xi -
        (valueGradientInterface k).gradV x‖ ^ 2 =
      2 * k ^ 2 *
        ((valueGradientInterface k).h x xi -
          (valueGradientInterface k).v x) := by
  simp [valueGradientInterface, gradXH, response, h, v,
    Real.norm_eq_abs, abs_mul, sq_abs]
  ring

/-- The generic quadratic-growth/Lipschitz theorem recovers the model's R2 form. -/
theorem certified_r2_gap (k x xi : ℝ) :
    ‖(valueGradientInterface k).gradXH x xi -
        (valueGradientInterface k).gradV x‖ ^ 2 ≤
      ((|k| : ℝ) ^ 2 / (1 / 2 : ℝ)) *
        ((valueGradientInterface k).h x xi -
          (valueGradientInterface k).v x) := by
  apply (valueGradientInterface k).r2_of_quadratic_growth
    (1 / 2) |k| (by norm_num) (abs_nonneg k)
  · intro x' xi' hmem
    exact quadratic_growth k x' xi'
  · simp
  · exact gradXH_lipschitz k x xi

end ScalarQuadraticResponse

end

end OUSVRBLO
