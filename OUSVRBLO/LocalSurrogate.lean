import Mathlib

namespace OUSVRBLO

noncomputable section

/--
Abstract local regularized surrogate used to state the modeling interface.

This records the local value-response form without asserting global neural
network optimality or original BLO KKT convergence.
-/
structure LocalRegularizedSurrogate where
  X : Type
  Y : Type
  trainLoss : X → Y → ℝ
  distSqToRef : Y → ℝ
  rho : ℝ
  rho_nonneg : 0 ≤ rho

def LocalRegularizedSurrogate.h
    (S : LocalRegularizedSurrogate) (x : S.X) (xi : S.Y) : ℝ :=
  S.trainLoss x xi + S.rho / 2 * S.distSqToRef xi

/--
Minimal value-function interface: the selected response realizes the value.
-/
structure ValueFunctionInterface where
  X : Type
  Y : Type
  h : X → Y → ℝ
  v : X → ℝ
  response : X → Y
  value_eq_response : ∀ x, v x = h x (response x)

end

end OUSVRBLO
