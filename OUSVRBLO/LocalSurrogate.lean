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
Legacy minimal value-function interface. It is retained for compatibility,
but the restricted minimizer interface below is the preferred theorem-facing
abstraction.
-/
structure ValueFunctionInterface where
  X : Type
  Y : Type
  h : X → Y → ℝ
  v : X → ℝ
  response : X → Y
  value_eq_response : ∀ x, v x = h x (response x)

/--
Restricted local value-response interface.

The selected response is feasible and minimizes the local surrogate over the
specified analysis region. This avoids identifying an arbitrary local branch
with the global value function of the original nonconvex lower problem.
-/
structure RestrictedValueResponseInterface where
  X : Type
  Y : Type
  feasible : X → Set Y
  h : X → Y → ℝ
  v : X → ℝ
  response : X → Y
  response_mem : ∀ x, response x ∈ feasible x
  response_minimizes :
    ∀ x xi, xi ∈ feasible x → h x (response x) ≤ h x xi
  value_eq_response : ∀ x, v x = h x (response x)

/-- Every feasible response lies above the represented restricted value. -/
theorem RestrictedValueResponseInterface.value_le
    (S : RestrictedValueResponseInterface) (x : S.X) (xi : S.Y)
    (hxi : xi ∈ S.feasible x) :
    S.v x ≤ S.h x xi := by
  rw [S.value_eq_response x]
  exact S.response_minimizes x xi hxi

/--
Abstract envelope-gradient interface attached to a restricted minimizer.

`G` can be instantiated by the ambient gradient space. The equality is kept
explicit because the repository does not yet formalize a full Danskin theorem
for nonconvex neural surrogates.
-/
structure RestrictedValueGradientInterface
    extends RestrictedValueResponseInterface where
  G : Type
  gradV : X → G
  gradXH : X → Y → G
  gradient_eq_response : ∀ x, gradV x = gradXH x (response x)

end

end OUSVRBLO
