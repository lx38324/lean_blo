import OUSVRBLO.LocalSurrogate
import Mathlib.Analysis.Calculus.FDeriv.Prod

open ContinuousLinearMap

namespace OUSVRBLO

noncomputable section

/-- A feasible minimizer of the represented restricted lower problem. -/
def RestrictedValueResponseInterface.IsMinimizer
    (S : RestrictedValueResponseInterface) (x : S.X) (xi : S.Y) : Prop :=
  xi ∈ S.feasible x ∧
    ∀ y, y ∈ S.feasible x → S.h x xi ≤ S.h x y

/-- The selected response is a minimizer of the represented restricted problem. -/
theorem RestrictedValueResponseInterface.response_isMinimizer
    (S : RestrictedValueResponseInterface) (x : S.X) :
    S.IsMinimizer x (S.response x) := by
  exact ⟨S.response_mem x, S.response_minimizes x⟩

/--
A positive quadratic-growth certificate makes the represented restricted response
unique among exact feasible minimizers.

This is the local property needed by the value-response interpretation; it does
not assert uniqueness for the original unrestricted nonconvex lower problem.
-/
theorem RestrictedValueResponseInterface.eq_response_of_quadratic_growth
    (S : RestrictedValueResponseInterface) [MetricSpace S.Y]
    (modulus : ℝ) (hmodulus : 0 < modulus)
    (hqg :
      ∀ x xi, xi ∈ S.feasible x →
        modulus * dist xi (S.response x) ^ 2 ≤
          S.h x xi - S.h x (S.response x))
    {x : S.X} {xi : S.Y} (hxi : S.IsMinimizer x xi) :
    xi = S.response x := by
  have hq := hqg x xi hxi.1
  have hmin : S.h x xi ≤ S.h x (S.response x) :=
    hxi.2 (S.response x) (S.response_mem x)
  have hprod_nonneg : 0 ≤ modulus * dist xi (S.response x) ^ 2 := by
    exact mul_nonneg (le_of_lt hmodulus) (sq_nonneg _)
  have hprod_zero : modulus * dist xi (S.response x) ^ 2 = 0 := by
    nlinarith
  have hdist_sq_zero : dist xi (S.response x) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hprod_zero with hmod_zero | hdist_zero
    · exact False.elim ((ne_of_gt hmodulus) hmod_zero)
    · exact hdist_zero
  have hdist_zero : dist xi (S.response x) = 0 := by
    exact sq_eq_zero_iff.mp hdist_sq_zero
  exact dist_eq_zero.mp hdist_zero

/--
Envelope derivative along a differentiable stationary response branch.

If `h` is differentiable at `(x, response x)`, the selected response is
differentiable at `x`, and the derivative of `h` annihilates all vertical
(response-space) directions, then the derivative of the branch value
`x ↦ h (x, response x)` is exactly the partial derivative in the `x`
direction.  This is a local branch-envelope theorem, not a global nonconvex
Danskin theorem.
-/
theorem hasFDerivAt_branchValue_of_stationary_response
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (h : X × Y → ℝ) (response : X → Y) (x : X)
    (dh : X × Y →L[ℝ] ℝ) (dresponse : X →L[ℝ] Y)
    (hh : HasFDerivAt h dh (x, response x))
    (hr : HasFDerivAt response dresponse x)
    (hstationary : ∀ dy : Y, dh (0, dy) = 0) :
    HasFDerivAt (fun x => h (x, response x))
      (dh.comp (ContinuousLinearMap.inl ℝ X Y)) x := by
  have hpair :
      HasFDerivAt (fun x => (x, response x))
        ((1 : X →L[ℝ] X).prod dresponse) x :=
    (hasFDerivAt_id x).prodMk hr
  have hcomp := hh.comp x hpair
  have hderiv :
      dh.comp ((1 : X →L[ℝ] X).prod dresponse) =
        dh.comp (ContinuousLinearMap.inl ℝ X Y) := by
    ext dx
    change dh (dx, dresponse dx) = dh (dx, 0)
    calc
      dh (dx, dresponse dx)
          = dh ((dx, 0) + (0, dresponse dx)) := by simp
      _ = dh (dx, 0) + dh (0, dresponse dx) := by rw [map_add]
      _ = dh (dx, 0) := by rw [hstationary]; simp
  rw [hderiv] at hcomp
  exact hcomp

/--
The branch-envelope theorem specialized to a represented restricted value.
The value identity comes from the restricted minimizer interface; differentiable
response regularity and lower stationarity remain explicit local assumptions.
-/
theorem RestrictedValueResponseInterface.hasFDerivAt_value_of_stationary_response
    (S : RestrictedValueResponseInterface)
    [NormedAddCommGroup S.X] [NormedSpace ℝ S.X]
    [NormedAddCommGroup S.Y] [NormedSpace ℝ S.Y]
    (x : S.X) (dh : S.X × S.Y →L[ℝ] ℝ)
    (dresponse : S.X →L[ℝ] S.Y)
    (hh : HasFDerivAt (fun p : S.X × S.Y => S.h p.1 p.2) dh
      (x, S.response x))
    (hr : HasFDerivAt S.response dresponse x)
    (hstationary : ∀ dy : S.Y, dh (0, dy) = 0) :
    HasFDerivAt S.v (dh.comp (ContinuousLinearMap.inl ℝ S.X S.Y)) x := by
  have hbranch := hasFDerivAt_branchValue_of_stationary_response
    (fun p : S.X × S.Y => S.h p.1 p.2) S.response x dh dresponse hh hr
      hstationary
  have hv : S.v = fun x => S.h x (S.response x) :=
    funext S.value_eq_response
  rw [hv]
  exact hbranch

end

end OUSVRBLO
