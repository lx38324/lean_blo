import OUSVRBLO.ValueGradientErrorEmbedding
import OUSVRBLO.ResponseErrorBound

namespace OUSVRBLO

noncomputable section

/--
Sequence-level proposal data generated directly from a represented restricted
value-gradient interface.

The base and proposal gradients are no longer arbitrary vectors: they are the
`x`-partial gradients of the local lower surrogate at two feasible response
sequences.  The represented value gradient is supplied by the restricted value
interface.
-/
structure RestrictedValueProposalData
    (I : RestrictedValueGradientInterface)
    [NormedAddCommGroup I.G] where
  x : ℕ → I.X
  xiBase : ℕ → I.Y
  xiProp : ℕ → I.Y
  base_mem : ∀ t, xiBase t ∈ I.feasible (x t)
  prop_mem : ∀ t, xiProp t ∈ I.feasible (x t)
  theta : ℝ
  R : ℕ → ℝ
  Rbase : ℕ → ℝ
  Rprop : ℕ → ℝ
  epsBase : ℕ → ℝ
  tauR : ℕ → ℝ
  ehatBase : ℕ → ℝ
  ehatProp : ℕ → ℝ
  DeltaHat : ℕ → ℝ
  tauE : ℕ → ℝ
  rhoBase : ℕ → ℝ
  rhoProp : ℕ → ℝ
  Rbase_nonneg : ∀ t, 0 ≤ Rbase t
  Rprop_nonneg : ∀ t, 0 ≤ Rprop t
  epsBase_nonneg : ∀ t, 0 ≤ epsBase t
  tauR_nonneg : ∀ t, 0 ≤ tauR t
  rhoBase_nonneg : ∀ t, 0 ≤ rhoBase t
  rhoProp_nonneg : ∀ t, 0 ≤ rhoProp t
  tauE_nonneg : ∀ t, 0 ≤ tauE t
  base_contract :
    ∀ t, Rbase t ≤ (1 - theta) * R t + epsBase t
  proposal_calib_abs :
    ∀ t,
      |ehatProp t -
        ‖I.gradV (x t) - I.gradXH (x t) (xiProp t)‖ ^ 2| ≤ rhoProp t
  baseline_calib_abs :
    ∀ t,
      |ehatBase t -
        ‖I.gradV (x t) - I.gradXH (x t) (xiBase t)‖ ^ 2| ≤ rhoBase t

/-- Convert restricted-response data into the vector-gradient proposal package. -/
def RestrictedValueProposalData.toValueGradientProposalData
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.G]
    (S : RestrictedValueProposalData I) : ValueGradientProposalData I.G where
  theta := S.theta
  R := S.R
  Rbase := S.Rbase
  Rprop := S.Rprop
  epsBase := S.epsBase
  tauR := S.tauR
  gradV := fun t => I.gradV (S.x t)
  gradBase := fun t => I.gradXH (S.x t) (S.xiBase t)
  gradProp := fun t => I.gradXH (S.x t) (S.xiProp t)
  ehatBase := S.ehatBase
  ehatProp := S.ehatProp
  DeltaHat := S.DeltaHat
  tauE := S.tauE
  rhoBase := S.rhoBase
  rhoProp := S.rhoProp
  Rbase_nonneg := S.Rbase_nonneg
  Rprop_nonneg := S.Rprop_nonneg
  epsBase_nonneg := S.epsBase_nonneg
  tauR_nonneg := S.tauR_nonneg
  rhoBase_nonneg := S.rhoBase_nonneg
  rhoProp_nonneg := S.rhoProp_nonneg
  tauE_nonneg := S.tauE_nonneg
  base_contract := S.base_contract
  proposal_calib_abs := S.proposal_calib_abs
  baseline_calib_abs := S.baseline_calib_abs

/-- The represented value gradient is the response partial gradient from the
restricted value interface. -/
theorem RestrictedValueProposalData.gradV_eq_response
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.G]
    (S : RestrictedValueProposalData I) (t : ℕ) :
    (S.toValueGradientProposalData).gradV t =
      I.gradXH (S.x t) (I.response (S.x t)) := by
  exact I.gradient_eq_response (S.x t)

/-- The base true error is the squared difference between the represented value
gradient and the partial gradient at the feasible base response. -/
@[simp]
theorem RestrictedValueProposalData.eBase_eq
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.G]
    (S : RestrictedValueProposalData I) (t : ℕ) :
    (S.toValueGradientProposalData).eBase t =
      ‖I.gradV (S.x t) - I.gradXH (S.x t) (S.xiBase t)‖ ^ 2 := by
  rfl

/-- Response-gradient Lipschitzness and a base response-distance error bound
produce the natural sequence-level base R2 certificate. -/
theorem RestrictedValueProposalData.baseline_error_bound_of_lipschitz
    {I : RestrictedValueGradientInterface}
    [PseudoMetricSpace I.Y] [NormedAddCommGroup I.G]
    (S : RestrictedValueProposalData I)
    (L CEB : ℝ) (bias : ℕ → ℝ) (hL : 0 ≤ L)
    (hlipschitz :
      ∀ t,
        ‖I.gradXH (S.x t) (S.xiBase t) -
            I.gradXH (S.x t) (I.response (S.x t))‖
          ≤ L * dist (S.xiBase t) (I.response (S.x t)))
    (herror :
      ∀ t,
        dist (S.xiBase t) (I.response (S.x t)) ^ 2
          ≤ CEB * S.Rbase t + bias t)
    (t : ℕ) :
    (S.toValueGradientProposalData).eBase t
      ≤ (L ^ 2 * CEB) * S.Rbase t + L ^ 2 * bias t := by
  have hbound := I.r2_of_lipschitz_and_error_bound
    (S.x t) (S.xiBase t) L CEB (S.Rbase t) (bias t)
    hL (hlipschitz t) (herror t)
  simpa [RestrictedValueProposalData.eBase_eq, norm_sub_rev] using hbound

/-- Positive quadratic growth gives an objective-gap certificate for the base
value-gradient error at every round. -/
theorem RestrictedValueProposalData.baseline_error_bound_of_quadratic_growth
    {I : RestrictedValueGradientInterface}
    [PseudoMetricSpace I.Y] [NormedAddCommGroup I.G]
    (S : RestrictedValueProposalData I)
    (modulus L : ℝ) (hmodulus : 0 < modulus) (hL : 0 ≤ L)
    (hqg :
      ∀ x xi, xi ∈ I.feasible x →
        modulus * dist xi (I.response x) ^ 2 ≤ I.h x xi - I.v x)
    (hlipschitz :
      ∀ t,
        ‖I.gradXH (S.x t) (S.xiBase t) -
            I.gradXH (S.x t) (I.response (S.x t))‖
          ≤ L * dist (S.xiBase t) (I.response (S.x t)))
    (t : ℕ) :
    (S.toValueGradientProposalData).eBase t
      ≤ (L ^ 2 / modulus) *
          (I.h (S.x t) (S.xiBase t) - I.v (S.x t)) := by
  have hbound := I.r2_of_quadratic_growth
    modulus L hmodulus hL hqg
    (S.x t) (S.xiBase t) (S.base_mem t) (hlipschitz t)
  simpa [RestrictedValueProposalData.eBase_eq, norm_sub_rev] using hbound

end

end OUSVRBLO
