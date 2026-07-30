import OUSVRBLO.ValueGradientTrajectory
import OUSVRBLO.FixedPenaltyGradientSemantics

open scoped Gradient

namespace OUSVRBLO

noncomputable section

/--
A semantic certificate coupling the represented value gradient used by the
proposal/error layer to the value component of the fixed-penalty objective.

Without this coupling, one could separately certify that `G` is a gradient of a
fixed-penalty decomposition and that `Err` uses some represented value gradient,
without proving that the two value-gradient objects agree.
-/
structure ValueGradientFixedPenaltyCertificate
    {E X V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (S : ValueGradientTrajectorySystem E X V) where
  outer : E → ℝ
  lower : E → ℝ
  value : E → ℝ
  gradOuter : ℕ → E
  gradLower : ℕ → E
  objective_eq :
    S.objective = fixedPenaltyObjective
      outer lower value S.driftParameters.lam
  gradient_eq :
    ∀ t,
      S.G t = fixedPenaltyGradient
        (gradOuter t) (gradLower t)
        (S.errorEmbedding (S.proposal.gradV t))
        S.driftParameters.lam
  outer_hasGradient :
    ∀ t, HasGradientAt outer (gradOuter t) (S.z t)
  lower_hasGradient :
    ∀ t, HasGradientAt lower (gradLower t) (S.z t)
  value_hasGradient :
    ∀ t,
      HasGradientAt value
        (S.errorEmbedding (S.proposal.gradV t)) (S.z t)

/-- Convert the coupled value-gradient semantics into the generic fixed-penalty
component certificate. -/
def ValueGradientFixedPenaltyCertificate.toFixedPenaltyCertificate
    {E X V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : ValueGradientTrajectorySystem E X V}
    (C : ValueGradientFixedPenaltyCertificate S) :
    FixedPenaltyTrajectoryGradientCertificate S.toTrajectorySystem where
  outer := C.outer
  lower := C.lower
  value := C.value
  gradOuter := C.gradOuter
  gradLower := C.gradLower
  gradValue := fun t => S.errorEmbedding (S.proposal.gradV t)
  objective_eq := C.objective_eq
  gradient_eq := C.gradient_eq
  outer_hasGradient := C.outer_hasGradient
  lower_hasGradient := C.lower_hasGradient
  value_hasGradient := C.value_hasGradient

/-- The true objective gradient has the fixed-penalty form with exactly the
represented value gradient used by the proposal layer. -/
theorem ValueGradientFixedPenaltyCertificate.objective_gradient_eq
    {E X V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : ValueGradientTrajectorySystem E X V}
    (C : ValueGradientFixedPenaltyCertificate S) (t : ℕ) :
    gradient S.objective (S.z t) =
      fixedPenaltyGradient
        (C.gradOuter t) (C.gradLower t)
        (S.errorEmbedding (S.proposal.gradV t))
        S.driftParameters.lam := by
  exact C.toFixedPenaltyCertificate.objective_gradient_eq t

/-- Adding the exact inexact-gradient error replaces the represented value
gradient by the partial gradient induced by the response selected by the
accept/fallback rule. -/
theorem ValueGradientFixedPenaltyCertificate.approximate_gradient_eq
    {E X V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : ValueGradientTrajectorySystem E X V}
    (C : ValueGradientFixedPenaltyCertificate S) (t : ℕ) :
    S.G t + S.Err t =
      fixedPenaltyGradient
        (C.gradOuter t) (C.gradLower t)
        (S.errorEmbedding (S.proposal.gradOnline t))
        S.driftParameters.lam := by
  rw [C.gradient_eq t]
  simp only [ValueGradientTrajectorySystem.Err,
    ValueGradientProposalData.ambientError,
    ValueGradientProposalData.valueGradientError,
    fixedPenaltyGradient, map_sub, smul_sub]
  abel

/-- The actual trajectory displacement is therefore the negative step along the
fixed-penalty gradient using the response selected by the certificates. -/
theorem ValueGradientFixedPenaltyCertificate.update_uses_selected_gradient
    {E X V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : ValueGradientTrajectorySystem E X V}
    (C : ValueGradientFixedPenaltyCertificate S) (t : ℕ) :
    S.z (t + 1) - S.z t =
      -S.driftParameters.eta •
        fixedPenaltyGradient
          (C.gradOuter t) (C.gradLower t)
          (S.errorEmbedding (S.proposal.gradOnline t))
          S.driftParameters.lam := by
  rw [S.update_displacement t]
  have h := congrArg
    (fun v : E => -S.driftParameters.eta • v)
    (C.approximate_gradient_eq t)
  simpa [ValueGradientTrajectorySystem.Err] using h

end

end OUSVRBLO
