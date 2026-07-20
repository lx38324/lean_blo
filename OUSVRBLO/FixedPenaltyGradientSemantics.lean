import OUSVRBLO.TrajectoryGradientSemantics
import Mathlib.Analysis.Calculus.FDeriv.Add

open scoped Gradient

namespace OUSVRBLO

noncomputable section

/-- Fixed-penalty scalar objective assembled from an outer term, a lower term,
and a represented value term. -/
def fixedPenaltyObjective
    {E : Type*} (outer lower value : E → ℝ) (lam : ℝ) : E → ℝ :=
  fun z => outer z + lam * (lower z - value z)

/-- Gradient vector corresponding to the fixed-penalty objective. -/
def fixedPenaltyGradient
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (gradOuter gradLower gradValue : E) (lam : ℝ) : E :=
  gradOuter + lam • (gradLower - gradValue)

/-- Gradients of the three objective components compose into the expected
fixed-penalty gradient. -/
theorem hasGradientAt_fixedPenaltyObjective
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (outer lower value : E → ℝ) (lam : ℝ)
    (z gradOuter gradLower gradValue : E)
    (hOuter : HasGradientAt outer gradOuter z)
    (hLower : HasGradientAt lower gradLower z)
    (hValue : HasGradientAt value gradValue z) :
    HasGradientAt (fixedPenaltyObjective outer lower value lam)
      (fixedPenaltyGradient gradOuter gradLower gradValue lam) z := by
  have hdiff : HasGradientAt (lower - value) (gradLower - gradValue) z :=
    hLower.sub hValue
  have hscaled :
      HasGradientAt (lam • (lower - value))
        (lam • (gradLower - gradValue)) z :=
    hdiff.const_smul lam
  have hsum :
      HasGradientAt (outer + lam • (lower - value))
        (gradOuter + lam • (gradLower - gradValue)) z :=
    hOuter.add hscaled
  simpa [fixedPenaltyObjective, fixedPenaltyGradient, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hsum

/--
Data certifying that the objective and gradient sequence in the trajectory
 theorem come from an explicit fixed-penalty decomposition.
-/
structure FixedPenaltyTrajectoryGradientCertificate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) where
  outer : E → ℝ
  lower : E → ℝ
  value : E → ℝ
  gradOuter : ℕ → E
  gradLower : ℕ → E
  gradValue : ℕ → E
  objective_eq :
    S.objective =
      fixedPenaltyObjective outer lower value S.driftParameters.lam
  gradient_eq :
    ∀ t,
      S.G t = fixedPenaltyGradient
        (gradOuter t) (gradLower t) (gradValue t) S.driftParameters.lam
  outer_hasGradient :
    ∀ t, HasGradientAt outer (gradOuter t) (S.z t)
  lower_hasGradient :
    ∀ t, HasGradientAt lower (gradLower t) (S.z t)
  value_hasGradient :
    ∀ t, HasGradientAt value (gradValue t) (S.z t)

/-- A fixed-penalty component certificate generates the objective-gradient
certificate consumed by the stationarity statements. -/
def FixedPenaltyTrajectoryGradientCertificate.toTrajectoryGradientCertificate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : TrajectoryCertifiedProposalGainSystem E X}
    (C : FixedPenaltyTrajectoryGradientCertificate S) :
    TrajectoryGradientCertificate S where
  hasGradient := by
    intro t
    rw [C.objective_eq, C.gradient_eq t]
    exact hasGradientAt_fixedPenaltyObjective
      C.outer C.lower C.value S.driftParameters.lam
      (S.z t) (C.gradOuter t) (C.gradLower t) (C.gradValue t)
      (C.outer_hasGradient t) (C.lower_hasGradient t)
      (C.value_hasGradient t)

/-- The canonical objective gradient therefore has the advertised fixed-penalty
formula along the trajectory. -/
theorem FixedPenaltyTrajectoryGradientCertificate.objective_gradient_eq
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : TrajectoryCertifiedProposalGainSystem E X}
    (C : FixedPenaltyTrajectoryGradientCertificate S) (t : ℕ) :
    gradient S.objective (S.z t) =
      fixedPenaltyGradient
        (C.gradOuter t) (C.gradLower t) (C.gradValue t)
        S.driftParameters.lam := by
  rw [C.toTrajectoryGradientCertificate.gradient_eq t, C.gradient_eq t]

end

end OUSVRBLO
