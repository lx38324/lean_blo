import OUSVRBLO.TrajectoryIterationComplexity
import Mathlib.Analysis.Calculus.Gradient.Basic

open BigOperators Filter Topology
open scoped BigOperators InnerProductSpace Gradient

namespace OUSVRBLO

noncomputable section

/--
Semantic certificate that the vector sequence called `G` by the trajectory
Lyapunov theorem is the actual Hilbert-space gradient of the represented
fixed-penalty objective along the trajectory.

The repository leaves this as a local analytic interface for a concrete neural
surrogate, but once supplied it rules out interpreting an arbitrary descent
vector as the objective gradient.
-/
structure TrajectoryGradientCertificate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) : Prop where
  hasGradient : ∀ t, HasGradientAt S.objective (S.G t) (S.z t)

/-- The canonical gradient operator agrees with the trajectory vector. -/
theorem TrajectoryGradientCertificate.gradient_eq
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : TrajectoryCertifiedProposalGainSystem E X}
    (C : TrajectoryGradientCertificate S) (t : ℕ) :
    gradient S.objective (S.z t) = S.G t :=
  (C.hasGradient t).gradient

/-- Finite-horizon same-iterate certificate written with the actual objective
gradient. -/
theorem TrajectoryCertifiedProposalGainSystem.exists_objective_gradient_joint_certificate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖gradient S.objective (S.z t)‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t
        ≤ 4 * S.toCertifiedGainStepSystem.accumulatedRhs T /
            (S.driftParameters.eta * (T : ℝ)) := by
  obtain ⟨t, ht, hcert⟩ := S.exists_joint_certificate hT
  refine ⟨t, ht, ?_⟩
  rw [C.gradient_eq t]
  exact hcert

/-- Summable-error same-iterate `O(1/T)` certificate stated using the actual
objective gradient. -/
theorem TrajectoryCertifiedProposalGainSystem.
    exists_objective_gradient_joint_certificate_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖gradient S.objective (S.z t)‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t
        ≤ 4 * S.toCertifiedGainStepSystem.summableRhs /
            (S.driftParameters.eta * (T : ℝ)) := by
  obtain ⟨t, ht, hcert⟩ :=
    S.exists_joint_certificate_of_summable hepsBase htauR hb hd hT
  refine ⟨t, ht, ?_⟩
  rw [C.gradient_eq t]
  exact hcert

/-- The objective gradient norm converges pointwise to zero under summable
certificate perturbations. -/
theorem TrajectoryCertifiedProposalGainSystem.
    objective_gradient_norm_tendsto_zero_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun t => ‖gradient S.objective (S.z t)‖) atTop (𝓝 0) := by
  have hfun :
      (fun t => ‖gradient S.objective (S.z t)‖) =
        (fun t => ‖S.G t‖) := by
    funext t
    rw [C.gradient_eq t]
  rw [hfun]
  exact S.gradient_norm_tendsto_zero_of_summable
    hepsBase htauR hb hd

/-- Explicit squared objective-gradient and response-residual tolerance theorem. -/
theorem TrajectoryCertifiedProposalGainSystem.
    exists_objective_gradient_and_scaled_residual_le_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) {tolerance : ℝ}
    (horizon : S.JointToleranceHorizon T tolerance) :
    ∃ t < T,
      ‖gradient S.objective (S.z t)‖ ^ 2 ≤ tolerance ∧
      S.proposal.R t ≤ tolerance /
        (S.driftParameters.lam ^ 2 * S.CR) := by
  obtain ⟨t, ht, hgrad, hres⟩ :=
    S.exists_stationarity_and_scaled_residual_le_of_summable
      hepsBase htauR hb hd hT horizon
  refine ⟨t, ht, ?_, hres⟩
  rw [C.gradient_eq t]
  exact hgrad

/-- Standard `epsilon`-stationarity statement. The horizon is imposed at squared
tolerance `epsilon^2`, hence the usual `O(1/epsilon^2)` dependence for gradient
norm stationarity. -/
theorem TrajectoryCertifiedProposalGainSystem.
    exists_objective_gradient_norm_and_scaled_residual_le_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (horizon : S.JointToleranceHorizon T (epsilon ^ 2)) :
    ∃ t < T,
      ‖gradient S.objective (S.z t)‖ ≤ epsilon ∧
      S.proposal.R t ≤ epsilon ^ 2 /
        (S.driftParameters.lam ^ 2 * S.CR) := by
  obtain ⟨t, ht, hgradSq, hres⟩ :=
    S.exists_objective_gradient_and_scaled_residual_le_of_summable
      C hepsBase htauR hb hd hT horizon
  have hnormNonneg : 0 ≤ ‖gradient S.objective (S.z t)‖ := norm_nonneg _
  have hgrad : ‖gradient S.objective (S.z t)‖ ≤ epsilon := by
    nlinarith [sq_nonneg epsilon]
  exact ⟨t, ht, hgrad, hres⟩

end

end OUSVRBLO
