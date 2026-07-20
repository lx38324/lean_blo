import OUSVRBLO.TrajectoryCertifiedProposalCorollaries
import OUSVRBLO.IterationComplexity

open BigOperators
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/-- Explicit trajectory-facing tolerance horizon. -/
def TrajectoryCertifiedProposalGainSystem.JointToleranceHorizon
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (T : ℕ) (tolerance : ℝ) : Prop :=
  S.toCertifiedGainStepSystem.JointToleranceHorizon T tolerance

/-- The conventional divided lower bound on `T` implies the trajectory-facing
cross-multiplied horizon condition. -/
theorem TrajectoryCertifiedProposalGainSystem.jointToleranceHorizon_of_div_bound
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    {T : ℕ} {tolerance : ℝ}
    (htolerance : 0 < tolerance)
    (horizon :
      4 * S.toCertifiedGainStepSystem.summableRhs /
          (S.driftParameters.eta * tolerance) ≤ (T : ℝ)) :
    S.JointToleranceHorizon T tolerance := by
  exact S.toCertifiedGainStepSystem.jointToleranceHorizon_of_div_bound
    htolerance horizon

/-- Summable certificate errors and the explicit horizon condition produce one
trajectory iterate whose joint stationarity/response measure is below the target
tolerance. -/
theorem TrajectoryCertifiedProposalGainSystem.exists_joint_certificate_le_tolerance_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) {tolerance : ℝ}
    (horizon : S.JointToleranceHorizon T tolerance) :
    ∃ t < T,
      ‖S.G t‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t
        ≤ tolerance := by
  have heps : Summable S.toCertifiedGainStepSystem.eps :=
    S.eps_summable hepsBase htauR
  change ∃ t < T,
    S.toCertifiedGainStepSystem.Gsq t
      + S.toCertifiedGainStepSystem.lam ^ 2 *
          S.toCertifiedGainStepSystem.CR *
          S.toCertifiedGainStepSystem.R t ≤ tolerance
  exact
    CertifiedGainStepSystem.exists_joint_certificate_le_tolerance_of_summable
      S.toCertifiedGainStepSystem heps hb hd hT horizon

/-- Component form: the same trajectory iterate has both small stationarity and
small response residual. -/
theorem TrajectoryCertifiedProposalGainSystem.exists_stationarity_and_scaled_residual_le_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) {tolerance : ℝ}
    (horizon : S.JointToleranceHorizon T tolerance) :
    ∃ t < T,
      ‖S.G t‖ ^ 2 ≤ tolerance ∧
      S.proposal.R t ≤ tolerance /
        (S.driftParameters.lam ^ 2 * S.CR) := by
  have heps : Summable S.toCertifiedGainStepSystem.eps :=
    S.eps_summable hepsBase htauR
  change ∃ t < T,
    S.toCertifiedGainStepSystem.Gsq t ≤ tolerance ∧
    S.toCertifiedGainStepSystem.R t ≤ tolerance /
      (S.toCertifiedGainStepSystem.lam ^ 2 *
        S.toCertifiedGainStepSystem.CR)
  exact
    CertifiedGainStepSystem.exists_stationarity_and_scaled_residual_le_of_summable
      S.toCertifiedGainStepSystem heps hb hd hT horizon

end

end OUSVRBLO
