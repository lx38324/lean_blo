import OUSVRBLO.TrajectoryCertifiedProposalGain
import OUSVRBLO.EndToEndCorollaries
import OUSVRBLO.AnalyticPointwise

open BigOperators Filter Topology
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/-- Summability of the certificate-facing base error and residual tolerance
supplies summability of the public envelope error. -/
theorem TrajectoryCertifiedProposalGainSystem.eps_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR) :
    Summable S.toCertifiedGainStepSystem.eps := by
  change Summable
    S.proposal.toAcceptedResponseSelector.safeguardSystem.eps
  exact S.proposal.toAcceptedResponseSelector.safeguardSystem.eps_summable
    hepsBase htauR

/-- A trajectory-facing same-iterate stationarity/residual certificate. -/
theorem TrajectoryCertifiedProposalGainSystem.exists_joint_certificate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖S.G t‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t
        ≤ 4 * S.toCertifiedGainStepSystem.accumulatedRhs T /
            (S.driftParameters.eta * (T : ℝ)) := by
  change ∃ t < T,
    S.toCertifiedGainStepSystem.jointMeasure t ≤
      4 * S.toCertifiedGainStepSystem.accumulatedRhs T /
        (S.toCertifiedGainStepSystem.eta * (T : ℝ))
  exact S.toCertifiedGainStepSystem.exists_joint_certificate hT

/-- Summable base contraction error, residual tolerance, bias, and drift errors
produce the explicit same-iterate `O(1/T)` certificate. -/
theorem TrajectoryCertifiedProposalGainSystem.exists_joint_certificate_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖S.G t‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t
        ≤ 4 * S.toCertifiedGainStepSystem.summableRhs /
            (S.driftParameters.eta * (T : ℝ)) := by
  have heps : Summable S.toCertifiedGainStepSystem.eps :=
    S.eps_summable hepsBase htauR
  change ∃ t < T,
    S.toCertifiedGainStepSystem.jointMeasure t ≤
      4 * S.toCertifiedGainStepSystem.summableRhs /
        (S.toCertifiedGainStepSystem.eta * (T : ℝ))
  exact S.toCertifiedGainStepSystem.exists_joint_certificate_of_summable
    heps hb hd hT

/-- The actual gradient norm converges pointwise to zero under summable
certificate perturbations. -/
theorem TrajectoryCertifiedProposalGainSystem.gradient_norm_tendsto_zero_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun t => ‖S.G t‖) atTop (𝓝 0) := by
  apply tendsto_norm_zero_of_tendsto_norm_sq_zero S.G
  have heps : Summable S.toCertifiedGainStepSystem.eps :=
    S.eps_summable hepsBase htauR
  change Tendsto S.toCertifiedGainStepSystem.Gsq atTop (𝓝 0)
  exact S.toCertifiedGainStepSystem.gradient_tendsto_zero_of_summable
    heps hb hd

/-- The response residual converges pointwise to zero. -/
theorem TrajectoryCertifiedProposalGainSystem.residual_tendsto_zero_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto S.proposal.R atTop (𝓝 0) := by
  have heps : Summable S.toCertifiedGainStepSystem.eps :=
    S.eps_summable hepsBase htauR
  change Tendsto S.toCertifiedGainStepSystem.R atTop (𝓝 0)
  exact S.toCertifiedGainStepSystem.residual_tendsto_zero_of_summable
    heps hb hd

/-- The selected uncertainty-adjusted gain vanishes pointwise as a finite-budget
consequence. -/
theorem TrajectoryCertifiedProposalGainSystem.gain_tendsto_zero_of_summable
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Summable S.proposal.epsBase)
    (htauR : Summable S.proposal.tauR)
    (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (S.proposal.toAcceptedResponseSelector).Gamma atTop (𝓝 0) := by
  have heps : Summable S.toCertifiedGainStepSystem.eps :=
    S.eps_summable hepsBase htauR
  have h := S.toCertifiedGainStepSystem.gain_tendsto_zero_of_summable
    heps hb hd
  rw [S.public_Gamma] at h
  exact h

end

end OUSVRBLO
