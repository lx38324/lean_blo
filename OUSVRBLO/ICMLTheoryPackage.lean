import OUSVRBLO.GainAdjustedRates
import OUSVRBLO.ProximalLocalInstantiation
import OUSVRBLO.StochasticGainAdjustedRates
import OUSVRBLO.StochasticVarianceRate

open BigOperators
open scoped BigOperators InnerProductSpace Gradient

namespace OUSVRBLO

noncomputable section

/-!
# Stable ICML-facing theorem exports

These declarations are thin wrappers around the fully checked theorem stack.
They provide a compact citation surface without introducing new assumptions or
weakening the existing claim boundary.
-/
namespace ICMLTheoryPackage

/-- Theorem 1: fallback-safe deterministic finite-horizon Lyapunov budget for the
trajectory descent vector. -/
theorem fallback_safe_finite_horizon
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + S.toCertifiedGainStepSystem.Cgain *
          SeqSum T (S.proposal.toAcceptedResponseSelector).Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.proposal.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps *
            SeqSum T (S.proposal.toAcceptedResponseSelector).safeguardSystem.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  exact S.cumulative_budget T

/-- Objective-gradient form of the fallback-safe finite-horizon theorem. This
wrapper makes the stationarity semantics explicit rather than identifying an
arbitrary descent vector with the objective gradient. -/
theorem fallback_safe_objective_gradient_finite_horizon
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S) (T : ℕ) :
    (S.driftParameters.eta / 4) *
          SeqSum T (fun t => ‖gradient S.objective (S.z t)‖ ^ 2)
      + S.toCertifiedGainStepSystem.Cgain *
          SeqSum T (S.proposal.toAcceptedResponseSelector).Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.proposal.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps *
            SeqSum T (S.proposal.toAcceptedResponseSelector).safeguardSystem.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  have hgradient :
      (fun t => ‖gradient S.objective (S.z t)‖ ^ 2) =
        (fun t => ‖S.G t‖ ^ 2) := by
    funext t
    rw [C.gradient_eq t]
  rw [hgradient]
  exact S.cumulative_budget T

/-- Theorem 2: gain-adjusted average stationarity/residual performance. -/
theorem certified_gain_average
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by
  exact S.joint_average_bound_with_gain hT

/-- Certified accumulated gain tightens the selected trajectory's same-horizon
stationarity/residual certificate. -/
theorem certified_gain_same_iterate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖S.G t‖ ^ 2 + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t ≤
        4 * S.toCertifiedGainStepSystem.gainAdjustedRhs T /
          (S.driftParameters.eta * (T : ℝ)) := by
  exact S.exists_joint_certificate_with_gain hT

/-- Objective-gradient form of the gain-adjusted same-horizon certificate. -/
theorem certified_gain_objective_gradient_same_iterate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S)
    {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      ‖gradient S.objective (S.z t)‖ ^ 2
          + S.driftParameters.lam ^ 2 * S.CR * S.proposal.R t ≤
        4 * S.toCertifiedGainStepSystem.gainAdjustedRhs T /
          (S.driftParameters.eta * (T : ℝ)) := by
  exact S.exists_objective_gradient_joint_certificate_with_gain C hT

/-- Positive accumulated certified gain makes the gain-adjusted numerator
strictly smaller than the safety-only numerator. -/
theorem positive_gain_strictly_tightens
    (S : CertifiedGainStepSystem) (T : ℕ)
    (hgainSum : 0 < SeqSum T S.Gamma) :
    S.gainAdjustedRhs T < S.accumulatedRhs T := by
  exact S.gainAdjustedRhs_lt_accumulatedRhs_of_positive_gain T hgainSum

/-- Theorem 3: a proximal local-response model instantiates the principal
residual-to-value-gradient error certificate. -/
theorem proximal_response_error_certificate
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) (x : I.X) (xi : I.Y) :
    ‖I.gradV x - I.gradXH x xi‖ ^ 2 ≤ M.CR * M.residual x xi := by
  exact M.r2 x xi

/-- Sequence-level baseline error certificate generated by the same proximal
local-response model. -/
theorem proximal_baseline_sequence_certificate
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (S : RestrictedValueProposalData I)
    (M : ProximalRestrictedValueModel I)
    (hRbase : ∀ t, S.Rbase t = M.residual (S.x t) (S.xiBase t))
    (t : ℕ) :
    (S.toValueGradientProposalData).eBase t ≤ M.CR * S.Rbase t := by
  exact S.baseline_error_bound_of_proximal M hRbase t

/-- Theorem 4: exact expectation-level stochastic certified-gain budget. -/
theorem stochastic_expected_finite_horizon
    (S : StochasticExpectedGainSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.EGsq
      + S.Cgain * SeqSum T S.EGamma
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.ER
      ≤ S.accumulatedRhs T := by
  exact S.cumulative_budget T

/-- Gain-adjusted expected average stationarity/residual rate. -/
theorem stochastic_expected_gain_adjusted_average
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by
  exact S.joint_average_bound_with_gain hT

/-- Some expected iterate on the horizon satisfies the gain-adjusted joint
stationarity/residual certificate. -/
theorem stochastic_expected_same_iterate
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.jointMeasure t ≤
        4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by
  exact S.exists_joint_certificate_with_gain hT

/-- Positive accumulated expected certified gain strictly tightens the expected
selected-trajectory numerator. -/
theorem stochastic_positive_gain_strictly_tightens
    (S : StochasticExpectedGainSystem) (T : ℕ)
    (hgainSum : 0 < SeqSum T S.EGamma) :
    S.gainAdjustedRhs T < S.accumulatedRhs T := by
  exact S.gainAdjustedRhs_lt_accumulatedRhs_of_positive_gain T hgainSum

/-- Manuscript-specialized stochastic rate with explicit
`O(1 / (eta*T) + eta*sigma^2)` dependence. -/
theorem stochastic_variance_rate
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T)
    (LR sigmaBar : ℝ)
    (hAeta :
      S.Aeta = S.eta / (2 * sqrtTwo * S.lam) + LR * S.eta ^ 2 / 2)
    (heps : ∀ t, S.Eeps t = 0)
    (hb : ∀ t, S.Eb t = 0)
    (hd : ∀ t, S.Ed t = 0)
    (hsigma : ∀ t, S.sigmaSq t ≤ sigmaBar) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + S.eta *
          (2 * S.LP
            + sqrtTwo * S.lam * S.CR / S.theta
            + 2 * S.lam ^ 2 * S.CR * LR * S.eta / S.theta) * sigmaBar := by
  exact S.joint_average_bound_of_variance_only_manuscript
    hT LR sigmaBar hAeta heps hb hd hsigma

end ICMLTheoryPackage

end

end OUSVRBLO
