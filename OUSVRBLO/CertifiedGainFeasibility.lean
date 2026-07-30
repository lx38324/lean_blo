import OUSVRBLO.AcceptedResponseSelector

namespace OUSVRBLO

noncomputable section

/-- The gain selected by the explicit proposal/fallback rule is nonnegative. -/
theorem AcceptedResponseSelector.Gamma_nonneg
    (S : AcceptedResponseSelector) (t : ℕ) :
    0 ≤ S.Gamma t := by
  have h := S.proxySequence.Gamma_nonneg t
  simpa using h

/-- A nonnegative selected true error and the calibrated improvement inequality
force the accepted gain to be no larger than the base true error. -/
theorem AcceptedResponseSelector.Gamma_le_base_error
    (S : AcceptedResponseSelector) (t : ℕ) :
    S.Gamma t ≤ S.eB t := by
  have herror := S.eOnline_nonneg t
  have himprove := S.true_error_improves t
  linarith

/-- The gain-aware residual-to-error scale is automatically nonnegative.  Thus
the enhanced theorem does not require an additional effective-gain clipping
operation. -/
theorem AcceptedResponseSelector.certified_scale_nonneg
    (S : AcceptedResponseSelector) (CR : ℝ) (b : ℕ → ℝ)
    (hbaseline : ∀ t, S.eB t ≤ CR * S.safeguardSystem.Q t + b t)
    (t : ℕ) :
    0 ≤ CR * S.safeguardSystem.Q t + b t - S.Gamma t := by
  have herror := S.eOnline_nonneg t
  have hr2 := S.r2_certified CR b hbaseline t
  linarith

end

end OUSVRBLO
