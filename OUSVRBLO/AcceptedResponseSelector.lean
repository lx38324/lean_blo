import OUSVRBLO.SafeguardCertificate
import OUSVRBLO.ProxySequenceCertificate

namespace OUSVRBLO

noncomputable section

/--
An explicit per-round proposal/fallback selector.

When `accept t = true`, the online response is the learned proposal and its
residual/proxy certificates must hold.  When `accept t = false`, the online
response is exactly the safe base response and the certified gain is defined to
be zero.  Thus fallback safety is a theorem of the selector rather than an
informal convention.
-/
structure AcceptedResponseSelector where
  theta : ℝ
  R : ℕ → ℝ
  Rbase : ℕ → ℝ
  Rprop : ℕ → ℝ
  epsBase : ℕ → ℝ
  tauR : ℕ → ℝ
  eB : ℕ → ℝ
  eProp : ℕ → ℝ
  ehatB : ℕ → ℝ
  ehatProp : ℕ → ℝ
  DeltaHat : ℕ → ℝ
  tauE : ℕ → ℝ
  rhoB : ℕ → ℝ
  rhoProp : ℕ → ℝ
  accept : ℕ → Bool
  Rbase_nonneg : ∀ t, 0 ≤ Rbase t
  epsBase_nonneg : ∀ t, 0 ≤ epsBase t
  tauR_nonneg : ∀ t, 0 ≤ tauR t
  rhoB_nonneg : ∀ t, 0 ≤ rhoB t
  rhoProp_nonneg : ∀ t, 0 ≤ rhoProp t
  tauE_nonneg : ∀ t, 0 ≤ tauE t
  base_contract :
    ∀ t, Rbase t ≤ (1 - theta) * R t + epsBase t
  proposal_residual_safe :
    ∀ t, accept t = true → Rprop t ≤ Rbase t + tauR t
  proposal_calib_abs :
    ∀ t, |ehatProp t - eProp t| ≤ rhoProp t
  baseline_calib_abs :
    ∀ t, |ehatB t - eB t| ≤ rhoB t
  proposal_proxy_improves :
    ∀ t, accept t = true →
      ehatProp t ≤ ehatB t - DeltaHat t + tauE t
  proposal_gain_nonneg :
    ∀ t, accept t = true →
      0 ≤ DeltaHat t - tauE t - rhoProp t - rhoB t

/-- Residual of the response actually used after proposal/fallback selection. -/
def AcceptedResponseSelector.Ronline
    (S : AcceptedResponseSelector) (t : ℕ) : ℝ :=
  if S.accept t = true then S.Rprop t else S.Rbase t

/-- True value-gradient error of the response actually used. -/
def AcceptedResponseSelector.eOnline
    (S : AcceptedResponseSelector) (t : ℕ) : ℝ :=
  if S.accept t = true then S.eProp t else S.eB t

/--
Accepted uncertainty-adjusted gain.  A rejected proposal contributes exactly
zero, while an accepted proposal contributes its calibrated positive margin.
-/
def AcceptedResponseSelector.Gamma
    (S : AcceptedResponseSelector) (t : ℕ) : ℝ :=
  if S.accept t = true then
    S.DeltaHat t - S.tauE t - S.rhoProp t - S.rhoB t
  else 0

/-- The selector produces the residual safeguard system consumed by the main theorem. -/
def AcceptedResponseSelector.safeguardSystem
    (S : AcceptedResponseSelector) : ResidualSafeguardSystem where
  theta := S.theta
  R := S.R
  Rbase := S.Rbase
  Ronline := S.Ronline
  epsBase := S.epsBase
  tau := S.tauR
  Rbase_nonneg := S.Rbase_nonneg
  epsBase_nonneg := S.epsBase_nonneg
  tau_nonneg := S.tauR_nonneg
  base_contract := S.base_contract
  accepted_safe := by
    intro t
    cases hacc : S.accept t with
    | false =>
        simp [AcceptedResponseSelector.Ronline, hacc, S.tauR_nonneg t]
    | true =>
        simpa [AcceptedResponseSelector.Ronline, hacc] using
          S.proposal_residual_safe t hacc

@[simp]
theorem AcceptedResponseSelector.safeguard_Q
    (S : AcceptedResponseSelector) (t : ℕ) :
    S.safeguardSystem.Q t = S.Rbase t + S.tauR t := by
  rfl

@[simp]
theorem AcceptedResponseSelector.safeguard_eps
    (S : AcceptedResponseSelector) (t : ℕ) :
    S.safeguardSystem.eps t = S.epsBase t + S.tauR t := by
  rfl

/-- The explicit selector gives a sequence-level proxy certificate. -/
def AcceptedResponseSelector.proxySequence
    (S : AcceptedResponseSelector) : ProxyGainSequence where
  eO := S.eOnline
  eB := S.eB
  ehatO := fun t =>
    if S.accept t = true then S.ehatProp t else S.eB t
  ehatB := fun t =>
    if S.accept t = true then S.ehatB t else S.eB t
  DeltaHat := fun t =>
    if S.accept t = true then S.DeltaHat t else 0
  tauE := fun t =>
    if S.accept t = true then S.tauE t else 0
  rhoO := fun t =>
    if S.accept t = true then S.rhoProp t else 0
  rhoB := fun t =>
    if S.accept t = true then S.rhoB t else 0
  rhoO_nonneg := by
    intro t
    cases hacc : S.accept t <;>
      simp [hacc, S.rhoProp_nonneg t]
  rhoB_nonneg := by
    intro t
    cases hacc : S.accept t <;>
      simp [hacc, S.rhoB_nonneg t]
  tauE_nonneg := by
    intro t
    cases hacc : S.accept t <;>
      simp [hacc, S.tauE_nonneg t]
  calibO_abs := by
    intro t
    cases hacc : S.accept t with
    | false =>
        simp [AcceptedResponseSelector.eOnline, hacc]
    | true =>
        simpa [AcceptedResponseSelector.eOnline, hacc] using
          S.proposal_calib_abs t
  calibB_abs := by
    intro t
    cases hacc : S.accept t with
    | false =>
        simp [hacc]
    | true =>
        simpa [hacc] using S.baseline_calib_abs t
  proxy_improves := by
    intro t
    cases hacc : S.accept t with
    | false =>
        simp [hacc]
    | true =>
        simpa [hacc] using S.proposal_proxy_improves t hacc
  accepted_gain_nonneg := by
    intro t
    cases hacc : S.accept t with
    | false =>
        simp [hacc]
    | true =>
        simpa [hacc] using S.proposal_gain_nonneg t hacc

@[simp]
theorem AcceptedResponseSelector.proxy_eO
    (S : AcceptedResponseSelector) (t : ℕ) :
    S.proxySequence.eO t = S.eOnline t := by
  rfl

@[simp]
theorem AcceptedResponseSelector.proxy_Gamma
    (S : AcceptedResponseSelector) (t : ℕ) :
    S.proxySequence.Gamma t = S.Gamma t := by
  cases hacc : S.accept t <;>
    simp [AcceptedResponseSelector.proxySequence,
      AcceptedResponseSelector.Gamma, ProxyGainSequence.Gamma, hacc]

/-- Accepted proposal or fallback always improves true error by the selected gain. -/
theorem AcceptedResponseSelector.true_error_improves
    (S : AcceptedResponseSelector) (t : ℕ) :
    S.eOnline t ≤ S.eB t - S.Gamma t := by
  have h := S.proxySequence.true_error_improves t
  simpa using h

/-- Attach baseline residual control to the selected response sequence. -/
def AcceptedResponseSelector.proxyResidualCertificate
    (S : AcceptedResponseSelector) (CR : ℝ) (b : ℕ → ℝ)
    (hbaseline : ∀ t, S.eB t ≤ CR * S.safeguardSystem.Q t + b t) :
    ProxyResidualCertificate where
  toProxyGainSequence := S.proxySequence
  CR := CR
  Q := S.safeguardSystem.Q
  b := b
  baseline_bound := hbaseline

/-- The selected response satisfies the exact gain-aware R2 certificate. -/
theorem AcceptedResponseSelector.r2_certified
    (S : AcceptedResponseSelector) (CR : ℝ) (b : ℕ → ℝ)
    (hbaseline : ∀ t, S.eB t ≤ CR * S.safeguardSystem.Q t + b t)
    (t : ℕ) :
    S.eOnline t ≤ CR * S.safeguardSystem.Q t + b t - S.Gamma t := by
  have h := (S.proxyResidualCertificate CR b hbaseline).r2_certified t
  simpa using h

/--
If the inexact-gradient vector is dominated by the selected response error, the
selector generates the exact squared-error premise of the enhanced theorem.
-/
theorem AcceptedResponseSelector.certified_error_bound
    {E : Type*} [NormedAddCommGroup E]
    (S : AcceptedResponseSelector) (CR lam : ℝ) (b : ℕ → ℝ)
    (Err : ℕ → E)
    (hbaseline : ∀ t, S.eB t ≤ CR * S.safeguardSystem.Q t + b t)
    (hErr : ∀ t, ‖Err t‖ ^ 2 ≤ lam ^ 2 * S.eOnline t)
    (t : ℕ) :
    ‖Err t‖ ^ 2 ≤
      lam ^ 2 *
        (CR * S.safeguardSystem.Q t + b t - S.Gamma t) := by
  have h := (S.proxyResidualCertificate CR b hbaseline).
    certified_error_bound lam Err hErr t
  simpa using h

end

end OUSVRBLO
