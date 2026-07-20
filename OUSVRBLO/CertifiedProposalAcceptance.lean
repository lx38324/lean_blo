import OUSVRBLO.AcceptedResponseSelector

namespace OUSVRBLO

noncomputable section

/--
Proposal data before the accept/fallback decision is made.

The Boolean decision is computed from three certificate tests:

1. proposal residual is no larger than the base residual plus tolerance;
2. proposal proxy error improves over the baseline by the advertised margin;
3. the margin remains nonnegative after subtracting proxy tolerance and both
   calibration radii.
-/
structure CertifiedProposalData where
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
  Rbase_nonneg : ∀ t, 0 ≤ Rbase t
  epsBase_nonneg : ∀ t, 0 ≤ epsBase t
  tauR_nonneg : ∀ t, 0 ≤ tauR t
  rhoB_nonneg : ∀ t, 0 ≤ rhoB t
  rhoProp_nonneg : ∀ t, 0 ≤ rhoProp t
  tauE_nonneg : ∀ t, 0 ≤ tauE t
  base_contract :
    ∀ t, Rbase t ≤ (1 - theta) * R t + epsBase t
  proposal_calib_abs :
    ∀ t, |ehatProp t - eProp t| ≤ rhoProp t
  baseline_calib_abs :
    ∀ t, |ehatB t - eB t| ≤ rhoB t

/-- Conjunction of the three computable acceptance certificates. -/
def CertifiedProposalData.AcceptanceCondition
    (S : CertifiedProposalData) (t : ℕ) : Prop :=
  S.Rprop t ≤ S.Rbase t + S.tauR t ∧
  S.ehatProp t ≤ S.ehatB t - S.DeltaHat t + S.tauE t ∧
  0 ≤ S.DeltaHat t - S.tauE t - S.rhoProp t - S.rhoB t

/-- The actual accept/fallback decision generated from the certificates. -/
def CertifiedProposalData.accept
    (S : CertifiedProposalData) (t : ℕ) : Bool :=
  decide (S.AcceptanceCondition t)

@[simp]
theorem CertifiedProposalData.accept_eq_true_iff
    (S : CertifiedProposalData) (t : ℕ) :
    S.accept t = true ↔ S.AcceptanceCondition t := by
  simp [CertifiedProposalData.accept]

@[simp]
theorem CertifiedProposalData.accept_eq_false_iff
    (S : CertifiedProposalData) (t : ℕ) :
    S.accept t = false ↔ ¬ S.AcceptanceCondition t := by
  simp [CertifiedProposalData.accept]

/-- Certificate-generated decision packaged as the explicit selector. -/
def CertifiedProposalData.toAcceptedResponseSelector
    (S : CertifiedProposalData) : AcceptedResponseSelector where
  theta := S.theta
  R := S.R
  Rbase := S.Rbase
  Rprop := S.Rprop
  epsBase := S.epsBase
  tauR := S.tauR
  eB := S.eB
  eProp := S.eProp
  ehatB := S.ehatB
  ehatProp := S.ehatProp
  DeltaHat := S.DeltaHat
  tauE := S.tauE
  rhoB := S.rhoB
  rhoProp := S.rhoProp
  accept := S.accept
  Rbase_nonneg := S.Rbase_nonneg
  epsBase_nonneg := S.epsBase_nonneg
  tauR_nonneg := S.tauR_nonneg
  rhoB_nonneg := S.rhoB_nonneg
  rhoProp_nonneg := S.rhoProp_nonneg
  tauE_nonneg := S.tauE_nonneg
  base_contract := S.base_contract
  proposal_residual_safe := by
    intro t hacc
    exact (S.accept_eq_true_iff t).mp hacc |>.1
  proposal_calib_abs := S.proposal_calib_abs
  baseline_calib_abs := S.baseline_calib_abs
  proposal_proxy_improves := by
    intro t hacc
    exact (S.accept_eq_true_iff t).mp hacc |>.2.1
  proposal_gain_nonneg := by
    intro t hacc
    exact (S.accept_eq_true_iff t).mp hacc |>.2.2

/-- Accepted residual is the proposal residual exactly when all certificates pass. -/
theorem CertifiedProposalData.Ronline_eq_proposal_of_accept
    (S : CertifiedProposalData) (t : ℕ)
    (h : S.AcceptanceCondition t) :
    S.toAcceptedResponseSelector.Ronline t = S.Rprop t := by
  have hacc : S.accept t = true := (S.accept_eq_true_iff t).2 h
  simp [AcceptedResponseSelector.Ronline,
    CertifiedProposalData.toAcceptedResponseSelector, hacc]

/-- Failure of any certificate selects the safe base response. -/
theorem CertifiedProposalData.Ronline_eq_base_of_reject
    (S : CertifiedProposalData) (t : ℕ)
    (h : ¬ S.AcceptanceCondition t) :
    S.toAcceptedResponseSelector.Ronline t = S.Rbase t := by
  have hacc : S.accept t = false := (S.accept_eq_false_iff t).2 h
  simp [AcceptedResponseSelector.Ronline,
    CertifiedProposalData.toAcceptedResponseSelector, hacc]

/-- Rejected proposals contribute exactly zero certified gain. -/
theorem CertifiedProposalData.Gamma_eq_zero_of_reject
    (S : CertifiedProposalData) (t : ℕ)
    (h : ¬ S.AcceptanceCondition t) :
    S.toAcceptedResponseSelector.Gamma t = 0 := by
  have hacc : S.accept t = false := (S.accept_eq_false_iff t).2 h
  simp [AcceptedResponseSelector.Gamma,
    CertifiedProposalData.toAcceptedResponseSelector, hacc]

/-- Accepted proposals contribute their complete uncertainty-adjusted margin. -/
theorem CertifiedProposalData.Gamma_eq_margin_of_accept
    (S : CertifiedProposalData) (t : ℕ)
    (h : S.AcceptanceCondition t) :
    S.toAcceptedResponseSelector.Gamma t =
      S.DeltaHat t - S.tauE t - S.rhoProp t - S.rhoB t := by
  have hacc : S.accept t = true := (S.accept_eq_true_iff t).2 h
  simp [AcceptedResponseSelector.Gamma,
    CertifiedProposalData.toAcceptedResponseSelector, hacc]

end

end OUSVRBLO
