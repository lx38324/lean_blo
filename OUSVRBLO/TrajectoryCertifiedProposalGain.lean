import OUSVRBLO.CertifiedProposalAcceptance
import OUSVRBLO.CanonicalSelectedEndToEndCertifiedGain

open BigOperators
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/--
Trajectory-facing highest-level assumptions.

This structure removes two further pre-collected premises from the canonical
selector theorem:

* the surrogate descent inequality after substituting the update;
* the independent upper-block displacement bound.

Instead it stores the actual trajectory displacement

`z_{t+1} - z_t = -eta • (G_t + Err_t)`,

a local smoothness inequality before substitution, and a contractive continuous
linear map extracting the upper-variable displacement.  The accept/fallback
Boolean is generated from `CertifiedProposalData`, not supplied externally.
-/
structure TrajectoryCertifiedProposalGainSystem
    (E X : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  proposal : CertifiedProposalData
  driftParameters : DriftParameterization
  CR : ℝ
  LP : ℝ
  CR_pos : 0 < CR
  theta_pos : 0 < proposal.theta
  theta_le_one : proposal.theta ≤ 1
  step_size : LP * driftParameters.eta ≤ 1
  small_step : CR * driftParameters.beta ≤ proposal.theta / 4
  Pstar : ℝ
  objective : E → ℝ
  z : ℕ → E
  G : ℕ → E
  Err : ℕ → E
  projectX : E →L[ℝ] X
  gradR : ℕ → X
  b : ℕ → ℝ
  d : ℕ → ℝ
  R_nonneg : ∀ t, 0 ≤ proposal.R t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  objective_lower : ∀ t, Pstar ≤ objective (z t)
  baseline_error_bound :
    ∀ t, proposal.eB t ≤ CR * proposal.Rbase t + b t
  error_vector_bound :
    ∀ t,
      ‖Err t‖ ^ 2 ≤ driftParameters.lam ^ 2 *
        proposal.toAcceptedResponseSelector.eOnline t
  update_displacement :
    ∀ t,
      z (t + 1) - z t =
        -driftParameters.eta • (G t + Err t)
  objective_smooth_step :
    ∀ t,
      objective (z (t + 1)) ≤ objective (z t)
        + ⟪G t, z (t + 1) - z t⟫_ℝ
        + LP / 2 * ‖z (t + 1) - z t‖ ^ 2
  projectX_contract : ∀ u, ‖projectX u‖ ≤ ‖u‖
  residual_smooth_step_online :
    ∀ t,
      proposal.R (t + 1) ≤
        proposal.toAcceptedResponseSelector.Ronline t
          + ⟪gradR t, projectX (z (t + 1) - z t)⟫_ℝ
          + driftParameters.LR / 2 *
              ‖projectX (z (t + 1) - z t)‖ ^ 2
          + d t
  residual_grad_sq_bound :
    ∀ t,
      ‖gradR t‖ ^ 2 ≤
        CR * proposal.toAcceptedResponseSelector.safeguardSystem.Q t + b t

/-- The pre-substitution smoothness inequality and the actual update imply the
exact `smooth_step` premise of the canonical theorem. -/
theorem TrajectoryCertifiedProposalGainSystem.smooth_step
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) (t : ℕ) :
    S.objective (S.z (t + 1)) ≤ S.objective (S.z t)
      - S.driftParameters.eta * ⟪S.G t, S.G t + S.Err t⟫_ℝ
      + S.LP * S.driftParameters.eta ^ 2 / 2 *
          ‖S.G t + S.Err t‖ ^ 2 := by
  have hs := S.objective_smooth_step t
  rw [S.update_displacement t] at hs
  have heta : 0 ≤ S.driftParameters.eta :=
    le_of_lt S.driftParameters.eta_pos
  have hinner :
      ⟪S.G t,
        -S.driftParameters.eta • (S.G t + S.Err t)⟫_ℝ =
        -S.driftParameters.eta *
          ⟪S.G t, S.G t + S.Err t⟫_ℝ := by
    simp
  have hnorm :
      ‖-S.driftParameters.eta • (S.G t + S.Err t)‖ ^ 2 =
        S.driftParameters.eta ^ 2 * ‖S.G t + S.Err t‖ ^ 2 := by
    simp [norm_smul, abs_of_nonneg heta]
  rw [hinner, hnorm] at hs
  calc
    S.objective (S.z (t + 1))
        ≤ S.objective (S.z t)
          + (-S.driftParameters.eta *
              ⟪S.G t, S.G t + S.Err t⟫_ℝ)
          + S.LP / 2 *
              (S.driftParameters.eta ^ 2 *
                ‖S.G t + S.Err t‖ ^ 2) := hs
    _ = S.objective (S.z t)
          - S.driftParameters.eta *
              ⟪S.G t, S.G t + S.Err t⟫_ℝ
          + S.LP * S.driftParameters.eta ^ 2 / 2 *
              ‖S.G t + S.Err t‖ ^ 2 := by ring

/-- The upper-variable displacement bound follows from the trajectory update and
contractivity of the upper-block projection. -/
theorem TrajectoryCertifiedProposalGainSystem.displacement_bound
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) (t : ℕ) :
    ‖S.projectX (S.z (t + 1) - S.z t)‖ ≤
      S.driftParameters.eta * ‖S.G t + S.Err t‖ := by
  have heta : 0 ≤ S.driftParameters.eta :=
    le_of_lt S.driftParameters.eta_pos
  calc
    ‖S.projectX (S.z (t + 1) - S.z t)‖
        ≤ ‖S.z (t + 1) - S.z t‖ :=
          S.projectX_contract (S.z (t + 1) - S.z t)
    _ = ‖-S.driftParameters.eta • (S.G t + S.Err t)‖ := by
          rw [S.update_displacement t]
    _ = S.driftParameters.eta * ‖S.G t + S.Err t‖ := by
          simp [norm_smul, abs_of_nonneg heta]

/-- Package the certificate-generated selector and trajectory facts into the
canonical highest-level theorem. -/
def TrajectoryCertifiedProposalGainSystem.toCanonicalSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) :
    CanonicalSelectedEndToEndCertifiedGainSystem E X where
  selector := S.proposal.toAcceptedResponseSelector
  driftParameters := S.driftParameters
  CR := S.CR
  LP := S.LP
  CR_pos := S.CR_pos
  theta_pos := S.theta_pos
  theta_le_one := S.theta_le_one
  step_size := S.step_size
  small_step := S.small_step
  Pstar := S.Pstar
  P := fun t => S.objective (S.z t)
  b := S.b
  d := S.d
  G := S.G
  Err := S.Err
  gradR := S.gradR
  dx := fun t => S.projectX (S.z (t + 1) - S.z t)
  R_nonneg := S.R_nonneg
  b_nonneg := S.b_nonneg
  d_nonneg := S.d_nonneg
  P_lower := S.objective_lower
  baseline_error_bound := S.baseline_error_bound
  error_vector_bound := S.error_vector_bound
  smooth_step := S.smooth_step
  residual_smooth_step_online := S.residual_smooth_step_online
  residual_grad_sq_bound := S.residual_grad_sq_bound
  displacement_bound := S.displacement_bound

/-- Previous end-to-end certificate system generated from the trajectory-facing API. -/
def TrajectoryCertifiedProposalGainSystem.toEndToEndCertifiedGainSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) :
    EndToEndCertifiedGainSystem E X :=
  S.toCanonicalSystem.toSelectedSystem.toEndToEndCertifiedGainSystem

/-- Public scalar system generated from certificate data and the actual
trajectory update. -/
def TrajectoryCertifiedProposalGainSystem.toCertifiedGainStepSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) :
    CertifiedGainStepSystem :=
  S.toCanonicalSystem.toCertifiedGainStepSystem

/-- The public gain sequence is exactly the gain selected by the explicit
certificate-generated accept/fallback rule. -/
theorem TrajectoryCertifiedProposalGainSystem.public_Gamma
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) :
    S.toCertifiedGainStepSystem.Gamma =
      (S.proposal.toAcceptedResponseSelector).Gamma := by
  simpa [TrajectoryCertifiedProposalGainSystem.toCertifiedGainStepSystem] using
    S.toCanonicalSystem.toSelectedSystem.public_Gamma

/-- Exact finite-horizon theorem from the pre-substitution smoothness premise and
certificate-generated proposal decision. -/
theorem TrajectoryCertifiedProposalGainSystem.cumulative_budget
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
  exact S.toCanonicalSystem.cumulative_budget T

/-- Simplified finite-horizon theorem using the checked lower gain coefficient. -/
theorem TrajectoryCertifiedProposalGainSystem.cumulative_budget_simple
    {E X : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 / 2) *
          SeqSum T (S.proposal.toAcceptedResponseSelector).Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.proposal.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps *
            SeqSum T (S.proposal.toAcceptedResponseSelector).safeguardSystem.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  exact S.toCanonicalSystem.cumulative_budget_simple T

end

end OUSVRBLO
