import OUSVRBLO.AcceptedResponseSelector
import OUSVRBLO.EndToEndCertifiedGain

open BigOperators
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/--
Highest-level theorem assumptions with an explicit learned-proposal selector.

Compared with `EndToEndCertifiedGainSystem`, this structure uses two more natural
premises:

* the baseline value-gradient error is controlled by the actual base residual
  `Rbase`, rather than by the larger envelope `Q`;
* residual smoothness starts from the residual `Ronline` of the response actually
  selected, rather than directly from `Q`.

The selector proves both replacements by monotonicity and fallback safety.
-/
structure SelectedEndToEndCertifiedGainSystem
    (E X : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  selector : AcceptedResponseSelector
  driftParameters : DriftParameterization
  CR : ℝ
  LP : ℝ
  CR_pos : 0 < CR
  theta_pos : 0 < selector.theta
  theta_le_one : selector.theta ≤ 1
  step_size : LP * driftParameters.eta ≤ 1
  small_step : CR * driftParameters.beta ≤ selector.theta / 4
  Pstar : ℝ
  P : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  G : ℕ → E
  Err : ℕ → E
  H : ℕ → ℝ
  stepNorm : ℕ → ℝ
  gradR : ℕ → X
  dx : ℕ → X
  R_nonneg : ∀ t, 0 ≤ selector.R t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  H_nonneg : ∀ t, 0 ≤ H t
  stepNorm_nonneg : ∀ t, 0 ≤ stepNorm t
  P_lower : ∀ t, Pstar ≤ P t
  baseline_error_bound :
    ∀ t, selector.eB t ≤ CR * selector.Rbase t + b t
  error_vector_bound :
    ∀ t, ‖Err t‖ ^ 2 ≤ driftParameters.lam ^ 2 * selector.eOnline t
  smooth_step :
    ∀ t,
      P (t + 1) ≤ P t
        - driftParameters.eta * ⟪G t, G t + Err t⟫_ℝ
        + LP * driftParameters.eta ^ 2 / 2 * ‖G t + Err t‖ ^ 2
  Hsq_eq :
    ∀ t, H t ^ 2 = CR * selector.safeguardSystem.Q t + b t
  residual_smooth_step_online :
    ∀ t,
      selector.R (t + 1) ≤ selector.Ronline t + ⟪gradR t, dx t⟫_ℝ
        + driftParameters.LR / 2 * ‖dx t‖ ^ 2 + d t
  residual_grad_sq_bound :
    ∀ t, ‖gradR t‖ ^ 2 ≤ CR * selector.safeguardSystem.Q t + b t
  displacement_bound :
    ∀ t, ‖dx t‖ ≤ driftParameters.eta * stepNorm t
  step_sq_bound :
    ∀ t,
      stepNorm t ^ 2 ≤ 2 * ‖G t‖ ^ 2 + 2 * ‖Err t‖ ^ 2

/-- The base-residual R2 premise implies the envelope-based premise. -/
theorem SelectedEndToEndCertifiedGainSystem.baseline_error_bound_envelope
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SelectedEndToEndCertifiedGainSystem E X) (t : ℕ) :
    S.selector.eB t ≤
      S.CR * S.selector.safeguardSystem.Q t + S.b t := by
  have hbase :
      S.selector.Rbase t ≤ S.selector.safeguardSystem.Q t := by
    simpa [AcceptedResponseSelector.safeguardSystem] using
      S.selector.safeguardSystem.base_le_envelope t
  have hscaled := mul_le_mul_of_nonneg_left hbase (le_of_lt S.CR_pos)
  nlinarith [S.baseline_error_bound t, hscaled]

/-- The selected-response residual smoothness premise implies its envelope form. -/
theorem SelectedEndToEndCertifiedGainSystem.residual_smooth_step_envelope
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SelectedEndToEndCertifiedGainSystem E X) (t : ℕ) :
    S.selector.R (t + 1) ≤
      S.selector.safeguardSystem.Q t + ⟪S.gradR t, S.dx t⟫_ℝ
        + S.driftParameters.LR / 2 * ‖S.dx t‖ ^ 2 + S.d t := by
  have honline :
      S.selector.Ronline t ≤ S.selector.safeguardSystem.Q t := by
    simpa [AcceptedResponseSelector.safeguardSystem] using
      S.selector.safeguardSystem.online_le_envelope t
  linarith [S.residual_smooth_step_online t, honline]

/-- Close the explicit selector into the previous end-to-end certificate system. -/
def SelectedEndToEndCertifiedGainSystem.toEndToEndCertifiedGainSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SelectedEndToEndCertifiedGainSystem E X) :
    EndToEndCertifiedGainSystem E X where
  safeguard := S.selector.safeguardSystem
  proxy := S.selector.proxySequence
  driftParameters := S.driftParameters
  CR := S.CR
  LP := S.LP
  CR_pos := S.CR_pos
  theta_pos := S.theta_pos
  theta_le_one := S.theta_le_one
  step_size := S.step_size
  small_step := S.small_step
  Pstar := S.Pstar
  P := S.P
  b := S.b
  d := S.d
  G := S.G
  Err := S.Err
  H := S.H
  stepNorm := S.stepNorm
  gradR := S.gradR
  dx := S.dx
  R_nonneg := S.R_nonneg
  b_nonneg := S.b_nonneg
  d_nonneg := S.d_nonneg
  H_nonneg := S.H_nonneg
  stepNorm_nonneg := S.stepNorm_nonneg
  P_lower := S.P_lower
  baseline_error_bound := S.baseline_error_bound_envelope
  error_vector_bound := by
    intro t
    simpa using S.error_vector_bound t
  smooth_step := S.smooth_step
  Hsq_eq := S.Hsq_eq
  residual_smooth_step := S.residual_smooth_step_envelope
  residual_grad_sq_bound := S.residual_grad_sq_bound
  displacement_bound := S.displacement_bound
  step_sq_bound := S.step_sq_bound

/-- Public scalar system obtained from explicit proposal/fallback selection. -/
def SelectedEndToEndCertifiedGainSystem.toCertifiedGainStepSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SelectedEndToEndCertifiedGainSystem E X) : CertifiedGainStepSystem :=
  S.toEndToEndCertifiedGainSystem.toCertifiedGainStepSystem

/-- The public gain sequence is exactly the selector's accepted gain. -/
theorem SelectedEndToEndCertifiedGainSystem.public_Gamma
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SelectedEndToEndCertifiedGainSystem E X) :
    S.toCertifiedGainStepSystem.Gamma = S.selector.Gamma := by
  funext t
  change S.selector.proxySequence.Gamma t = S.selector.Gamma t
  exact S.selector.proxy_Gamma t

/-- Exact finite-horizon theorem from explicit proposal/fallback selection. -/
theorem SelectedEndToEndCertifiedGainSystem.cumulative_budget
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SelectedEndToEndCertifiedGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + S.toCertifiedGainStepSystem.Cgain * SeqSum T S.selector.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.selector.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps *
            SeqSum T S.selector.safeguardSystem.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  simpa [SelectedEndToEndCertifiedGainSystem.toCertifiedGainStepSystem,
    SelectedEndToEndCertifiedGainSystem.toEndToEndCertifiedGainSystem,
    AcceptedResponseSelector.safeguardSystem,
    ResidualSafeguardSystem.eps, SeqSum]
    using S.toEndToEndCertifiedGainSystem.cumulative_budget T

/-- Simplified finite-horizon theorem using the checked lower gain coefficient. -/
theorem SelectedEndToEndCertifiedGainSystem.cumulative_budget_simple
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SelectedEndToEndCertifiedGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 / 2) *
          SeqSum T S.selector.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.selector.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps *
            SeqSum T S.selector.safeguardSystem.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  simpa [SelectedEndToEndCertifiedGainSystem.toCertifiedGainStepSystem,
    SelectedEndToEndCertifiedGainSystem.toEndToEndCertifiedGainSystem,
    AcceptedResponseSelector.safeguardSystem,
    ResidualSafeguardSystem.eps, SeqSum]
    using S.toEndToEndCertifiedGainSystem.cumulative_budget_simple T

end

end OUSVRBLO
