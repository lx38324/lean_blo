import OUSVRBLO.SafeguardCertificate
import OUSVRBLO.ProxySequenceCertificate
import OUSVRBLO.SmoothResidualAnalyticClosure

open BigOperators
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/--
End-to-end assumptions for the certified online value-anchor theorem.

The structure keeps the machine-learning-facing certificate objects explicit:

* `safeguard` turns a safe base response and accepted-response tolerance into the
  common residual envelope `Q` and contraction error `eps`;
* `proxy` turns an asymmetric calibrated comparison into the nonnegative true
  gain `Gamma`;
* the remaining fields are the local smoothness, response-error, residual
  smoothness, and step-control premises used by the analytic Lyapunov proof.

No one-step descent, residual recursion, or final Lyapunov coefficient bound is
assumed as an independent field.
-/
structure EndToEndCertifiedGainSystem
    (E X : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  safeguard : ResidualSafeguardSystem
  proxy : ProxyGainSequence
  driftParameters : DriftParameterization
  CR : ℝ
  LP : ℝ
  CR_pos : 0 < CR
  theta_pos : 0 < safeguard.theta
  theta_le_one : safeguard.theta ≤ 1
  step_size : LP * driftParameters.eta ≤ 1
  small_step : CR * driftParameters.beta ≤ safeguard.theta / 4
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
  R_nonneg : ∀ t, 0 ≤ safeguard.R t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  H_nonneg : ∀ t, 0 ≤ H t
  stepNorm_nonneg : ∀ t, 0 ≤ stepNorm t
  P_lower : ∀ t, Pstar ≤ P t
  baseline_error_bound :
    ∀ t, proxy.eB t ≤ CR * safeguard.Q t + b t
  error_vector_bound :
    ∀ t, ‖Err t‖ ^ 2 ≤ driftParameters.lam ^ 2 * proxy.eO t
  smooth_step :
    ∀ t,
      P (t + 1) ≤ P t
        - driftParameters.eta * ⟪G t, G t + Err t⟫_ℝ
        + LP * driftParameters.eta ^ 2 / 2 * ‖G t + Err t‖ ^ 2
  Hsq_eq : ∀ t, H t ^ 2 = CR * safeguard.Q t + b t
  residual_smooth_step :
    ∀ t,
      safeguard.R (t + 1) ≤ safeguard.Q t + ⟪gradR t, dx t⟫_ℝ
        + driftParameters.LR / 2 * ‖dx t‖ ^ 2 + d t
  residual_grad_sq_bound :
    ∀ t, ‖gradR t‖ ^ 2 ≤ CR * safeguard.Q t + b t
  displacement_bound :
    ∀ t, ‖dx t‖ ≤ driftParameters.eta * stepNorm t
  step_sq_bound :
    ∀ t,
      stepNorm t ^ 2 ≤ 2 * ‖G t‖ ^ 2 + 2 * ‖Err t‖ ^ 2

/-- Sequence-level residual/proxy certificate generated from the end-to-end
system. -/
def EndToEndCertifiedGainSystem.proxyCertificate
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X) : ProxyResidualCertificate where
  toProxyGainSequence := S.proxy
  CR := S.CR
  Q := S.safeguard.Q
  b := S.b
  baseline_bound := S.baseline_error_bound

/-- The calibrated comparison and the online-error domination produce the exact
certified squared-error inequality consumed by the gain-aware descent theorem. -/
theorem EndToEndCertifiedGainSystem.certified_error_bound
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X) (t : ℕ) :
    ‖S.Err t‖ ^ 2 ≤
      S.driftParameters.lam ^ 2 *
        (S.CR * S.safeguard.Q t + S.b t - S.proxy.Gamma t) := by
  exact S.proxyCertificate.certified_error_bound
    S.driftParameters.lam S.Err S.error_vector_bound t

/--
Close the safeguard, proxy, and residual-smoothness certificates into the
high-level analytic gain system.
-/
def EndToEndCertifiedGainSystem.toSmoothResidualAnalyticGainSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X) :
    SmoothResidualAnalyticGainSystem E X where
  driftParameters := S.driftParameters
  CR := S.CR
  theta := S.safeguard.theta
  LP := S.LP
  CR_pos := S.CR_pos
  theta_pos := S.theta_pos
  theta_le_one := S.theta_le_one
  step_size := S.step_size
  small_step := S.small_step
  Pstar := S.Pstar
  P := S.P
  R := S.safeguard.R
  Q := S.safeguard.Q
  Gamma := S.proxy.Gamma
  eps := S.safeguard.eps
  b := S.b
  d := S.d
  G := S.G
  Err := S.Err
  H := S.H
  stepNorm := S.stepNorm
  gradR := S.gradR
  dx := S.dx
  R_nonneg := S.R_nonneg
  Gamma_nonneg := S.proxy.Gamma_nonneg
  eps_nonneg := S.safeguard.eps_nonneg
  b_nonneg := S.b_nonneg
  d_nonneg := S.d_nonneg
  H_nonneg := S.H_nonneg
  stepNorm_nonneg := S.stepNorm_nonneg
  P_lower := S.P_lower
  smooth_step := S.smooth_step
  certified_error_bound := S.certified_error_bound
  Hsq_eq := S.Hsq_eq
  residual_smooth_step := S.residual_smooth_step
  residual_grad_sq_bound := S.residual_grad_sq_bound
  displacement_bound := S.displacement_bound
  step_sq_bound := S.step_sq_bound
  envelope_contraction := S.safeguard.envelope_contract

/-- Public certified-gain scalar system generated by the complete certificate
chain. -/
def EndToEndCertifiedGainSystem.toCertifiedGainStepSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X) : CertifiedGainStepSystem :=
  S.toSmoothResidualAnalyticGainSystem.toAnalyticGainSystem.toCertifiedGainStepSystem

/--
Exact finite-horizon theorem from the full certificate-facing assumptions.
The learned proposal appears only through the accepted residual and calibrated
proxy fields; all safety and gain claims are consequences of their certificates.
-/
theorem EndToEndCertifiedGainSystem.cumulative_budget
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + S.toCertifiedGainStepSystem.Cgain * SeqSum T S.proxy.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.safeguard.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps * SeqSum T S.safeguard.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  simpa [EndToEndCertifiedGainSystem.toCertifiedGainStepSystem] using
    S.toSmoothResidualAnalyticGainSystem.cumulative_budget T

/-- Conventional version using the checked lower gain coefficient
`eta * lam^2 / 2`. -/
theorem EndToEndCertifiedGainSystem.cumulative_budget_simple
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : EndToEndCertifiedGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 / 2) *
          SeqSum T S.proxy.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.safeguard.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps * SeqSum T S.safeguard.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  simpa [EndToEndCertifiedGainSystem.toCertifiedGainStepSystem] using
    S.toSmoothResidualAnalyticGainSystem.toAnalyticGainSystem.cumulative_budget_simple T

end

end OUSVRBLO
