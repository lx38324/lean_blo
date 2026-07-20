import OUSVRBLO.ResidualSmoothnessCertificate
import OUSVRBLO.AnalyticClosure
import OUSVRBLO.AnalyticGainClosure

open BigOperators
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/--
High-level fallback-safe assumptions in which residual drift is supplied through
local residual smoothness, squared residual-gradient control, and a displacement
bound rather than as an already-collected `raw_drift` inequality.
-/
structure SmoothResidualAnalyticSafetySystem
    (E X : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  driftParameters : DriftParameterization
  CR : ℝ
  theta : ℝ
  LP : ℝ
  CR_pos : 0 < CR
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  step_size : LP * driftParameters.eta ≤ 1
  small_step : CR * driftParameters.beta ≤ theta / 4
  Pstar : ℝ
  P : ℕ → ℝ
  R : ℕ → ℝ
  Q : ℕ → ℝ
  eps : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  G : ℕ → E
  Err : ℕ → E
  H : ℕ → ℝ
  stepNorm : ℕ → ℝ
  gradR : ℕ → X
  dx : ℕ → X
  R_nonneg : ∀ t, 0 ≤ R t
  eps_nonneg : ∀ t, 0 ≤ eps t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  H_nonneg : ∀ t, 0 ≤ H t
  stepNorm_nonneg : ∀ t, 0 ≤ stepNorm t
  P_lower : ∀ t, Pstar ≤ P t
  smooth_step :
    ∀ t,
      P (t + 1) ≤ P t
        - driftParameters.eta * ⟪G t, G t + Err t⟫_ℝ
        + LP * driftParameters.eta ^ 2 / 2 * ‖G t + Err t‖ ^ 2
  error_bound :
    ∀ t,
      ‖Err t‖ ^ 2 ≤
        driftParameters.lam ^ 2 * (CR * Q t + b t)
  Hsq_eq : ∀ t, H t ^ 2 = CR * Q t + b t
  residual_smooth_step :
    ∀ t,
      R (t + 1) ≤ Q t + ⟪gradR t, dx t⟫_ℝ
        + driftParameters.LR / 2 * ‖dx t‖ ^ 2 + d t
  residual_grad_sq_bound :
    ∀ t, ‖gradR t‖ ^ 2 ≤ CR * Q t + b t
  displacement_bound :
    ∀ t, ‖dx t‖ ≤ driftParameters.eta * stepNorm t
  step_sq_bound :
    ∀ t,
      stepNorm t ^ 2 ≤ 2 * ‖G t‖ ^ 2 + 2 * ‖Err t‖ ^ 2
  envelope_contraction :
    ∀ t, Q t ≤ (1 - theta) * R t + eps t

/-- Residual smoothness closes the high-level safety assumptions into the
analytic theorem that begins from `raw_drift`. -/
def SmoothResidualAnalyticSafetySystem.toAnalyticSafetySystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SmoothResidualAnalyticSafetySystem E X) : AnalyticSafetySystem E where
  driftParameters := S.driftParameters
  CR := S.CR
  theta := S.theta
  LP := S.LP
  CR_pos := S.CR_pos
  theta_pos := S.theta_pos
  theta_le_one := S.theta_le_one
  step_size := S.step_size
  small_step := S.small_step
  Pstar := S.Pstar
  P := S.P
  R := S.R
  Q := S.Q
  eps := S.eps
  b := S.b
  d := S.d
  G := S.G
  Err := S.Err
  H := S.H
  stepNorm := S.stepNorm
  R_nonneg := S.R_nonneg
  eps_nonneg := S.eps_nonneg
  b_nonneg := S.b_nonneg
  d_nonneg := S.d_nonneg
  H_nonneg := S.H_nonneg
  stepNorm_nonneg := S.stepNorm_nonneg
  P_lower := S.P_lower
  smooth_step := S.smooth_step
  error_bound := S.error_bound
  Hsq_eq := S.Hsq_eq
  raw_drift := by
    intro t
    exact raw_residual_drift_of_smoothness_interface
      (S.R (t + 1)) (S.Q t) S.driftParameters.eta S.driftParameters.LR
      (S.H t) (S.stepNorm t) (S.d t) S.CR (S.b t)
      (S.gradR t) (S.dx t)
      (le_of_lt S.driftParameters.eta_pos)
      S.driftParameters.LR_nonneg
      (S.H_nonneg t) (S.stepNorm_nonneg t)
      (S.Hsq_eq t) (S.residual_smooth_step t)
      (S.residual_grad_sq_bound t) (S.displacement_bound t)
  step_sq_bound := S.step_sq_bound
  envelope_contraction := S.envelope_contraction

/-- Finite-horizon safety budget directly from smooth residual assumptions. -/
theorem SmoothResidualAnalyticSafetySystem.cumulative_budget
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SmoothResidualAnalyticSafetySystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.R
      ≤ S.toAnalyticSafetySystem.toCertifiedSafetySystem.Psi 0 - S.Pstar
        + S.toAnalyticSafetySystem.toCertifiedSafetySystem.Ceps * SeqSum T S.eps
        + S.toAnalyticSafetySystem.toCertifiedSafetySystem.Cb * SeqSum T S.b
        + S.toAnalyticSafetySystem.toCertifiedSafetySystem.Cd * SeqSum T S.d := by
  exact S.toAnalyticSafetySystem.cumulative_budget T

/--
Gain-aware analogue in which the squared value-gradient error already contains
the nonnegative uncertainty-adjusted gain `Gamma`.
-/
structure SmoothResidualAnalyticGainSystem
    (E X : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  driftParameters : DriftParameterization
  CR : ℝ
  theta : ℝ
  LP : ℝ
  CR_pos : 0 < CR
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  step_size : LP * driftParameters.eta ≤ 1
  small_step : CR * driftParameters.beta ≤ theta / 4
  Pstar : ℝ
  P : ℕ → ℝ
  R : ℕ → ℝ
  Q : ℕ → ℝ
  Gamma : ℕ → ℝ
  eps : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  G : ℕ → E
  Err : ℕ → E
  H : ℕ → ℝ
  stepNorm : ℕ → ℝ
  gradR : ℕ → X
  dx : ℕ → X
  R_nonneg : ∀ t, 0 ≤ R t
  Gamma_nonneg : ∀ t, 0 ≤ Gamma t
  eps_nonneg : ∀ t, 0 ≤ eps t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  H_nonneg : ∀ t, 0 ≤ H t
  stepNorm_nonneg : ∀ t, 0 ≤ stepNorm t
  P_lower : ∀ t, Pstar ≤ P t
  smooth_step :
    ∀ t,
      P (t + 1) ≤ P t
        - driftParameters.eta * ⟪G t, G t + Err t⟫_ℝ
        + LP * driftParameters.eta ^ 2 / 2 * ‖G t + Err t‖ ^ 2
  certified_error_bound :
    ∀ t,
      ‖Err t‖ ^ 2 ≤
        driftParameters.lam ^ 2 * (CR * Q t + b t - Gamma t)
  Hsq_eq : ∀ t, H t ^ 2 = CR * Q t + b t
  residual_smooth_step :
    ∀ t,
      R (t + 1) ≤ Q t + ⟪gradR t, dx t⟫_ℝ
        + driftParameters.LR / 2 * ‖dx t‖ ^ 2 + d t
  residual_grad_sq_bound :
    ∀ t, ‖gradR t‖ ^ 2 ≤ CR * Q t + b t
  displacement_bound :
    ∀ t, ‖dx t‖ ≤ driftParameters.eta * stepNorm t
  step_sq_bound :
    ∀ t,
      stepNorm t ^ 2 ≤ 2 * ‖G t‖ ^ 2 + 2 * ‖Err t‖ ^ 2
  envelope_contraction :
    ∀ t, Q t ≤ (1 - theta) * R t + eps t

/-- Close residual smoothness into the gain-aware analytic theorem. -/
def SmoothResidualAnalyticGainSystem.toAnalyticGainSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SmoothResidualAnalyticGainSystem E X) : AnalyticGainSystem E where
  driftParameters := S.driftParameters
  CR := S.CR
  theta := S.theta
  LP := S.LP
  CR_pos := S.CR_pos
  theta_pos := S.theta_pos
  theta_le_one := S.theta_le_one
  step_size := S.step_size
  small_step := S.small_step
  Pstar := S.Pstar
  P := S.P
  R := S.R
  Q := S.Q
  Gamma := S.Gamma
  eps := S.eps
  b := S.b
  d := S.d
  G := S.G
  Err := S.Err
  H := S.H
  stepNorm := S.stepNorm
  R_nonneg := S.R_nonneg
  Gamma_nonneg := S.Gamma_nonneg
  eps_nonneg := S.eps_nonneg
  b_nonneg := S.b_nonneg
  d_nonneg := S.d_nonneg
  H_nonneg := S.H_nonneg
  stepNorm_nonneg := S.stepNorm_nonneg
  P_lower := S.P_lower
  smooth_step := S.smooth_step
  certified_error_bound := S.certified_error_bound
  Hsq_eq := S.Hsq_eq
  raw_drift := by
    intro t
    exact raw_residual_drift_of_smoothness_interface
      (S.R (t + 1)) (S.Q t) S.driftParameters.eta S.driftParameters.LR
      (S.H t) (S.stepNorm t) (S.d t) S.CR (S.b t)
      (S.gradR t) (S.dx t)
      (le_of_lt S.driftParameters.eta_pos)
      S.driftParameters.LR_nonneg
      (S.H_nonneg t) (S.stepNorm_nonneg t)
      (S.Hsq_eq t) (S.residual_smooth_step t)
      (S.residual_grad_sq_bound t) (S.displacement_bound t)
  step_sq_bound := S.step_sq_bound
  envelope_contraction := S.envelope_contraction

/-- Exact gain-aware finite-horizon budget from smooth residual assumptions. -/
theorem SmoothResidualAnalyticGainSystem.cumulative_budget
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : SmoothResidualAnalyticGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + S.toAnalyticGainSystem.toCertifiedGainStepSystem.Cgain * SeqSum T S.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.R
      ≤ S.toAnalyticGainSystem.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toAnalyticGainSystem.toCertifiedGainStepSystem.Ceps * SeqSum T S.eps
        + S.toAnalyticGainSystem.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toAnalyticGainSystem.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  exact S.toAnalyticGainSystem.cumulative_budget T

end

end OUSVRBLO
