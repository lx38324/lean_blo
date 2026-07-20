import OUSVRBLO.InexactDescent
import OUSVRBLO.ResidualDrift
import OUSVRBLO.CertifiedGainDescent

open BigOperators
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/--
Sequence-level analytic assumptions for the uncertainty-adjusted certified-gain
theorem.

The squared error premise already contains the nonnegative true gain `Gamma`.
Consequently both the smooth surrogate descent and the residual drift retain a
favorable `Gamma` contribution before the Lyapunov inequalities are combined.
-/
structure AnalyticGainSystem
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
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
  raw_drift :
    ∀ t,
      R (t + 1) ≤ Q t
        + driftParameters.eta * H t * stepNorm t
        + driftParameters.LR * driftParameters.eta ^ 2 / 2 * stepNorm t ^ 2
        + d t
  step_sq_bound :
    ∀ t,
      stepNorm t ^ 2 ≤ 2 * ‖G t‖ ^ 2 + 2 * ‖Err t‖ ^ 2
  envelope_contraction :
    ∀ t, Q t ≤ (1 - theta) * R t + eps t

/-- Public coefficient package generated from the analytic drift constants. -/
def AnalyticGainSystem.parameters
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E) : SafetyParameters :=
  S.driftParameters.toSafetyParameters S.CR S.theta S.CR_pos S.theta_pos
    S.theta_le_one S.small_step

/-- Smoothness plus the certified squared-error bound yields a surrogate descent
inequality retaining `-eta * lam^2 / 2 * Gamma`. -/
theorem AnalyticGainSystem.descent_interface
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E) (t : ℕ) :
    S.P (t + 1) ≤ S.P t
      - S.driftParameters.eta / 2 * ‖S.G t‖ ^ 2
      + S.driftParameters.eta * S.driftParameters.lam ^ 2 / 2 *
          (S.CR * S.Q t + S.b t)
      - S.driftParameters.eta * S.driftParameters.lam ^ 2 / 2 * S.Gamma t := by
  exact inexact_gradient_descent_with_certified_gain
    (S.P t) (S.P (t + 1)) S.driftParameters.eta S.LP
    S.driftParameters.lam S.CR (S.Q t) (S.b t) (S.Gamma t)
    (S.G t) (S.Err t) (le_of_lt S.driftParameters.eta_pos)
    (le_of_lt S.driftParameters.lam_pos) S.step_size (S.smooth_step t)
    (S.certified_error_bound t)

/-- The raw residual compatibility inequality yields the enhanced drift with the
favorable term `-2 * Aeta * lam^2 * Gamma`. -/
theorem AnalyticGainSystem.drift_interface
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E) (t : ℕ) :
    S.R (t + 1) ≤
      (1 + S.CR * S.driftParameters.beta) * S.Q t
        + 2 * S.driftParameters.Aeta * ‖S.G t‖ ^ 2
        + S.driftParameters.beta * S.b t
        - 2 * S.driftParameters.Aeta * S.driftParameters.lam ^ 2 * S.Gamma t
        + S.d t := by
  let D : CertifiedResidualDriftScalar where
    eta := S.driftParameters.eta
    lam := S.driftParameters.lam
    mu := S.driftParameters.mu
    LR := S.driftParameters.LR
    CR := S.CR
    Rnext := S.R (t + 1)
    Q := S.Q t
    Gsq := ‖S.G t‖ ^ 2
    Esq := ‖S.Err t‖ ^ 2
    b := S.b t
    d := S.d t
    Gamma := S.Gamma t
    H := S.H t
    stepNorm := S.stepNorm t
    eta_pos := S.driftParameters.eta_pos
    lam_pos := S.driftParameters.lam_pos
    mu_pos := S.driftParameters.mu_pos
    LR_nonneg := S.driftParameters.LR_nonneg
    CR_nonneg := le_of_lt S.CR_pos
    Gsq_nonneg := sq_nonneg ‖S.G t‖
    Esq_nonneg := sq_nonneg ‖S.Err t‖
    H_nonneg := S.H_nonneg t
    stepNorm_nonneg := S.stepNorm_nonneg t
    Hsq_eq := S.Hsq_eq t
    raw_drift := S.raw_drift t
    step_sq_bound := S.step_sq_bound t
    error_bound := S.certified_error_bound t
  simpa [D, CertifiedResidualDriftScalar.Aeta,
    CertifiedResidualDriftScalar.beta, CertifiedResidualDriftScalar.parameters]
    using D.certified_drift

/-- Close the analytic gain assumptions into the public certified-gain system. -/
def AnalyticGainSystem.toCertifiedGainStepSystem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E) : CertifiedGainStepSystem where
  toSafetyParameters := S.parameters
  Pstar := S.Pstar
  P := S.P
  R := S.R
  Q := S.Q
  Gsq := fun t => ‖S.G t‖ ^ 2
  Gamma := S.Gamma
  eps := S.eps
  b := S.b
  d := S.d
  Gsq_nonneg := fun t => sq_nonneg ‖S.G t‖
  R_nonneg := S.R_nonneg
  Gamma_nonneg := S.Gamma_nonneg
  eps_nonneg := S.eps_nonneg
  b_nonneg := S.b_nonneg
  d_nonneg := S.d_nonneg
  P_lower := S.P_lower
  certified_descent := by
    intro t
    simpa [AnalyticGainSystem.parameters,
      DriftParameterization.toSafetyParameters] using S.descent_interface t
  certified_drift := by
    intro t
    simpa [AnalyticGainSystem.parameters,
      DriftParameterization.toSafetyParameters] using S.drift_interface t
  envelope_contraction := S.envelope_contraction

/-- Exact finite-horizon certified-gain budget directly from the Hilbert-space
smoothness and raw residual assumptions. -/
theorem AnalyticGainSystem.cumulative_budget
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + S.toCertifiedGainStepSystem.Cgain * SeqSum T S.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps * SeqSum T S.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  exact S.toCertifiedGainStepSystem.cumulative_budget T

/-- Conventional simplified gain coefficient `eta * lam^2 / 2`. -/
theorem AnalyticGainSystem.cumulative_budget_simple
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : AnalyticGainSystem E) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 / 2) *
          SeqSum T S.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps * SeqSum T S.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  exact S.toCertifiedGainStepSystem.cumulative_budget_simple T

end

end OUSVRBLO
