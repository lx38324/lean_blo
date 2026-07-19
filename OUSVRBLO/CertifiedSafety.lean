import OUSVRBLO.ParameterBounds
import OUSVRBLO.SafetyDescent

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/--
Public fallback-safe scalar system.

The accepted-anchor residual is represented by the certificate envelope `Q`.
The system assumes only the manuscript small-step condition through
`SafetyParameters`; all final Lyapunov coefficient bounds are derived rather
than supplied as independent hypotheses.
-/
structure CertifiedSafetySystem extends SafetyParameters where
  Pstar : ℝ
  P : ℕ → ℝ
  R : ℕ → ℝ
  Q : ℕ → ℝ
  Gsq : ℕ → ℝ
  eps : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  Gsq_nonneg : ∀ t, 0 ≤ Gsq t
  R_nonneg : ∀ t, 0 ≤ R t
  eps_nonneg : ∀ t, 0 ≤ eps t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  P_lower : ∀ t, Pstar ≤ P t
  descent :
    ∀ t,
      P (t + 1) ≤ P t
        - eta / 2 * Gsq t
        + eta * lam ^ 2 / 2 * (CR * Q t + b t)
  drift :
    ∀ t,
      R (t + 1) ≤
        (1 + CR * beta) * Q t
          + 2 * Aeta * Gsq t
          + beta * b t
          + d t
  envelope_contraction :
    ∀ t, Q t ≤ (1 - theta) * R t + eps t

def CertifiedSafetySystem.Psi (S : CertifiedSafetySystem) (t : ℕ) : ℝ :=
  S.P t + S.alpha * S.R t

def CertifiedSafetySystem.Ceps (S : CertifiedSafetySystem) : ℝ :=
  S.toSafetyParameters.Ceps

def CertifiedSafetySystem.Cb (S : CertifiedSafetySystem) : ℝ :=
  S.toSafetyParameters.Cb

def CertifiedSafetySystem.Cd (S : CertifiedSafetySystem) : ℝ :=
  S.toSafetyParameters.Cd

/-- Convert the public small-step formulation to the reusable algebraic core. -/
def CertifiedSafetySystem.toStepSystem (S : CertifiedSafetySystem) :
    SafetyStepSystem where
  eta := S.eta
  lam := S.lam
  CR := S.CR
  theta := S.theta
  beta := S.beta
  Aeta := S.Aeta
  alpha := S.alpha
  Pstar := S.Pstar
  P := S.P
  R := S.R
  Rhat := S.Q
  Gsq := S.Gsq
  eps := S.eps
  b := S.b
  d := S.d
  eta_pos := S.eta_pos
  lam_pos := S.lam_pos
  CR_pos := S.CR_pos
  theta_pos := S.theta_pos
  theta_le_one := S.theta_le_one
  alpha_eq := rfl
  alpha_nonneg := S.toSafetyParameters.alpha_nonneg
  Gsq_nonneg := S.Gsq_nonneg
  R_nonneg := S.R_nonneg
  eps_nonneg := S.eps_nonneg
  b_nonneg := S.b_nonneg
  d_nonneg := S.d_nonneg
  P_lower := S.P_lower
  two_alpha_Aeta_le := S.toSafetyParameters.two_alpha_Aeta_le
  residual_drop_coeff := S.toSafetyParameters.residual_drop_coeff
  rhat_coeff_nonneg := S.toSafetyParameters.envelope_coeff_nonneg
  eps_coeff_bound := S.toSafetyParameters.eps_coeff_bound
  b_coeff_bound := S.toSafetyParameters.b_coeff_bound
  descent := S.descent
  drift := S.drift
  contraction := S.envelope_contraction

theorem CertifiedSafetySystem.Psi_lower
    (S : CertifiedSafetySystem) (t : ℕ) :
    S.Pstar ≤ S.Psi t := by
  simpa [CertifiedSafetySystem.Psi, CertifiedSafetySystem.toStepSystem,
    SafetyStepSystem.Psi] using
    SafetyStepSystem.Psi_lower S.toStepSystem t

/-- One-step fallback-safe Lyapunov descent with coefficients derived from S2. -/
theorem CertifiedSafetySystem.one_step_lyapunov
    (S : CertifiedSafetySystem) (t : ℕ) :
    S.Psi (t + 1) ≤ S.Psi t
      - S.eta / 4 * S.Gsq t
      - S.eta * S.lam ^ 2 * S.CR / 4 * S.R t
      + S.Ceps * S.eps t
      + S.Cb * S.b t
      + S.Cd * S.d t := by
  simpa [CertifiedSafetySystem.Psi, CertifiedSafetySystem.Ceps,
    CertifiedSafetySystem.Cb, CertifiedSafetySystem.Cd,
    CertifiedSafetySystem.toStepSystem, SafetyStepSystem.Psi,
    SafetyStepSystem.Ceps, SafetyStepSystem.Cb, SafetyStepSystem.Cd,
    SafetyParameters.Ceps, SafetyParameters.Cb, SafetyParameters.Cd] using
    SafetyStepSystem.one_step_lyapunov S.toStepSystem t

theorem CertifiedSafetySystem.cumulative_budget_to_time
    (S : CertifiedSafetySystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Psi T
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d := by
  simpa [CertifiedSafetySystem.Psi, CertifiedSafetySystem.Ceps,
    CertifiedSafetySystem.Cb, CertifiedSafetySystem.Cd,
    CertifiedSafetySystem.toStepSystem, SafetyStepSystem.Psi,
    SafetyStepSystem.Ceps, SafetyStepSystem.Cb, SafetyStepSystem.Cd,
    SafetyParameters.Ceps, SafetyParameters.Cb, SafetyParameters.Cd] using
    SafetyStepSystem.cumulative_budget_to_time S.toStepSystem T

/-- Finite-horizon fallback-safe stationarity and residual budget. -/
theorem CertifiedSafetySystem.cumulative_budget
    (S : CertifiedSafetySystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.Gsq
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.R
      ≤ S.Psi 0 - S.Pstar
        + S.Ceps * SeqSum T S.eps
        + S.Cb * SeqSum T S.b
        + S.Cd * SeqSum T S.d := by
  simpa [CertifiedSafetySystem.Psi, CertifiedSafetySystem.Ceps,
    CertifiedSafetySystem.Cb, CertifiedSafetySystem.Cd,
    CertifiedSafetySystem.toStepSystem, SafetyStepSystem.Psi,
    SafetyStepSystem.Ceps, SafetyStepSystem.Cb, SafetyStepSystem.Cd,
    SafetyParameters.Ceps, SafetyParameters.Cb, SafetyParameters.Cd] using
    SafetyStepSystem.cumulative_budget S.toStepSystem T

def CertifiedSafetySystem.toBudget
    (S : CertifiedSafetySystem) (T : ℕ) : SafetyBudget T :=
  S.toStepSystem.toBudget T

theorem CertifiedSafetySystem.gradient_average_bound
    (S : CertifiedSafetySystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.Gsq
      ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ)) := by
  simpa [CertifiedSafetySystem.Psi, CertifiedSafetySystem.Ceps,
    CertifiedSafetySystem.Cb, CertifiedSafetySystem.Cd,
    CertifiedSafetySystem.toStepSystem, SafetyStepSystem.Psi,
    SafetyStepSystem.Ceps, SafetyStepSystem.Cb, SafetyStepSystem.Cd,
    SafetyParameters.Ceps, SafetyParameters.Cb, SafetyParameters.Cd] using
    SafetyStepSystem.gradient_average_bound S.toStepSystem hT

theorem CertifiedSafetySystem.residual_average_bound
    (S : CertifiedSafetySystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.R
      ≤ 4 * (S.Psi 0 - S.Pstar) /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Ceps * SeqSum T S.eps /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cb * SeqSum T S.b /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
        + 4 * S.Cd * SeqSum T S.d /
          (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  simpa [CertifiedSafetySystem.Psi, CertifiedSafetySystem.Ceps,
    CertifiedSafetySystem.Cb, CertifiedSafetySystem.Cd,
    CertifiedSafetySystem.toStepSystem, SafetyStepSystem.Psi,
    SafetyStepSystem.Ceps, SafetyStepSystem.Cb, SafetyStepSystem.Cd,
    SafetyParameters.Ceps, SafetyParameters.Cb, SafetyParameters.Cd] using
    SafetyStepSystem.residual_average_bound S.toStepSystem hT

end

end OUSVRBLO
