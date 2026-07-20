import OUSVRBLO.ResidualDrift
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace

namespace OUSVRBLO

noncomputable section

/--
Local residual smoothness, a residual-gradient norm bound, and a displacement
bound imply the raw residual-compatibility inequality used by the main theorem.
-/
theorem raw_residual_drift_of_smoothness
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (Rnext Q eta LR H stepNorm d : ℝ) (gradR dx : X)
    (heta : 0 ≤ eta) (hLR : 0 ≤ LR)
    (hH : 0 ≤ H) (hstepNorm : 0 ≤ stepNorm)
    (hsmooth :
      Rnext ≤ Q + ⟪gradR, dx⟫_ℝ + LR / 2 * ‖dx‖ ^ 2 + d)
    (hgrad : ‖gradR‖ ≤ H)
    (hstep : ‖dx‖ ≤ eta * stepNorm) :
    Rnext ≤ Q + eta * H * stepNorm
      + LR * eta ^ 2 / 2 * stepNorm ^ 2 + d := by
  have hinner := real_inner_le_norm gradR dx
  have hstep_rhs : 0 ≤ eta * stepNorm := mul_nonneg heta hstepNorm
  have hprod :
      ‖gradR‖ * ‖dx‖ ≤ H * (eta * stepNorm) :=
    mul_le_mul hgrad hstep (norm_nonneg dx) hH
  have hcross : ⟪gradR, dx⟫_ℝ ≤ eta * H * stepNorm := by
    calc
      ⟪gradR, dx⟫_ℝ ≤ ‖gradR‖ * ‖dx‖ := hinner
      _ ≤ H * (eta * stepNorm) := hprod
      _ = eta * H * stepNorm := by ring
  have hsq : ‖dx‖ ^ 2 ≤ (eta * stepNorm) ^ 2 := by
    nlinarith [norm_nonneg dx, hstep_rhs]
  have hLRhalf : 0 ≤ LR / 2 := div_nonneg hLR (by norm_num)
  have hquad_scaled := mul_le_mul_of_nonneg_left hsq hLRhalf
  have hquad :
      LR / 2 * ‖dx‖ ^ 2 ≤ LR * eta ^ 2 / 2 * stepNorm ^ 2 := by
    calc
      LR / 2 * ‖dx‖ ^ 2
          ≤ LR / 2 * (eta * stepNorm) ^ 2 := hquad_scaled
      _ = LR * eta ^ 2 / 2 * stepNorm ^ 2 := by ring
  linarith

/--
Specialization in which the displacement is exactly a nonnegative scalar times
a step vector.
-/
theorem raw_residual_drift_of_smoothness_step
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (Rnext Q eta LR H d : ℝ) (gradR step : X)
    (heta : 0 ≤ eta) (hLR : 0 ≤ LR) (hH : 0 ≤ H)
    (hsmooth :
      Rnext ≤ Q + ⟪gradR, -eta • step⟫_ℝ
        + LR / 2 * ‖-eta • step‖ ^ 2 + d)
    (hgrad : ‖gradR‖ ≤ H) :
    Rnext ≤ Q + eta * H * ‖step‖
      + LR * eta ^ 2 / 2 * ‖step‖ ^ 2 + d := by
  apply raw_residual_drift_of_smoothness
    Rnext Q eta LR H ‖step‖ d gradR (-eta • step)
    heta hLR hH (norm_nonneg step) hsmooth hgrad
  simp [norm_smul, abs_of_nonneg heta]

/--
Sequence-level sufficient conditions for the raw residual drift in
`AnalyticSafetySystem` and `AnalyticGainSystem`.
-/
structure ResidualSmoothnessSystem
    (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  eta : ℝ
  LR : ℝ
  Rnext : ℕ → ℝ
  Q : ℕ → ℝ
  H : ℕ → ℝ
  stepNorm : ℕ → ℝ
  d : ℕ → ℝ
  gradR : ℕ → X
  dx : ℕ → X
  eta_nonneg : 0 ≤ eta
  LR_nonneg : 0 ≤ LR
  H_nonneg : ∀ t, 0 ≤ H t
  stepNorm_nonneg : ∀ t, 0 ≤ stepNorm t
  residual_smooth_step :
    ∀ t,
      Rnext t ≤ Q t + ⟪gradR t, dx t⟫_ℝ
        + LR / 2 * ‖dx t‖ ^ 2 + d t
  residual_grad_bound : ∀ t, ‖gradR t‖ ≤ H t
  displacement_bound : ∀ t, ‖dx t‖ ≤ eta * stepNorm t

/-- The smooth residual system produces the exact raw drift interface. -/
theorem ResidualSmoothnessSystem.raw_drift
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ResidualSmoothnessSystem X) (t : ℕ) :
    S.Rnext t ≤ S.Q t + S.eta * S.H t * S.stepNorm t
      + S.LR * S.eta ^ 2 / 2 * S.stepNorm t ^ 2 + S.d t := by
  exact raw_residual_drift_of_smoothness
    (S.Rnext t) (S.Q t) S.eta S.LR (S.H t) (S.stepNorm t) (S.d t)
    (S.gradR t) (S.dx t) S.eta_nonneg S.LR_nonneg
    (S.H_nonneg t) (S.stepNorm_nonneg t)
    (S.residual_smooth_step t) (S.residual_grad_bound t)
    (S.displacement_bound t)

end

end OUSVRBLO
