import Mathlib

namespace OUSVRBLO

noncomputable section

/--
Scalar smoothness interface for the inexact-descent step.

The normed-space argument is represented by `smooth_step`; this theorem checks
the scalar algebra that drops the nonpositive step-size term.
-/
structure SmoothDescentScalar where
  eta : ℝ
  LP : ℝ
  Gsq : ℝ
  Esq : ℝ
  stepSq : ℝ
  Pnow : ℝ
  Pnext : ℝ
  eta_pos : 0 < eta
  step_nonneg : 0 ≤ stepSq
  eta_le_inv_LP : LP * eta ≤ 1
  smooth_step :
    Pnext ≤ Pnow
      - eta / 2 * Gsq
      + eta / 2 * Esq
      - eta / 2 * (1 - LP * eta) * stepSq

theorem SmoothDescentScalar.drop_nonpositive_step
    (S : SmoothDescentScalar) :
    S.Pnext ≤ S.Pnow - S.eta / 2 * S.Gsq + S.eta / 2 * S.Esq := by
  have hcoef : 0 ≤ S.eta / 2 * (1 - S.LP * S.eta) := by
    nlinarith [S.eta_pos, S.eta_le_inv_LP]
  have hterm : 0 ≤ S.eta / 2 * (1 - S.LP * S.eta) * S.stepSq := by
    exact mul_nonneg hcoef S.step_nonneg
  nlinarith [S.smooth_step, hterm]

/--
Sufficient scalar interface for converting a residual error bound into the
`CR * R + b` value-gradient error form used by the main descent theorem.
-/
structure ResidualGradientInterface where
  Lxxi : ℝ
  CEB : ℝ
  R : ℝ
  nu : ℝ
  gradErrSq : ℝ
  Lxxi_nonneg : 0 ≤ Lxxi
  CEB_nonneg : 0 ≤ CEB
  R_nonneg : 0 ≤ R
  nu_nonneg : 0 ≤ nu
  grad_lipschitz_error :
    gradErrSq ≤ Lxxi ^ 2 * (CEB * R + nu)

def ResidualGradientInterface.CR (S : ResidualGradientInterface) : ℝ :=
  S.Lxxi ^ 2 * S.CEB

def ResidualGradientInterface.b (S : ResidualGradientInterface) : ℝ :=
  S.Lxxi ^ 2 * S.nu

theorem ResidualGradientInterface.r2_bound
    (S : ResidualGradientInterface) :
    S.gradErrSq ≤ S.CR * S.R + S.b := by
  dsimp [ResidualGradientInterface.CR, ResidualGradientInterface.b]
  nlinarith [S.grad_lipschitz_error]

end

end OUSVRBLO
