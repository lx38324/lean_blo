import OUSVRBLO.ParameterBounds

namespace OUSVRBLO

noncomputable section

/-- Scalar Young inequality with an explicit positive balancing parameter. -/
theorem young_product_with_parameter
    (a s mu : ℝ) (hmu : 0 < mu) :
    a * s ≤ mu / 2 * s ^ 2 + 1 / (2 * mu) * a ^ 2 := by
  have hraw : 2 * mu * (a * s) ≤ mu ^ 2 * s ^ 2 + a ^ 2 := by
    nlinarith [sq_nonneg (mu * s - a)]
  have hscale : 0 ≤ 1 / (2 * mu) := by
    exact le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) hmu))
  have hscaled := mul_le_mul_of_nonneg_left hraw hscale
  calc
    a * s = (1 / (2 * mu)) * (2 * mu * (a * s)) := by
      field_simp [ne_of_gt hmu]
    _ ≤ (1 / (2 * mu)) * (mu ^ 2 * s ^ 2 + a ^ 2) := hscaled
    _ = mu / 2 * s ^ 2 + 1 / (2 * mu) * a ^ 2 := by
      field_simp [ne_of_gt hmu]
      ring

/--
Scalar sufficient conditions for the residual-drift recursion.

`stepNorm` represents `‖G + E‖`, `H^2 = C_R Q + b`, and `Gamma` is the
uncertainty-adjusted certified gain. The theorem checks Young's inequality,
the squared-sum estimate, and all coefficient propagation into the drift
recursion used by `CertifiedGainStepSystem`.
-/
structure CertifiedResidualDriftScalar where
  eta : ℝ
  lam : ℝ
  mu : ℝ
  LR : ℝ
  CR : ℝ
  Rnext : ℝ
  Q : ℝ
  Gsq : ℝ
  Esq : ℝ
  b : ℝ
  d : ℝ
  Gamma : ℝ
  H : ℝ
  stepNorm : ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  mu_pos : 0 < mu
  LR_nonneg : 0 ≤ LR
  CR_nonneg : 0 ≤ CR
  Gsq_nonneg : 0 ≤ Gsq
  Esq_nonneg : 0 ≤ Esq
  H_nonneg : 0 ≤ H
  stepNorm_nonneg : 0 ≤ stepNorm
  Hsq_eq : H ^ 2 = CR * Q + b
  raw_drift :
    Rnext ≤ Q
      + eta * H * stepNorm
      + LR * eta ^ 2 / 2 * stepNorm ^ 2
      + d
  step_sq_bound : stepNorm ^ 2 ≤ 2 * Gsq + 2 * Esq
  error_bound : Esq ≤ lam ^ 2 * (CR * Q + b - Gamma)

def CertifiedResidualDriftScalar.parameters
    (S : CertifiedResidualDriftScalar) : DriftParameterization where
  eta := S.eta
  lam := S.lam
  mu := S.mu
  LR := S.LR
  eta_pos := S.eta_pos
  lam_pos := S.lam_pos
  mu_pos := S.mu_pos
  LR_nonneg := S.LR_nonneg

def CertifiedResidualDriftScalar.Aeta
    (S : CertifiedResidualDriftScalar) : ℝ :=
  S.parameters.Aeta

def CertifiedResidualDriftScalar.beta
    (S : CertifiedResidualDriftScalar) : ℝ :=
  S.parameters.beta

/-- The raw residual compatibility inequality implies the certified drift
interface with the favorable `Gamma` term retained. -/
theorem CertifiedResidualDriftScalar.certified_drift
    (S : CertifiedResidualDriftScalar) :
    S.Rnext ≤
      (1 + S.CR * S.beta) * S.Q
        + 2 * S.Aeta * S.Gsq
        + S.beta * S.b
        - 2 * S.Aeta * S.lam ^ 2 * S.Gamma
        + S.d := by
  have hyoung := young_product_with_parameter S.H S.stepNorm S.mu S.mu_pos
  have heta : 0 ≤ S.eta := le_of_lt S.eta_pos
  have hyoung_scaled := mul_le_mul_of_nonneg_left hyoung heta
  have hA : 0 ≤ S.Aeta := S.parameters.Aeta_nonneg
  have hstep_scaled := mul_le_mul_of_nonneg_left S.step_sq_bound hA
  have htwoA : 0 ≤ 2 * S.Aeta := mul_nonneg (by norm_num) hA
  have herror_scaled := mul_le_mul_of_nonneg_left S.error_bound htwoA
  have hpre :
      S.Rnext ≤ S.Q
        + S.Aeta * S.stepNorm ^ 2
        + S.eta / (2 * S.mu) * S.H ^ 2
        + S.d := by
    dsimp [CertifiedResidualDriftScalar.Aeta,
      CertifiedResidualDriftScalar.parameters, DriftParameterization.Aeta]
    nlinarith [S.raw_drift, hyoung_scaled]
  dsimp [CertifiedResidualDriftScalar.Aeta,
    CertifiedResidualDriftScalar.beta,
    CertifiedResidualDriftScalar.parameters,
    DriftParameterization.Aeta, DriftParameterization.beta] at hpre hstep_scaled
      herror_scaled ⊢
  rw [S.Hsq_eq] at hpre
  nlinarith [hpre, hstep_scaled, herror_scaled]

/-- Zero-gain specialization used by the fallback-safe theorem. -/
structure SafeResidualDriftScalar where
  eta : ℝ
  lam : ℝ
  mu : ℝ
  LR : ℝ
  CR : ℝ
  Rnext : ℝ
  Q : ℝ
  Gsq : ℝ
  Esq : ℝ
  b : ℝ
  d : ℝ
  H : ℝ
  stepNorm : ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  mu_pos : 0 < mu
  LR_nonneg : 0 ≤ LR
  CR_nonneg : 0 ≤ CR
  Gsq_nonneg : 0 ≤ Gsq
  Esq_nonneg : 0 ≤ Esq
  H_nonneg : 0 ≤ H
  stepNorm_nonneg : 0 ≤ stepNorm
  Hsq_eq : H ^ 2 = CR * Q + b
  raw_drift :
    Rnext ≤ Q
      + eta * H * stepNorm
      + LR * eta ^ 2 / 2 * stepNorm ^ 2
      + d
  step_sq_bound : stepNorm ^ 2 ≤ 2 * Gsq + 2 * Esq
  error_bound : Esq ≤ lam ^ 2 * (CR * Q + b)

def SafeResidualDriftScalar.toCertified
    (S : SafeResidualDriftScalar) : CertifiedResidualDriftScalar where
  eta := S.eta
  lam := S.lam
  mu := S.mu
  LR := S.LR
  CR := S.CR
  Rnext := S.Rnext
  Q := S.Q
  Gsq := S.Gsq
  Esq := S.Esq
  b := S.b
  d := S.d
  Gamma := 0
  H := S.H
  stepNorm := S.stepNorm
  eta_pos := S.eta_pos
  lam_pos := S.lam_pos
  mu_pos := S.mu_pos
  LR_nonneg := S.LR_nonneg
  CR_nonneg := S.CR_nonneg
  Gsq_nonneg := S.Gsq_nonneg
  Esq_nonneg := S.Esq_nonneg
  H_nonneg := S.H_nonneg
  stepNorm_nonneg := S.stepNorm_nonneg
  Hsq_eq := S.Hsq_eq
  raw_drift := S.raw_drift
  step_sq_bound := S.step_sq_bound
  error_bound := by simpa using S.error_bound

def SafeResidualDriftScalar.Aeta (S : SafeResidualDriftScalar) : ℝ :=
  S.toCertified.Aeta

def SafeResidualDriftScalar.beta (S : SafeResidualDriftScalar) : ℝ :=
  S.toCertified.beta

theorem SafeResidualDriftScalar.drift
    (S : SafeResidualDriftScalar) :
    S.Rnext ≤
      (1 + S.CR * S.beta) * S.Q
        + 2 * S.Aeta * S.Gsq
        + S.beta * S.b
        + S.d := by
  simpa [SafeResidualDriftScalar.Aeta, SafeResidualDriftScalar.beta] using
    S.toCertified.certified_drift

end

end OUSVRBLO
