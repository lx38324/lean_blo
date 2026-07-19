import Mathlib

namespace OUSVRBLO

noncomputable section

/--
Scalar parameter package used by the public safety and certified-gain theorems.

Unlike `SafetyStepSystem`, this structure does not assume the final Lyapunov
coefficient bounds. They are derived below from the small-step condition and
the relation between the drift constants `Aeta` and `beta`.
-/
structure SafetyParameters where
  eta : ℝ
  lam : ℝ
  CR : ℝ
  theta : ℝ
  beta : ℝ
  Aeta : ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  CR_pos : 0 < CR
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  beta_nonneg : 0 ≤ beta
  Aeta_nonneg : 0 ≤ Aeta
  /-- For the manuscript choice of `Aeta` and `beta`, this follows directly
  from `beta = 2 * Aeta * lam^2 + eta / (2 * mu)`. -/
  drift_scale_le : 2 * Aeta * lam ^ 2 ≤ beta
  /-- The manuscript small-step condition `C_R * beta_eta ≤ theta / 4`. -/
  small_step : CR * beta ≤ theta / 4

/-- Lyapunov weight. -/
def SafetyParameters.alpha (P : SafetyParameters) : ℝ :=
  P.eta * P.lam ^ 2 * P.CR / P.theta

/-- Coefficient of the residual-contraction error. -/
def SafetyParameters.Ceps (P : SafetyParameters) : ℝ :=
  P.eta * P.lam ^ 2 * P.CR * (3 / 4 + 1 / P.theta)

/-- Coefficient of the value-gradient bias budget. -/
def SafetyParameters.Cb (P : SafetyParameters) : ℝ :=
  3 / 4 * P.eta * P.lam ^ 2

/-- Coefficient of the residual-drift error. -/
def SafetyParameters.Cd (P : SafetyParameters) : ℝ :=
  P.alpha

/-- Exact favorable coefficient of an uncertainty-adjusted certified gain. -/
def SafetyParameters.Cgain (P : SafetyParameters) : ℝ :=
  P.eta * P.lam ^ 2 / 2 + 2 * P.alpha * P.Aeta * P.lam ^ 2

theorem SafetyParameters.alpha_nonneg (P : SafetyParameters) :
    0 ≤ P.alpha := by
  dsimp [SafetyParameters.alpha]
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (le_of_lt P.eta_pos) (sq_nonneg P.lam))
      (le_of_lt P.CR_pos))
    (le_of_lt P.theta_pos)

/-- The small-step condition implies the gradient coefficient loss is at most
`eta / 4`. -/
theorem SafetyParameters.two_alpha_Aeta_le (P : SafetyParameters) :
    2 * P.alpha * P.Aeta ≤ P.eta / 4 := by
  have hscale₁ : 0 ≤ P.eta * P.CR / P.theta := by
    exact div_nonneg
      (mul_nonneg (le_of_lt P.eta_pos) (le_of_lt P.CR_pos))
      (le_of_lt P.theta_pos)
  have hscale₂ : 0 ≤ P.eta / P.theta := by
    exact div_nonneg (le_of_lt P.eta_pos) (le_of_lt P.theta_pos)
  calc
    2 * P.alpha * P.Aeta
        = (P.eta * P.CR / P.theta) * (2 * P.Aeta * P.lam ^ 2) := by
            dsimp [SafetyParameters.alpha]
            ring
    _ ≤ (P.eta * P.CR / P.theta) * P.beta := by
          exact mul_le_mul_of_nonneg_left P.drift_scale_le hscale₁
    _ = (P.eta / P.theta) * (P.CR * P.beta) := by ring
    _ ≤ (P.eta / P.theta) * (P.theta / 4) := by
          exact mul_le_mul_of_nonneg_left P.small_step hscale₂
    _ = P.eta / 4 := by
          field_simp [ne_of_gt P.theta_pos]

/-- Positivity of the coefficient multiplying the accepted residual envelope. -/
theorem SafetyParameters.envelope_coeff_nonneg (P : SafetyParameters) :
    0 ≤ P.eta * P.lam ^ 2 * P.CR / 2
      + P.alpha * (1 + P.CR * P.beta) := by
  have hCRbeta : 0 ≤ P.CR * P.beta :=
    mul_nonneg (le_of_lt P.CR_pos) P.beta_nonneg
  have hfirst : 0 ≤ P.eta * P.lam ^ 2 * P.CR / 2 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (le_of_lt P.eta_pos) (sq_nonneg P.lam))
        (le_of_lt P.CR_pos))
      (by norm_num)
  have hsecond : 0 ≤ P.alpha * (1 + P.CR * P.beta) := by
    exact mul_nonneg P.alpha_nonneg (by linarith)
  exact add_nonneg hfirst hsecond

/-- The residual coefficient in the Lyapunov recursion remains at least
`eta * lam^2 * C_R / 4`. -/
theorem SafetyParameters.residual_drop_coeff (P : SafetyParameters) :
    P.alpha
      - (1 - P.theta) *
        (P.eta * P.lam ^ 2 * P.CR / 2
          + P.alpha * (1 + P.CR * P.beta))
      ≥ P.eta * P.lam ^ 2 * P.CR / 4 := by
  have hCRbeta : 0 ≤ P.CR * P.beta :=
    mul_nonneg (le_of_lt P.CR_pos) P.beta_nonneg
  have hone_le : 1 - P.theta ≤ 1 := by linarith [P.theta_pos]
  have hprod_le_CRbeta :
      (1 - P.theta) * (P.CR * P.beta) ≤ P.CR * P.beta := by
    simpa using mul_le_mul_of_nonneg_right hone_le hCRbeta
  have hprod :
      (1 - P.theta) * (P.CR * P.beta) ≤ P.theta / 4 :=
    le_trans hprod_le_CRbeta P.small_step
  have hinside :
      P.theta / 4 ≤
        P.theta * (1 + P.theta) / 2
          - (1 - P.theta) * (P.CR * P.beta) := by
    nlinarith [sq_nonneg P.theta]
  calc
    P.alpha
        - (1 - P.theta) *
          (P.eta * P.lam ^ 2 * P.CR / 2
            + P.alpha * (1 + P.CR * P.beta))
        = P.alpha *
          (P.theta * (1 + P.theta) / 2
            - (1 - P.theta) * (P.CR * P.beta)) := by
              dsimp [SafetyParameters.alpha]
              field_simp [ne_of_gt P.theta_pos]
              ring
    _ ≥ P.alpha * (P.theta / 4) := by
          exact mul_le_mul_of_nonneg_left hinside P.alpha_nonneg
    _ = P.eta * P.lam ^ 2 * P.CR / 4 := by
          dsimp [SafetyParameters.alpha]
          field_simp [ne_of_gt P.theta_pos]

/-- Upper bound for the residual-contraction error coefficient. -/
theorem SafetyParameters.eps_coeff_bound (P : SafetyParameters) :
    P.eta * P.lam ^ 2 * P.CR / 2
      + P.alpha * (1 + P.CR * P.beta)
      ≤ P.Ceps := by
  have hscaled :
      P.alpha * (P.CR * P.beta)
        ≤ P.eta * P.lam ^ 2 * P.CR / 4 := by
    calc
      P.alpha * (P.CR * P.beta)
          ≤ P.alpha * (P.theta / 4) := by
              exact mul_le_mul_of_nonneg_left P.small_step P.alpha_nonneg
      _ = P.eta * P.lam ^ 2 * P.CR / 4 := by
            dsimp [SafetyParameters.alpha]
            field_simp [ne_of_gt P.theta_pos]
  calc
    P.eta * P.lam ^ 2 * P.CR / 2
        + P.alpha * (1 + P.CR * P.beta)
        = P.eta * P.lam ^ 2 * P.CR / 2
          + P.alpha + P.alpha * (P.CR * P.beta) := by ring
    _ ≤ P.eta * P.lam ^ 2 * P.CR / 2
          + P.alpha + P.eta * P.lam ^ 2 * P.CR / 4 := by
          linarith
    _ = P.Ceps := by
          dsimp [SafetyParameters.Ceps, SafetyParameters.alpha]
          field_simp [ne_of_gt P.theta_pos]
          ring

/-- Upper bound for the value-gradient bias coefficient. -/
theorem SafetyParameters.b_coeff_bound (P : SafetyParameters) :
    P.eta * P.lam ^ 2 / 2 + P.alpha * P.beta
      ≤ P.Cb := by
  have hscale : 0 ≤ P.eta * P.lam ^ 2 / P.theta := by
    exact div_nonneg
      (mul_nonneg (le_of_lt P.eta_pos) (sq_nonneg P.lam))
      (le_of_lt P.theta_pos)
  have hscaled :
      P.alpha * P.beta ≤ P.eta * P.lam ^ 2 / 4 := by
    calc
      P.alpha * P.beta
          = (P.eta * P.lam ^ 2 / P.theta) * (P.CR * P.beta) := by
              dsimp [SafetyParameters.alpha]
              ring
      _ ≤ (P.eta * P.lam ^ 2 / P.theta) * (P.theta / 4) := by
            exact mul_le_mul_of_nonneg_left P.small_step hscale
      _ = P.eta * P.lam ^ 2 / 4 := by
            field_simp [ne_of_gt P.theta_pos]
  dsimp [SafetyParameters.Cb]
  nlinarith

/-- The exact certified-gain coefficient is at least the descent contribution
`eta * lam^2 / 2`. -/
theorem SafetyParameters.Cgain_lower (P : SafetyParameters) :
    P.eta * P.lam ^ 2 / 2 ≤ P.Cgain := by
  have hterm : 0 ≤ 2 * P.alpha * P.Aeta * P.lam ^ 2 := by
    positivity
  dsimp [SafetyParameters.Cgain]
  linarith

/-- The exact certified-gain coefficient is at most
`3/4 * eta * lam^2`. -/
theorem SafetyParameters.Cgain_upper (P : SafetyParameters) :
    P.Cgain ≤ 3 / 4 * P.eta * P.lam ^ 2 := by
  have hscaled :=
    mul_le_mul_of_nonneg_right P.two_alpha_Aeta_le (sq_nonneg P.lam)
  dsimp [SafetyParameters.Cgain]
  nlinarith

/--
Young-inequality parameterization of the residual-drift constants.

The manuscript uses `mu = 1 / (sqrt 2 * lam)`. Keeping `mu` explicit gives a
slightly more general checked theorem and makes the two key facts immediate:
`Aeta ≥ 0`, `beta ≥ 0`, and `2 * Aeta * lam^2 ≤ beta`.
-/
structure DriftParameterization where
  eta : ℝ
  lam : ℝ
  mu : ℝ
  LR : ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  mu_pos : 0 < mu
  LR_nonneg : 0 ≤ LR

/-- Coefficient after applying Young's inequality to residual drift. -/
def DriftParameterization.Aeta (D : DriftParameterization) : ℝ :=
  D.eta * D.mu / 2 + D.LR * D.eta ^ 2 / 2

/-- Complete coefficient multiplying `C_R * Q + b` in residual drift. -/
def DriftParameterization.beta (D : DriftParameterization) : ℝ :=
  2 * D.Aeta * D.lam ^ 2 + D.eta / (2 * D.mu)

theorem DriftParameterization.Aeta_nonneg (D : DriftParameterization) :
    0 ≤ D.Aeta := by
  dsimp [DriftParameterization.Aeta]
  positivity

theorem DriftParameterization.beta_nonneg (D : DriftParameterization) :
    0 ≤ D.beta := by
  dsimp [DriftParameterization.beta]
  have hA := D.Aeta_nonneg
  positivity

theorem DriftParameterization.drift_scale_le (D : DriftParameterization) :
    2 * D.Aeta * D.lam ^ 2 ≤ D.beta := by
  dsimp [DriftParameterization.beta]
  have htail : 0 ≤ D.eta / (2 * D.mu) := by positivity
  linarith

/-- Build the public safety parameter package from the analytic drift
parameterization and the single small-step inequality. -/
def DriftParameterization.toSafetyParameters
    (D : DriftParameterization) (CR theta : ℝ)
    (hCR : 0 < CR) (htheta : 0 < theta) (htheta_one : theta ≤ 1)
    (hsmall : CR * D.beta ≤ theta / 4) : SafetyParameters where
  eta := D.eta
  lam := D.lam
  CR := CR
  theta := theta
  beta := D.beta
  Aeta := D.Aeta
  eta_pos := D.eta_pos
  lam_pos := D.lam_pos
  CR_pos := hCR
  theta_pos := htheta
  theta_le_one := htheta_one
  beta_nonneg := D.beta_nonneg
  Aeta_nonneg := D.Aeta_nonneg
  drift_scale_le := D.drift_scale_le
  small_step := hsmall

end

end OUSVRBLO
