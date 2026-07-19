import OUSVRBLO.ParameterBounds

namespace OUSVRBLO

noncomputable section

/-- The manuscript constant `sqrt 2`. -/
def sqrtTwo : ℝ := Real.sqrt 2

theorem sqrtTwo_pos : 0 < sqrtTwo := by
  dsimp [sqrtTwo]
  positivity

theorem sqrtTwo_ne_zero : sqrtTwo ≠ 0 := ne_of_gt sqrtTwo_pos

theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  dsimp [sqrtTwo]
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- Exact parameterization used in the manuscript residual-drift proof. -/
structure ManuscriptDriftParameters where
  eta : ℝ
  lam : ℝ
  LR : ℝ
  eta_pos : 0 < eta
  lam_pos : 0 < lam
  LR_nonneg : 0 ≤ LR

/-- Young parameter `mu = 1 / (sqrt 2 * lambda)`. -/
def ManuscriptDriftParameters.mu (M : ManuscriptDriftParameters) : ℝ :=
  1 / (sqrtTwo * M.lam)

/-- Manuscript coefficient following Young's inequality. -/
def ManuscriptDriftParameters.Aeta (M : ManuscriptDriftParameters) : ℝ :=
  M.eta / (2 * sqrtTwo * M.lam) + M.LR * M.eta ^ 2 / 2

/-- Manuscript residual drift coefficient. -/
def ManuscriptDriftParameters.betaEta (M : ManuscriptDriftParameters) : ℝ :=
  sqrtTwo * M.lam * M.eta + M.lam ^ 2 * M.LR * M.eta ^ 2

theorem ManuscriptDriftParameters.mu_pos (M : ManuscriptDriftParameters) :
    0 < M.mu := by
  dsimp [ManuscriptDriftParameters.mu]
  exact div_pos (by norm_num) (mul_pos sqrtTwo_pos M.lam_pos)

/-- The general Young parameterization specialized to the manuscript choice. -/
def ManuscriptDriftParameters.parameterization
    (M : ManuscriptDriftParameters) : DriftParameterization where
  eta := M.eta
  lam := M.lam
  mu := M.mu
  LR := M.LR
  eta_pos := M.eta_pos
  lam_pos := M.lam_pos
  mu_pos := M.mu_pos
  LR_nonneg := M.LR_nonneg

theorem ManuscriptDriftParameters.parameterization_Aeta
    (M : ManuscriptDriftParameters) :
    M.parameterization.Aeta = M.Aeta := by
  dsimp [ManuscriptDriftParameters.parameterization,
    ManuscriptDriftParameters.mu, ManuscriptDriftParameters.Aeta,
    DriftParameterization.Aeta]
  field_simp [sqrtTwo_ne_zero, ne_of_gt M.lam_pos]

/-- The abstract drift coefficient is exactly
`sqrt 2 * lambda * eta + lambda^2 * L_R * eta^2`. -/
theorem ManuscriptDriftParameters.parameterization_beta
    (M : ManuscriptDriftParameters) :
    M.parameterization.beta = M.betaEta := by
  rw [DriftParameterization.beta, M.parameterization_Aeta]
  dsimp [ManuscriptDriftParameters.parameterization,
    ManuscriptDriftParameters.mu, ManuscriptDriftParameters.Aeta,
    ManuscriptDriftParameters.betaEta]
  field_simp [sqrtTwo_ne_zero, ne_of_gt M.lam_pos]
  conv_rhs => rw [sqrtTwo_sq]
  ring

/-- Direct constructor from the manuscript small-step condition
`C_R * beta_eta ≤ theta / 4` to the public parameter package. -/
def ManuscriptDriftParameters.toSafetyParameters
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (hCR : 0 < CR) (htheta : 0 < theta) (htheta_one : theta ≤ 1)
    (hsmall : CR * M.betaEta ≤ theta / 4) : SafetyParameters :=
  M.parameterization.toSafetyParameters CR theta hCR htheta htheta_one (by
    rw [M.parameterization_beta]
    exact hsmall)

end

end OUSVRBLO
