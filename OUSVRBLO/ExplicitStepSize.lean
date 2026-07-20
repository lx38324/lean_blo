import OUSVRBLO.ManuscriptParameters

namespace OUSVRBLO

noncomputable section

/-- A split linear/quadratic budget is a transparent sufficient condition for
the manuscript small-step inequality. -/
theorem ManuscriptDriftParameters.small_step_of_split
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (hlinear :
      CR * (sqrtTwo * M.lam * M.eta) ≤ theta / 8)
    (hquadratic :
      CR * (M.lam ^ 2 * M.LR * M.eta ^ 2) ≤ theta / 8) :
    CR * M.betaEta ≤ theta / 4 := by
  dsimp [ManuscriptDriftParameters.betaEta]
  nlinarith

/-- A direct bound on `eta` gives the linear half of the split condition. -/
theorem ManuscriptDriftParameters.linear_budget_of_eta_bound
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (hCR : 0 < CR)
    (heta :
      M.eta ≤ theta / (8 * CR * sqrtTwo * M.lam)) :
    CR * (sqrtTwo * M.lam * M.eta) ≤ theta / 8 := by
  have hden : 0 < 8 * CR * sqrtTwo * M.lam := by positivity
  have hmul := (le_div_iff₀ hden).mp heta
  nlinarith

/-- A direct bound on `eta^2` gives the quadratic half when `L_R > 0`. -/
theorem ManuscriptDriftParameters.quadratic_budget_of_eta_sq_bound
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (hCR : 0 < CR) (hLR : 0 < M.LR)
    (hetaSq :
      M.eta ^ 2 ≤
        theta / (8 * CR * M.lam ^ 2 * M.LR)) :
    CR * (M.lam ^ 2 * M.LR * M.eta ^ 2) ≤ theta / 8 := by
  have hden : 0 < 8 * CR * M.lam ^ 2 * M.LR := by positivity
  have hmul := (le_div_iff₀ hden).mp hetaSq
  nlinarith

/-- If `L_R = 0`, the quadratic half of the split budget is automatic. -/
theorem ManuscriptDriftParameters.quadratic_budget_of_LR_zero
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (htheta : 0 ≤ theta) (hLR : M.LR = 0) :
    CR * (M.lam ^ 2 * M.LR * M.eta ^ 2) ≤ theta / 8 := by
  rw [hLR]
  simp [htheta]

/-- The split condition constructs the public Lyapunov parameter package. -/
def ManuscriptDriftParameters.toSafetyParametersOfSplit
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (hCR : 0 < CR) (htheta : 0 < theta) (htheta_one : theta ≤ 1)
    (hlinear :
      CR * (sqrtTwo * M.lam * M.eta) ≤ theta / 8)
    (hquadratic :
      CR * (M.lam ^ 2 * M.LR * M.eta ^ 2) ≤ theta / 8) :
    SafetyParameters :=
  M.toSafetyParameters CR theta hCR htheta htheta_one
    (M.small_step_of_split CR theta hlinear hquadratic)

end

end OUSVRBLO
