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
  have hden : 0 < 8 * CR * sqrtTwo * M.lam :=
    mul_pos (mul_pos (mul_pos (by norm_num) hCR) sqrtTwo_pos) M.lam_pos
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
  have hlamSq : 0 < M.lam ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt M.lam_pos)
  have hden : 0 < 8 * CR * M.lam ^ 2 * M.LR :=
    mul_pos (mul_pos (mul_pos (by norm_num) hCR) hlamSq) hLR
  have hmul := (le_div_iff₀ hden).mp hetaSq
  nlinarith

/-- If `L_R = 0`, the quadratic half of the split budget is automatic. -/
theorem ManuscriptDriftParameters.quadratic_budget_of_LR_zero
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (htheta : 0 ≤ theta) (hLR : M.LR = 0) :
    CR * (M.lam ^ 2 * M.LR * M.eta ^ 2) ≤ theta / 8 := by
  have hdiv : 0 ≤ theta / 8 := div_nonneg htheta (by norm_num)
  simpa [hLR] using hdiv

/--
A single readable upper bound on `eta` implies the manuscript small-step
condition whenever `L_R > 0`.

This is the direct formal counterpart of

`eta <= min { theta / (8 CR sqrt(2) lambda),
              sqrt (theta / (8 CR lambda^2 L_R)) }`.
-/
theorem ManuscriptDriftParameters.small_step_of_eta_le_min
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (hCR : 0 < CR) (htheta : 0 < theta) (hLR : 0 < M.LR)
    (heta :
      M.eta ≤ min
        (theta / (8 * CR * sqrtTwo * M.lam))
        (Real.sqrt (theta / (8 * CR * M.lam ^ 2 * M.LR)))) :
    CR * M.betaEta ≤ theta / 4 := by
  have hlinearEta :
      M.eta ≤ theta / (8 * CR * sqrtTwo * M.lam) :=
    heta.trans (min_le_left _ _)
  have hlinear := M.linear_budget_of_eta_bound CR theta hCR hlinearEta
  have hlamSq : 0 < M.lam ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt M.lam_pos)
  have hden : 0 < 8 * CR * M.lam ^ 2 * M.LR :=
    mul_pos (mul_pos (mul_pos (by norm_num) hCR) hlamSq) hLR
  have hradicand :
      0 ≤ theta / (8 * CR * M.lam ^ 2 * M.LR) :=
    le_of_lt (div_pos htheta hden)
  have hetaSqrt :
      M.eta ≤ Real.sqrt (theta / (8 * CR * M.lam ^ 2 * M.LR)) :=
    heta.trans (min_le_right _ _)
  have hsqrtSq := Real.sq_sqrt hradicand
  have hetaSq :
      M.eta ^ 2 ≤ theta / (8 * CR * M.lam ^ 2 * M.LR) := by
    have hetaNonneg : 0 ≤ M.eta := le_of_lt M.eta_pos
    have hsqrtNonneg :=
      Real.sqrt_nonneg (theta / (8 * CR * M.lam ^ 2 * M.LR))
    nlinarith
  have hquadratic :=
    M.quadratic_budget_of_eta_sq_bound CR theta hCR hLR hetaSq
  exact M.small_step_of_split CR theta hlinear hquadratic

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

/-- Construct the public parameter package from the single explicit `eta` bound. -/
def ManuscriptDriftParameters.toSafetyParametersOfEtaLeMin
    (M : ManuscriptDriftParameters) (CR theta : ℝ)
    (hCR : 0 < CR) (htheta : 0 < theta) (htheta_one : theta ≤ 1)
    (hLR : 0 < M.LR)
    (heta :
      M.eta ≤ min
        (theta / (8 * CR * sqrtTwo * M.lam))
        (Real.sqrt (theta / (8 * CR * M.lam ^ 2 * M.LR)))) :
    SafetyParameters :=
  M.toSafetyParameters CR theta hCR htheta htheta_one
    (M.small_step_of_eta_le_min CR theta hCR htheta hLR heta)

end

end OUSVRBLO