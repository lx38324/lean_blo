import OUSVRBLO.ResponseErrorBound

namespace OUSVRBLO

noncomputable section

/--
A contractive response map gives a distance-to-fixed-point error bound in terms
of the computable fixed-point residual `dist xi (step xi)`.
-/
theorem dist_le_fixedPoint_residual_of_contraction
    {Y : Type*} [PseudoMetricSpace Y]
    (step : Y → Y) (xi xistar : Y) (q : ℝ)
    (_hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1)
    (hfixed : step xistar = xistar)
    (hcontract : ∀ u v, dist (step u) (step v) ≤ q * dist u v) :
    dist xi xistar ≤
      (1 / (1 - q)) * dist xi (step xi) := by
  have htri :
      dist xi xistar ≤ dist xi (step xi) + dist (step xi) xistar :=
    dist_triangle xi (step xi) xistar
  have hstep : dist (step xi) xistar ≤ q * dist xi xistar := by
    calc
      dist (step xi) xistar = dist (step xi) (step xistar) := by rw [hfixed]
      _ ≤ q * dist xi xistar := hcontract xi xistar
  have hraw :
      dist xi xistar ≤ dist xi (step xi) + q * dist xi xistar :=
    htri.trans (add_le_add le_rfl hstep)
  have hlinear :
      (1 - q) * dist xi xistar ≤ dist xi (step xi) := by
    linarith
  have hgap_pos : 0 < 1 - q := sub_pos.mpr hq_lt_one
  have hscale : 0 ≤ 1 / (1 - q) :=
    le_of_lt (one_div_pos.mpr hgap_pos)
  have hscaled := mul_le_mul_of_nonneg_left hlinear hscale
  calc
    dist xi xistar
        = (1 / (1 - q)) * ((1 - q) * dist xi xistar) := by
            field_simp [ne_of_gt hgap_pos]
    _ ≤ (1 / (1 - q)) * dist xi (step xi) := hscaled

/-- Squared fixed-point residual version of the contraction error bound. -/
theorem dist_sq_le_fixedPoint_residual_sq_of_contraction
    {Y : Type*} [PseudoMetricSpace Y]
    (step : Y → Y) (xi xistar : Y) (q : ℝ)
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1)
    (hfixed : step xistar = xistar)
    (hcontract : ∀ u v, dist (step u) (step v) ≤ q * dist u v) :
    dist xi xistar ^ 2 ≤
      (1 / (1 - q) ^ 2) * dist xi (step xi) ^ 2 := by
  have hdist := dist_le_fixedPoint_residual_of_contraction
    step xi xistar q hq_nonneg hq_lt_one hfixed hcontract
  have hgap_pos : 0 < 1 - q := sub_pos.mpr hq_lt_one
  have hright_nonneg :
      0 ≤ (1 / (1 - q)) * dist xi (step xi) :=
    mul_nonneg (le_of_lt (one_div_pos.mpr hgap_pos)) dist_nonneg
  have hsquare :
      dist xi xistar ^ 2 ≤
        ((1 / (1 - q)) * dist xi (step xi)) ^ 2 := by
    nlinarith [dist_nonneg (x := xi) (y := xistar)]
  calc
    dist xi xistar ^ 2
        ≤ ((1 / (1 - q)) * dist xi (step xi)) ^ 2 := hsquare
    _ = (1 / (1 - q) ^ 2) * dist xi (step xi) ^ 2 := by
          field_simp [ne_of_gt hgap_pos]

/-- A contraction has at most one fixed point. -/
theorem eq_of_contraction_fixedPoints
    {Y : Type*} [MetricSpace Y]
    (step : Y → Y) (x y : Y) (q : ℝ)
    (_hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1)
    (hx : step x = x) (hy : step y = y)
    (hcontract : ∀ u v, dist (step u) (step v) ≤ q * dist u v) :
    x = y := by
  have hdist : dist x y ≤ q * dist x y := by
    calc
      dist x y = dist (step x) (step y) := by rw [hx, hy]
      _ ≤ q * dist x y := hcontract x y
  have hzero : dist x y = 0 := by
    have hnonneg : 0 ≤ dist x y := dist_nonneg
    nlinarith
  exact dist_eq_zero.mp hzero

/--
A contractive projected/proximal response step plus response-Lipschitzness of the
upper/value gradient gives R2 with constant `L^2 / (1-q)^2` and residual
`dist xi (step xi)^2`.
-/
theorem value_gradient_error_sq_le_fixedPoint_residual
    {Y G : Type*}
    [PseudoMetricSpace Y] [NormedAddCommGroup G]
    (step : Y → Y) (upperGrad : Y → G)
    (xi xistar : Y) (q L : ℝ)
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) (hL : 0 ≤ L)
    (hfixed : step xistar = xistar)
    (hcontract : ∀ u v, dist (step u) (step v) ≤ q * dist u v)
    (hlipschitz :
      ‖upperGrad xi - upperGrad xistar‖ ≤ L * dist xi xistar) :
    ‖upperGrad xi - upperGrad xistar‖ ^ 2 ≤
      (L ^ 2 / (1 - q) ^ 2) * dist xi (step xi) ^ 2 := by
  have herror := dist_sq_le_fixedPoint_residual_sq_of_contraction
    step xi xistar q hq_nonneg hq_lt_one hfixed hcontract
  have herror' :
      dist xi xistar ^ 2 ≤
        (1 / (1 - q) ^ 2) * dist xi (step xi) ^ 2 + 0 := by
    simpa using herror
  have hbound := gradient_error_sq_le_of_lipschitz_and_error_bound
    upperGrad xi xistar L (1 / (1 - q) ^ 2)
      (dist xi (step xi) ^ 2) 0 hL hlipschitz herror'
  simpa [div_eq_mul_inv, mul_assoc] using hbound

end

end OUSVRBLO
