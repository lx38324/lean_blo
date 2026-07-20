import OUSVRBLO.LocalSurrogate

namespace OUSVRBLO

noncomputable section

/--
A Lipschitz value-gradient map and a response-distance error bound imply the
squared residual-to-value-gradient interface used by the main theorem.
-/
theorem gradient_error_sq_le_of_lipschitz_and_error_bound
    {Y G : Type*} [PseudoMetricSpace Y] [NormedAddCommGroup G]
    (gradXH : Y → G) (xi xistar : Y)
    (L CEB R nu : ℝ) (hL : 0 ≤ L)
    (hlipschitz :
      ‖gradXH xi - gradXH xistar‖ ≤ L * dist xi xistar)
    (herror : dist xi xistar ^ 2 ≤ CEB * R + nu) :
    ‖gradXH xi - gradXH xistar‖ ^ 2 ≤
      (L ^ 2 * CEB) * R + L ^ 2 * nu := by
  have hgrad_nonneg : 0 ≤ ‖gradXH xi - gradXH xistar‖ := norm_nonneg _
  have hLdist_nonneg : 0 ≤ L * dist xi xistar :=
    mul_nonneg hL dist_nonneg
  have hlipschitz_sq :
      ‖gradXH xi - gradXH xistar‖ ^ 2 ≤
        (L * dist xi xistar) ^ 2 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left herror (sq_nonneg L)
  calc
    ‖gradXH xi - gradXH xistar‖ ^ 2
        ≤ (L * dist xi xistar) ^ 2 := hlipschitz_sq
    _ = L ^ 2 * dist xi xistar ^ 2 := by ring
    _ ≤ L ^ 2 * (CEB * R + nu) := hscaled
    _ = (L ^ 2 * CEB) * R + L ^ 2 * nu := by ring

/--
The generic response-distance argument specialized to the represented
restricted value-gradient interface.
-/
theorem RestrictedValueGradientInterface.r2_of_lipschitz_and_error_bound
    (S : RestrictedValueGradientInterface)
    [PseudoMetricSpace S.Y] [NormedAddCommGroup S.G]
    (x : S.X) (xi : S.Y) (L CEB R nu : ℝ) (hL : 0 ≤ L)
    (hlipschitz :
      ‖S.gradXH x xi - S.gradXH x (S.response x)‖ ≤
        L * dist xi (S.response x))
    (herror :
      dist xi (S.response x) ^ 2 ≤ CEB * R + nu) :
    ‖S.gradXH x xi - S.gradV x‖ ^ 2 ≤
      (L ^ 2 * CEB) * R + L ^ 2 * nu := by
  rw [S.gradient_eq_response x]
  exact gradient_error_sq_le_of_lipschitz_and_error_bound
    (S.gradXH x) xi (S.response x) L CEB R nu hL hlipschitz herror

/--
Positive quadratic growth converts the restricted objective gap into a response
distance error bound with constant `1 / modulus`.
-/
theorem RestrictedValueResponseInterface.distance_sq_le_gap_div
    (S : RestrictedValueResponseInterface) [PseudoMetricSpace S.Y]
    (modulus : ℝ) (hmodulus : 0 < modulus)
    (hqg :
      ∀ x xi, xi ∈ S.feasible x →
        modulus * dist xi (S.response x) ^ 2 ≤
          S.h x xi - S.v x)
    (x : S.X) (xi : S.Y) (hxi : xi ∈ S.feasible x) :
    dist xi (S.response x) ^ 2 ≤
      (1 / modulus) * (S.h x xi - S.v x) := by
  have hq := hqg x xi hxi
  have hscale : 0 ≤ 1 / modulus := by
    exact le_of_lt (one_div_pos.mpr hmodulus)
  have hscaled := mul_le_mul_of_nonneg_left hq hscale
  calc
    dist xi (S.response x) ^ 2
        = (1 / modulus) *
            (modulus * dist xi (S.response x) ^ 2) := by
              field_simp [ne_of_gt hmodulus]
    _ ≤ (1 / modulus) * (S.h x xi - S.v x) := hscaled

/--
Quadratic growth plus Lipschitz dependence of the upper/value gradient on the
response yields a direct objective-gap version of the R2 interface.
-/
theorem RestrictedValueGradientInterface.r2_of_quadratic_growth
    (S : RestrictedValueGradientInterface)
    [PseudoMetricSpace S.Y] [NormedAddCommGroup S.G]
    (modulus L : ℝ) (hmodulus : 0 < modulus) (hL : 0 ≤ L)
    (hqg :
      ∀ x xi, xi ∈ S.feasible x →
        modulus * dist xi (S.response x) ^ 2 ≤
          S.h x xi - S.v x)
    (x : S.X) (xi : S.Y) (hxi : xi ∈ S.feasible x)
    (hlipschitz :
      ‖S.gradXH x xi - S.gradXH x (S.response x)‖ ≤
        L * dist xi (S.response x)) :
    ‖S.gradXH x xi - S.gradV x‖ ^ 2 ≤
      (L ^ 2 / modulus) * (S.h x xi - S.v x) := by
  have herror := S.distance_sq_le_gap_div modulus hmodulus hqg x xi hxi
  have hbound := S.r2_of_lipschitz_and_error_bound
    x xi L (1 / modulus) (S.h x xi - S.v x) 0 hL hlipschitz (by
      simpa using herror)
  simpa [div_eq_mul_inv, mul_assoc] using hbound

end

end OUSVRBLO
