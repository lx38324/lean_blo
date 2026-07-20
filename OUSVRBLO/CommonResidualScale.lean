import Mathlib

namespace OUSVRBLO

noncomputable section

/-- An affine residual scale is monotone in its coefficient and bias whenever
the residual envelope is nonnegative. -/
theorem affine_residual_scale_mono
    (Q C Cbar b bbar : ℝ)
    (hQ : 0 ≤ Q) (hC : C ≤ Cbar) (hb : b ≤ bbar) :
    C * Q + b ≤ Cbar * Q + bbar := by
  have hscaled := mul_le_mul_of_nonneg_right hC hQ
  linarith

/-- Two independently calibrated affine residual scales admit a common scale
formed by taking the maximum coefficient and maximum bias. -/
theorem two_affine_residual_scales_le_common_max
    (Q C₁ C₂ b₁ b₂ : ℝ) (hQ : 0 ≤ Q) :
    C₁ * Q + b₁ ≤ max C₁ C₂ * Q + max b₁ b₂ ∧
    C₂ * Q + b₂ ≤ max C₁ C₂ * Q + max b₁ b₂ := by
  constructor
  · exact affine_residual_scale_mono Q C₁ (max C₁ C₂) b₁ (max b₁ b₂)
      hQ (le_max_left _ _) (le_max_left _ _)
  · exact affine_residual_scale_mono Q C₂ (max C₁ C₂) b₂ (max b₁ b₂)
      hQ (le_max_right _ _) (le_max_right _ _)

/-- Sequence form used to interpret the common `C_R, b_t` notation in the main
theorem. -/
theorem two_affine_residual_scale_sequences_le_common_max
    (Q b₁ b₂ : ℕ → ℝ) (C₁ C₂ : ℝ)
    (hQ : ∀ t, 0 ≤ Q t) (t : ℕ) :
    C₁ * Q t + b₁ t ≤ max C₁ C₂ * Q t + max (b₁ t) (b₂ t) ∧
    C₂ * Q t + b₂ t ≤ max C₁ C₂ * Q t + max (b₁ t) (b₂ t) :=
  two_affine_residual_scales_le_common_max
    (Q t) C₁ C₂ (b₁ t) (b₂ t) (hQ t)

end

end OUSVRBLO
