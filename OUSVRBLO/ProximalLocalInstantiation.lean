import OUSVRBLO.ProximalResponseCertificate
import OUSVRBLO.RestrictedValueProposalData

open scoped InnerProductSpace

namespace OUSVRBLO

noncomputable section

/--
A reusable local proximal response class that instantiates the principal
residual-to-value-gradient assumption of the certified theorem.

The represented response is stationary for the proximal lower-gradient map.
The unregularized lower gradient is locally hypomonotone, while the represented
upper/value partial gradient is Lipschitz in the response.  Proximal strength
strictly larger than the negative-curvature bound then gives an explicit
computable R2 constant.
-/
structure ProximalRestrictedValueModel
    (I : RestrictedValueGradientInterface)
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G] where
  baseGrad : I.X → I.Y → I.Y
  reference : I.X → I.Y
  rho : ℝ
  curvature : ℝ
  L : ℝ
  rho_gt_curvature : curvature < rho
  L_pos : 0 < L
  hypomonotone :
    ∀ x u w,
      -curvature * ‖u - w‖ ^ 2 ≤
        ⟪baseGrad x u - baseGrad x w, u - w⟫_ℝ
  response_stationary :
    ∀ x,
      proximalLowerGradient (baseGrad x) rho (reference x) (I.response x) = 0
  gradXH_lipschitz :
    ∀ x xi,
      ‖I.gradXH x xi - I.gradXH x (I.response x)‖ ≤
        L * ‖xi - I.response x‖

/-- Strong-monotonicity modulus created by proximal domination. -/
def ProximalRestrictedValueModel.modulus
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) : ℝ :=
  M.rho - M.curvature

/-- Explicit residual-to-value-gradient coefficient. -/
def ProximalRestrictedValueModel.CR
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) : ℝ :=
  M.L ^ 2 / M.modulus ^ 2

/-- Squared proximal lower-gradient residual. -/
def ProximalRestrictedValueModel.residual
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) (x : I.X) (xi : I.Y) : ℝ :=
  ‖proximalLowerGradient (M.baseGrad x) M.rho (M.reference x) xi‖ ^ 2

/-- Proximal domination gives a positive strong-monotonicity modulus. -/
theorem ProximalRestrictedValueModel.modulus_pos
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) :
    0 < M.modulus :=
  sub_pos.mpr M.rho_gt_curvature

/-- The explicit R2 coefficient is positive. -/
theorem ProximalRestrictedValueModel.CR_pos
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) :
    0 < M.CR := by
  dsimp [ProximalRestrictedValueModel.CR]
  exact div_pos (sq_pos_of_pos M.L_pos) (sq_pos_of_pos M.modulus_pos)

/-- The proximal residual is nonnegative. -/
theorem ProximalRestrictedValueModel.residual_nonneg
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) (x : I.X) (xi : I.Y) :
    0 ≤ M.residual x xi :=
  sq_nonneg _

/-- The represented response is the unique stationary point of the proximal
lower-gradient map inside the modeled local region. -/
theorem ProximalRestrictedValueModel.eq_response_of_stationary
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) (x : I.X) (xi : I.Y)
    (hxi :
      proximalLowerGradient (M.baseGrad x) M.rho (M.reference x) xi = 0) :
    xi = I.response x := by
  exact proximalLowerGradient_stationary_unique
    (M.baseGrad x) M.rho M.curvature (M.reference x)
    xi (I.response x) M.rho_gt_curvature (M.hypomonotone x)
    hxi (M.response_stationary x)

/-- Complete proximal instantiation of the squared residual-to-value-gradient
interface:

`||gradV(x) - gradXH(x,xi)||^2 <= CR * residual(x,xi)`.
-/
theorem ProximalRestrictedValueModel.r2
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (M : ProximalRestrictedValueModel I) (x : I.X) (xi : I.Y) :
    ‖I.gradV x - I.gradXH x xi‖ ^ 2 ≤ M.CR * M.residual x xi := by
  have hbound := value_gradient_error_sq_le_proximal_residual
    (M.baseGrad x) (I.gradXH x)
    M.rho M.curvature M.L (M.reference x) xi (I.response x)
    M.rho_gt_curvature (le_of_lt M.L_pos)
    (M.response_stationary x)
    (M.hypomonotone x xi (I.response x))
    (M.gradXH_lipschitz x xi)
  rw [I.gradient_eq_response x]
  simpa [ProximalRestrictedValueModel.CR,
    ProximalRestrictedValueModel.modulus,
    ProximalRestrictedValueModel.residual, norm_sub_rev] using hbound

/-- Sequence-level exact baseline R2 certificate for proposal data generated
from the same restricted value interface. -/
theorem RestrictedValueProposalData.baseline_error_bound_of_proximal
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (S : RestrictedValueProposalData I)
    (M : ProximalRestrictedValueModel I)
    (hRbase : ∀ t, S.Rbase t = M.residual (S.x t) (S.xiBase t))
    (t : ℕ) :
    (S.toValueGradientProposalData).eBase t ≤ M.CR * S.Rbase t := by
  have hbound := M.r2 (S.x t) (S.xiBase t)
  rw [hRbase t]
  simpa [RestrictedValueProposalData.eBase_eq] using hbound

/-- The same proximal model fills the exact public baseline interface after
possibly enlarging the common residual coefficient and adding a nonnegative
bias shared with the residual-drift certificate. -/
theorem RestrictedValueProposalData.baseline_error_bound_of_proximal_common_scale
    {I : RestrictedValueGradientInterface}
    [NormedAddCommGroup I.Y] [InnerProductSpace ℝ I.Y]
    [NormedAddCommGroup I.G]
    (S : RestrictedValueProposalData I)
    (M : ProximalRestrictedValueModel I)
    (CR : ℝ) (b : ℕ → ℝ)
    (hRbase : ∀ t, S.Rbase t = M.residual (S.x t) (S.xiBase t))
    (hCR : M.CR ≤ CR) (hb : ∀ t, 0 ≤ b t)
    (t : ℕ) :
    (S.toValueGradientProposalData).eBase t ≤ CR * S.Rbase t + b t := by
  have hexact := S.baseline_error_bound_of_proximal M hRbase t
  have hscale := mul_le_mul_of_nonneg_right hCR (S.Rbase_nonneg t)
  linarith

end

end OUSVRBLO
