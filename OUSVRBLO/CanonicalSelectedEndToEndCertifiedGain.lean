import OUSVRBLO.SelectedEndToEndCertifiedGain
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators
open scoped BigOperators InnerProductSpace

namespace OUSVRBLO

noncomputable section

/-- Standard squared norm estimate used to remove the abstract `step_sq_bound`. -/
theorem norm_add_sq_le_two
    {E : Type*} [NormedAddCommGroup E]
    (G Err : E) :
    ‖G + Err‖ ^ 2 ≤ 2 * ‖G‖ ^ 2 + 2 * ‖Err‖ ^ 2 := by
  have hadd := norm_add_le G Err
  have hsum_nonneg : 0 ≤ ‖G‖ + ‖Err‖ :=
    add_nonneg (norm_nonneg G) (norm_nonneg Err)
  have hleft_nonneg : 0 ≤ ‖G + Err‖ := norm_nonneg _
  have hsquare : ‖G + Err‖ ^ 2 ≤ (‖G‖ + ‖Err‖) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (‖G‖ - ‖Err‖)]

/--
Canonical highest-level assumptions.

The auxiliary scalar quantities used in Young's inequality are no longer public
fields.  They are fixed internally as

* `H_t = sqrt (CR * Q_t + b_t)`;
* `stepNorm_t = ‖G_t + Err_t‖`.

Their nonnegativity, defining square identity, and squared-sum estimate are all
proved automatically.
-/
structure CanonicalSelectedEndToEndCertifiedGainSystem
    (E X : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  selector : AcceptedResponseSelector
  driftParameters : DriftParameterization
  CR : ℝ
  LP : ℝ
  CR_pos : 0 < CR
  theta_pos : 0 < selector.theta
  theta_le_one : selector.theta ≤ 1
  step_size : LP * driftParameters.eta ≤ 1
  small_step : CR * driftParameters.beta ≤ selector.theta / 4
  Pstar : ℝ
  P : ℕ → ℝ
  b : ℕ → ℝ
  d : ℕ → ℝ
  G : ℕ → E
  Err : ℕ → E
  gradR : ℕ → X
  dx : ℕ → X
  R_nonneg : ∀ t, 0 ≤ selector.R t
  b_nonneg : ∀ t, 0 ≤ b t
  d_nonneg : ∀ t, 0 ≤ d t
  P_lower : ∀ t, Pstar ≤ P t
  baseline_error_bound :
    ∀ t, selector.eB t ≤ CR * selector.Rbase t + b t
  error_vector_bound :
    ∀ t, ‖Err t‖ ^ 2 ≤ driftParameters.lam ^ 2 * selector.eOnline t
  smooth_step :
    ∀ t,
      P (t + 1) ≤ P t
        - driftParameters.eta * ⟪G t, G t + Err t⟫_ℝ
        + LP * driftParameters.eta ^ 2 / 2 * ‖G t + Err t‖ ^ 2
  residual_smooth_step_online :
    ∀ t,
      selector.R (t + 1) ≤ selector.Ronline t + ⟪gradR t, dx t⟫_ℝ
        + driftParameters.LR / 2 * ‖dx t‖ ^ 2 + d t
  residual_grad_sq_bound :
    ∀ t,
      ‖gradR t‖ ^ 2 ≤ CR * selector.safeguardSystem.Q t + b t
  displacement_bound :
    ∀ t,
      ‖dx t‖ ≤ driftParameters.eta * ‖G t + Err t‖

/-- The residual scale inside the square root is nonnegative. -/
theorem CanonicalSelectedEndToEndCertifiedGainSystem.residual_scale_nonneg
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : CanonicalSelectedEndToEndCertifiedGainSystem E X) (t : ℕ) :
    0 ≤ S.CR * S.selector.safeguardSystem.Q t + S.b t := by
  exact add_nonneg
    (mul_nonneg (le_of_lt S.CR_pos)
      (S.selector.safeguardSystem.Q_nonneg t))
    (S.b_nonneg t)

/-- Close canonical auxiliary quantities into the explicit selector theorem. -/
def CanonicalSelectedEndToEndCertifiedGainSystem.toSelectedSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : CanonicalSelectedEndToEndCertifiedGainSystem E X) :
    SelectedEndToEndCertifiedGainSystem E X where
  selector := S.selector
  driftParameters := S.driftParameters
  CR := S.CR
  LP := S.LP
  CR_pos := S.CR_pos
  theta_pos := S.theta_pos
  theta_le_one := S.theta_le_one
  step_size := S.step_size
  small_step := S.small_step
  Pstar := S.Pstar
  P := S.P
  b := S.b
  d := S.d
  G := S.G
  Err := S.Err
  H := fun t => Real.sqrt
    (S.CR * S.selector.safeguardSystem.Q t + S.b t)
  stepNorm := fun t => ‖S.G t + S.Err t‖
  gradR := S.gradR
  dx := S.dx
  R_nonneg := S.R_nonneg
  b_nonneg := S.b_nonneg
  d_nonneg := S.d_nonneg
  H_nonneg := fun t => Real.sqrt_nonneg _
  stepNorm_nonneg := fun t => norm_nonneg _
  P_lower := S.P_lower
  baseline_error_bound := S.baseline_error_bound
  error_vector_bound := S.error_vector_bound
  smooth_step := S.smooth_step
  Hsq_eq := by
    intro t
    exact Real.sq_sqrt (S.residual_scale_nonneg t)
  residual_smooth_step_online := S.residual_smooth_step_online
  residual_grad_sq_bound := S.residual_grad_sq_bound
  displacement_bound := S.displacement_bound
  step_sq_bound := fun t => norm_add_sq_le_two (S.G t) (S.Err t)

/-- Public certified-gain system generated from the canonical top-level data. -/
def CanonicalSelectedEndToEndCertifiedGainSystem.toCertifiedGainStepSystem
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : CanonicalSelectedEndToEndCertifiedGainSystem E X) :
    CertifiedGainStepSystem :=
  S.toSelectedSystem.toCertifiedGainStepSystem

/-- Exact finite-horizon theorem with no public `H` or `stepNorm` fields. -/
theorem CanonicalSelectedEndToEndCertifiedGainSystem.cumulative_budget
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : CanonicalSelectedEndToEndCertifiedGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + S.toCertifiedGainStepSystem.Cgain * SeqSum T S.selector.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.selector.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps *
            SeqSum T S.selector.safeguardSystem.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  exact S.toSelectedSystem.cumulative_budget T

/-- Simplified gain coefficient version of the canonical finite-horizon theorem. -/
theorem CanonicalSelectedEndToEndCertifiedGainSystem.cumulative_budget_simple
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : CanonicalSelectedEndToEndCertifiedGainSystem E X) (T : ℕ) :
    (S.driftParameters.eta / 4) * SeqSum T (fun t => ‖S.G t‖ ^ 2)
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 / 2) *
          SeqSum T S.selector.Gamma
      + (S.driftParameters.eta * S.driftParameters.lam ^ 2 * S.CR / 4) *
          SeqSum T S.selector.R
      ≤ S.toCertifiedGainStepSystem.Psi 0 - S.Pstar
        + S.toCertifiedGainStepSystem.Ceps *
            SeqSum T S.selector.safeguardSystem.eps
        + S.toCertifiedGainStepSystem.Cb * SeqSum T S.b
        + S.toCertifiedGainStepSystem.Cd * SeqSum T S.d := by
  exact S.toSelectedSystem.cumulative_budget_simple T

end

end OUSVRBLO
