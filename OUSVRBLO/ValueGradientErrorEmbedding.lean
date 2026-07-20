import OUSVRBLO.CertifiedProposalAcceptance

namespace OUSVRBLO

noncomputable section

/--
Raw proposal data whose true error scalars are defined by value-gradient vectors
rather than supplied as unrelated real numbers.

`gradV` is the represented restricted value gradient, while `gradBase` and
`gradProp` are the gradients induced by the safe base response and learned
proposal.  The two true errors are their squared distances from `gradV`.
-/
structure ValueGradientProposalData
    (V : Type*) [NormedAddCommGroup V] where
  theta : ℝ
  R : ℕ → ℝ
  Rbase : ℕ → ℝ
  Rprop : ℕ → ℝ
  epsBase : ℕ → ℝ
  tauR : ℕ → ℝ
  gradV : ℕ → V
  gradBase : ℕ → V
  gradProp : ℕ → V
  ehatBase : ℕ → ℝ
  ehatProp : ℕ → ℝ
  DeltaHat : ℕ → ℝ
  tauE : ℕ → ℝ
  rhoBase : ℕ → ℝ
  rhoProp : ℕ → ℝ
  Rbase_nonneg : ∀ t, 0 ≤ Rbase t
  epsBase_nonneg : ∀ t, 0 ≤ epsBase t
  tauR_nonneg : ∀ t, 0 ≤ tauR t
  rhoBase_nonneg : ∀ t, 0 ≤ rhoBase t
  rhoProp_nonneg : ∀ t, 0 ≤ rhoProp t
  tauE_nonneg : ∀ t, 0 ≤ tauE t
  base_contract :
    ∀ t, Rbase t ≤ (1 - theta) * R t + epsBase t
  proposal_calib_abs :
    ∀ t,
      |ehatProp t - ‖gradV t - gradProp t‖ ^ 2| ≤ rhoProp t
  baseline_calib_abs :
    ∀ t,
      |ehatBase t - ‖gradV t - gradBase t‖ ^ 2| ≤ rhoBase t

/-- True squared value-gradient error of the safe base response. -/
def ValueGradientProposalData.eBase
    {V : Type*} [NormedAddCommGroup V]
    (S : ValueGradientProposalData V) (t : ℕ) : ℝ :=
  ‖S.gradV t - S.gradBase t‖ ^ 2

/-- True squared value-gradient error of the learned proposal. -/
def ValueGradientProposalData.eProp
    {V : Type*} [NormedAddCommGroup V]
    (S : ValueGradientProposalData V) (t : ℕ) : ℝ :=
  ‖S.gradV t - S.gradProp t‖ ^ 2

/-- Convert vector-valued true errors into the scalar certificate data. -/
def ValueGradientProposalData.toCertifiedProposalData
    {V : Type*} [NormedAddCommGroup V]
    (S : ValueGradientProposalData V) : CertifiedProposalData where
  theta := S.theta
  R := S.R
  Rbase := S.Rbase
  Rprop := S.Rprop
  epsBase := S.epsBase
  tauR := S.tauR
  eB := S.eBase
  eProp := S.eProp
  ehatB := S.ehatBase
  ehatProp := S.ehatProp
  DeltaHat := S.DeltaHat
  tauE := S.tauE
  rhoB := S.rhoBase
  rhoProp := S.rhoProp
  Rbase_nonneg := S.Rbase_nonneg
  epsBase_nonneg := S.epsBase_nonneg
  tauR_nonneg := S.tauR_nonneg
  rhoB_nonneg := S.rhoBase_nonneg
  rhoProp_nonneg := S.rhoProp_nonneg
  tauE_nonneg := S.tauE_nonneg
  base_contract := S.base_contract
  proposal_calib_abs := by
    intro t
    simpa [ValueGradientProposalData.eProp] using S.proposal_calib_abs t
  baseline_calib_abs := by
    intro t
    simpa [ValueGradientProposalData.eBase] using S.baseline_calib_abs t

/-- Certificate-generated selector attached to the vector-gradient data. -/
def ValueGradientProposalData.selector
    {V : Type*} [NormedAddCommGroup V]
    (S : ValueGradientProposalData V) : AcceptedResponseSelector :=
  S.toCertifiedProposalData.toAcceptedResponseSelector

/-- Gradient selected by the explicit proposal/fallback decision. -/
def ValueGradientProposalData.gradOnline
    {V : Type*} [NormedAddCommGroup V]
    (S : ValueGradientProposalData V) (t : ℕ) : V :=
  if S.toCertifiedProposalData.accept t = true then
    S.gradProp t
  else S.gradBase t

/-- Signed value-gradient approximation error used in the ambient update. -/
def ValueGradientProposalData.valueGradientError
    {V : Type*} [NormedAddCommGroup V]
    (S : ValueGradientProposalData V) (t : ℕ) : V :=
  S.gradV t - S.gradOnline t

/-- The selector's online error is exactly the squared norm of the selected
value-gradient error. -/
theorem ValueGradientProposalData.selector_eOnline
    {V : Type*} [NormedAddCommGroup V]
    (S : ValueGradientProposalData V) (t : ℕ) :
    S.selector.eOnline t = ‖S.valueGradientError t‖ ^ 2 := by
  cases hacc : S.toCertifiedProposalData.accept t with
  | false =>
      simp [ValueGradientProposalData.selector,
        ValueGradientProposalData.toCertifiedProposalData,
        AcceptedResponseSelector.eOnline,
        ValueGradientProposalData.valueGradientError,
        ValueGradientProposalData.gradOnline,
        ValueGradientProposalData.eBase, hacc]
  | true =>
      simp [ValueGradientProposalData.selector,
        ValueGradientProposalData.toCertifiedProposalData,
        AcceptedResponseSelector.eOnline,
        ValueGradientProposalData.valueGradientError,
        ValueGradientProposalData.gradOnline,
        ValueGradientProposalData.eProp, hacc]

/-- Embed the signed value-gradient error into the ambient update space and
multiply by the fixed penalty parameter. -/
def ValueGradientProposalData.ambientError
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ValueGradientProposalData V)
    (lam : ℝ) (embed : V →ₗᵢ[ℝ] E) (t : ℕ) : E :=
  lam • embed (S.valueGradientError t)

/-- The ambient inexact-gradient error has exactly the expected squared norm,
not merely an assumed upper bound. -/
theorem ValueGradientProposalData.ambientError_sq
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ValueGradientProposalData V)
    (lam : ℝ) (embed : V →ₗᵢ[ℝ] E) (t : ℕ) :
    ‖S.ambientError lam embed t‖ ^ 2 =
      lam ^ 2 * S.selector.eOnline t := by
  rw [S.selector_eOnline t]
  dsimp [ValueGradientProposalData.ambientError]
  rw [norm_smul, Real.norm_eq_abs, embed.norm_map, mul_pow, sq_abs]

/-- Exact error-vector domination required by the trajectory theorem. -/
theorem ValueGradientProposalData.ambientError_bound
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ValueGradientProposalData V)
    (lam : ℝ) (embed : V →ₗᵢ[ℝ] E) (t : ℕ) :
    ‖S.ambientError lam embed t‖ ^ 2 ≤
      lam ^ 2 * S.selector.eOnline t := by
  exact (S.ambientError_sq lam embed t).le

end

end OUSVRBLO
