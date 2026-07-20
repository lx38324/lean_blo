import OUSVRBLO.JointCertificates
import OUSVRBLO.TrajectoryGradientSemantics

open BigOperators Filter Topology
open scoped BigOperators InnerProductSpace Gradient

namespace OUSVRBLO

noncomputable section

/-- Arithmetic average over the first `T` sequence entries. -/
def CesaroAverage (a : ℕ → ℝ) (T : ℕ) : ℝ :=
  (1 / (T : ℝ)) * SeqSum T a

/-- A nonnegative sequence has a nonnegative finite arithmetic average. -/
theorem CesaroAverage_nonneg
    (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (T : ℕ) :
    0 ≤ CesaroAverage a T := by
  have hsum : 0 ≤ SeqSum T a := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => ha t)
  exact mul_nonneg (by positivity) hsum

/-- Normalized perturbation upper bound used by the certified-gain system. -/
def CertifiedGainStepSystem.cesaroRhs
    (S : CertifiedGainStepSystem) (T : ℕ) : ℝ :=
  (4 * (S.Psi 0 - S.Pstar) / S.eta) / (T : ℝ)
    + (4 * S.Ceps / S.eta) * CesaroAverage S.eps T
    + (4 * S.Cb / S.eta) * CesaroAverage S.b T
    + (4 * S.Cd / S.eta) * CesaroAverage S.d T

/-- The finite-horizon joint bound written directly in Cesaro-average form. -/
theorem CertifiedGainStepSystem.joint_average_le_cesaroRhs
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    CesaroAverage S.jointMeasure T ≤ S.cesaroRhs T := by
  have hbase := S.joint_average_bound hT
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  calc
    CesaroAverage S.jointMeasure T
        ≤ 4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by
          simpa [CesaroAverage] using hbase
    _ = S.cesaroRhs T := by
      dsimp [CertifiedGainStepSystem.accumulatedRhs,
        CertifiedGainStepSystem.cesaroRhs, CesaroAverage]
      field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]
      ring

/-- If all perturbation averages vanish, the normalized certified-gain right-hand
side vanishes even when the perturbations are not summable. -/
theorem CertifiedGainStepSystem.cesaroRhs_tendsto_zero
    (S : CertifiedGainStepSystem)
    (heps : Tendsto (CesaroAverage S.eps) atTop (𝓝 0))
    (hb : Tendsto (CesaroAverage S.b) atTop (𝓝 0))
    (hd : Tendsto (CesaroAverage S.d) atTop (𝓝 0)) :
    Tendsto S.cesaroRhs atTop (𝓝 0) := by
  have hgap :
      Tendsto
        (fun T : ℕ => (4 * (S.Psi 0 - S.Pstar) / S.eta) / (T : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat
      (4 * (S.Psi 0 - S.Pstar) / S.eta)
  have heps' :
      Tendsto
        (fun T : ℕ => (4 * S.Ceps / S.eta) * CesaroAverage S.eps T)
        atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => 4 * S.Ceps / S.eta) atTop
          (𝓝 (4 * S.Ceps / S.eta)) := tendsto_const_nhds
    simpa using hconst.mul heps
  have hb' :
      Tendsto
        (fun T : ℕ => (4 * S.Cb / S.eta) * CesaroAverage S.b T)
        atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => 4 * S.Cb / S.eta) atTop
          (𝓝 (4 * S.Cb / S.eta)) := tendsto_const_nhds
    simpa using hconst.mul hb
  have hd' :
      Tendsto
        (fun T : ℕ => (4 * S.Cd / S.eta) * CesaroAverage S.d T)
        atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => 4 * S.Cd / S.eta) atTop
          (𝓝 (4 * S.Cd / S.eta)) := tendsto_const_nhds
    simpa using hconst.mul hd
  simpa [CertifiedGainStepSystem.cesaroRhs] using
    ((hgap.add heps').add hb').add hd'

/-- Vanishing perturbation averages imply vanishing average joint
stationarity/residual performance.  No summability premise is required. -/
theorem CertifiedGainStepSystem.joint_average_tendsto_zero_of_cesaro
    (S : CertifiedGainStepSystem)
    (heps : Tendsto (CesaroAverage S.eps) atTop (𝓝 0))
    (hb : Tendsto (CesaroAverage S.b) atTop (𝓝 0))
    (hd : Tendsto (CesaroAverage S.d) atTop (𝓝 0)) :
    Tendsto (CesaroAverage S.jointMeasure) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      CesaroAverage_nonneg S.jointMeasure (fun t => by
        exact add_nonneg (S.Gsq_nonneg t)
          (mul_nonneg
            (mul_nonneg (sq_nonneg S.lam) (le_of_lt S.CR_pos))
            (S.R_nonneg t))) T
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    exact S.joint_average_le_cesaroRhs hT
  · exact S.cesaroRhs_tendsto_zero heps hb hd

/-- The average squared stationarity measure vanishes under Cesaro-vanishing
perturbations. -/
theorem CertifiedGainStepSystem.gradient_average_tendsto_zero_of_cesaro
    (S : CertifiedGainStepSystem)
    (heps : Tendsto (CesaroAverage S.eps) atTop (𝓝 0))
    (hb : Tendsto (CesaroAverage S.b) atTop (𝓝 0))
    (hd : Tendsto (CesaroAverage S.d) atTop (𝓝 0)) :
    Tendsto (CesaroAverage S.Gsq) atTop (𝓝 0) := by
  have hjoint := S.joint_average_tendsto_zero_of_cesaro heps hb hd
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      CesaroAverage_nonneg S.Gsq S.Gsq_nonneg T
  · exact Filter.Eventually.of_forall fun T => by
      have hRavg : 0 ≤ CesaroAverage S.R T :=
        CesaroAverage_nonneg S.R S.R_nonneg T
      have hRterm :
          0 ≤ S.lam ^ 2 * S.CR * CesaroAverage S.R T :=
        mul_nonneg
          (mul_nonneg (sq_nonneg S.lam) (le_of_lt S.CR_pos)) hRavg
      have heq := S.joint_average_eq T
      change CesaroAverage S.jointMeasure T =
        CesaroAverage S.Gsq T
          + S.lam ^ 2 * S.CR * CesaroAverage S.R T at heq
      rw [heq]
      exact le_add_of_nonneg_right hRterm
  · exact hjoint

/-- The average response residual also vanishes under Cesaro-vanishing
perturbations. -/
theorem CertifiedGainStepSystem.residual_average_tendsto_zero_of_cesaro
    (S : CertifiedGainStepSystem)
    (heps : Tendsto (CesaroAverage S.eps) atTop (𝓝 0))
    (hb : Tendsto (CesaroAverage S.b) atTop (𝓝 0))
    (hd : Tendsto (CesaroAverage S.d) atTop (𝓝 0)) :
    Tendsto (CesaroAverage S.R) atTop (𝓝 0) := by
  have hjoint := S.joint_average_tendsto_zero_of_cesaro heps hb hd
  have hlamSq : 0 < S.lam ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt S.lam_pos)
  have hcoef : 0 < S.lam ^ 2 * S.CR :=
    mul_pos hlamSq S.CR_pos
  have hupperTendsto :
      Tendsto
        (fun T : ℕ =>
          (1 / (S.lam ^ 2 * S.CR)) * CesaroAverage S.jointMeasure T)
        atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => 1 / (S.lam ^ 2 * S.CR)) atTop
          (𝓝 (1 / (S.lam ^ 2 * S.CR))) := tendsto_const_nhds
    simpa using hconst.mul hjoint
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      CesaroAverage_nonneg S.R S.R_nonneg T
  · exact Filter.Eventually.of_forall fun T => by
      have hGavg : 0 ≤ CesaroAverage S.Gsq T :=
        CesaroAverage_nonneg S.Gsq S.Gsq_nonneg T
      have heq := S.joint_average_eq T
      change CesaroAverage S.jointMeasure T =
        CesaroAverage S.Gsq T
          + S.lam ^ 2 * S.CR * CesaroAverage S.R T at heq
      have hscaled :
          S.lam ^ 2 * S.CR * CesaroAverage S.R T ≤
            CesaroAverage S.jointMeasure T := by
        rw [heq]
        exact le_add_of_nonneg_left hGavg
      have hinv : 0 ≤ 1 / (S.lam ^ 2 * S.CR) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hscaled hinv
      calc
        CesaroAverage S.R T
            = (1 / (S.lam ^ 2 * S.CR)) *
                (S.lam ^ 2 * S.CR * CesaroAverage S.R T) := by
                  field_simp [ne_of_gt S.lam_pos, ne_of_gt S.CR_pos]
        _ ≤ (1 / (S.lam ^ 2 * S.CR)) *
              CesaroAverage S.jointMeasure T := hmul
  · exact hupperTendsto

/-- The safeguard envelope error is the sum of the base contraction error and
residual-acceptance tolerance also at the level of finite averages. -/
theorem ResidualSafeguardSystem.eps_cesaro_eq
    (S : ResidualSafeguardSystem) (T : ℕ) :
    CesaroAverage S.eps T =
      CesaroAverage S.epsBase T + CesaroAverage S.tau T := by
  simp only [CesaroAverage, ResidualSafeguardSystem.eps, SeqSum,
    Finset.sum_add_distrib]
  ring

/-- Cesaro-vanishing base contraction errors and residual tolerances imply a
Cesaro-vanishing total envelope error. -/
theorem ResidualSafeguardSystem.eps_average_tendsto_zero_of_cesaro
    (S : ResidualSafeguardSystem)
    (hepsBase : Tendsto (CesaroAverage S.epsBase) atTop (𝓝 0))
    (htau : Tendsto (CesaroAverage S.tau) atTop (𝓝 0)) :
    Tendsto (CesaroAverage S.eps) atTop (𝓝 0) := by
  have hfun :
      CesaroAverage S.eps =
        fun T => CesaroAverage S.epsBase T + CesaroAverage S.tau T := by
    funext T
    exact S.eps_cesaro_eq T
  rw [hfun]
  simpa using hepsBase.add htau

/-- Trajectory-facing average squared-stationarity convergence under the weaker
Cesaro-vanishing perturbation assumptions. -/
theorem TrajectoryCertifiedProposalGainSystem.gradient_average_tendsto_zero_of_cesaro
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Tendsto (CesaroAverage S.proposal.epsBase) atTop (𝓝 0))
    (htauR : Tendsto (CesaroAverage S.proposal.tauR) atTop (𝓝 0))
    (hb : Tendsto (CesaroAverage S.b) atTop (𝓝 0))
    (hd : Tendsto (CesaroAverage S.d) atTop (𝓝 0)) :
    Tendsto (CesaroAverage (fun t => ‖S.G t‖ ^ 2)) atTop (𝓝 0) := by
  have heps :
      Tendsto (CesaroAverage S.toCertifiedGainStepSystem.eps) atTop (𝓝 0) := by
    change Tendsto
      (CesaroAverage
        S.proposal.toAcceptedResponseSelector.safeguardSystem.eps)
      atTop (𝓝 0)
    exact
      S.proposal.toAcceptedResponseSelector.safeguardSystem
        |>.eps_average_tendsto_zero_of_cesaro hepsBase htauR
  change Tendsto (CesaroAverage S.toCertifiedGainStepSystem.Gsq) atTop (𝓝 0)
  exact S.toCertifiedGainStepSystem.gradient_average_tendsto_zero_of_cesaro
    heps hb hd

/-- Trajectory-facing average response-residual convergence under the same weak
Cesaro assumptions. -/
theorem TrajectoryCertifiedProposalGainSystem.residual_average_tendsto_zero_of_cesaro
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (hepsBase : Tendsto (CesaroAverage S.proposal.epsBase) atTop (𝓝 0))
    (htauR : Tendsto (CesaroAverage S.proposal.tauR) atTop (𝓝 0))
    (hb : Tendsto (CesaroAverage S.b) atTop (𝓝 0))
    (hd : Tendsto (CesaroAverage S.d) atTop (𝓝 0)) :
    Tendsto (CesaroAverage S.proposal.R) atTop (𝓝 0) := by
  have heps :
      Tendsto (CesaroAverage S.toCertifiedGainStepSystem.eps) atTop (𝓝 0) := by
    change Tendsto
      (CesaroAverage
        S.proposal.toAcceptedResponseSelector.safeguardSystem.eps)
      atTop (𝓝 0)
    exact
      S.proposal.toAcceptedResponseSelector.safeguardSystem
        |>.eps_average_tendsto_zero_of_cesaro hepsBase htauR
  change Tendsto (CesaroAverage S.toCertifiedGainStepSystem.R) atTop (𝓝 0)
  exact S.toCertifiedGainStepSystem.residual_average_tendsto_zero_of_cesaro
    heps hb hd

/-- If `G_t` is the actual objective gradient, Cesaro-vanishing perturbations
imply vanishing average squared objective-gradient norm. -/
theorem TrajectoryCertifiedProposalGainSystem.objective_gradient_average_tendsto_zero_of_cesaro
    {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : TrajectoryCertifiedProposalGainSystem E X)
    (C : TrajectoryGradientCertificate S)
    (hepsBase : Tendsto (CesaroAverage S.proposal.epsBase) atTop (𝓝 0))
    (htauR : Tendsto (CesaroAverage S.proposal.tauR) atTop (𝓝 0))
    (hb : Tendsto (CesaroAverage S.b) atTop (𝓝 0))
    (hd : Tendsto (CesaroAverage S.d) atTop (𝓝 0)) :
    Tendsto
      (CesaroAverage (fun t => ‖gradient S.objective (S.z t)‖ ^ 2))
      atTop (𝓝 0) := by
  have hfun :
      (fun t => ‖gradient S.objective (S.z t)‖ ^ 2) =
        (fun t => ‖S.G t‖ ^ 2) := by
    funext t
    rw [C.gradient_eq t]
  rw [hfun]
  exact S.gradient_average_tendsto_zero_of_cesaro
    hepsBase htauR hb hd

end

end OUSVRBLO