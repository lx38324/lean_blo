import OUSVRBLO.CertifiedGainDescent
import OUSVRBLO.JointCertificates

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/--
Scalar moment interface for a centered stochastic update perturbation.

The quantities can be read as conditional expectations given the current
history. If the noise cross moment is zero and its second moment is bounded by
`sigmaSq`, the full stochastic step second moment is bounded by the noiseless
step second moment plus `sigmaSq`.
-/
structure CenteredNoiseMoment where
  baseStepSq : ℝ
  fullStepSq : ℝ
  noiseSq : ℝ
  crossMoment : ℝ
  sigmaSq : ℝ
  decomposition :
    fullStepSq = baseStepSq + 2 * crossMoment + noiseSq
  cross_zero : crossMoment = 0
  noise_bound : noiseSq ≤ sigmaSq

/-- Conditional centering and a second-moment bound control the full stochastic
step moment. -/
theorem CenteredNoiseMoment.fullStepSq_le
    (M : CenteredNoiseMoment) :
    M.fullStepSq ≤ M.baseStepSq + M.sigmaSq := by
  rw [M.decomposition, M.cross_zero]
  linarith [M.noise_bound]

/--
Expectation-level certified-gain Lyapunov system.

`EP`, `ER`, `EQ`, `EGsq`, and `EGamma` represent expectations, or conditional
expectations already averaged over the stochastic history. The one-step
interfaces are the standard consequences of a centered stochastic perturbation
`W_t` with second moment bounded by `sigmaSq t`:

* objective descent gains `LP * eta^2 / 2 * sigmaSq t`;
* residual drift gains `Aeta * sigmaSq t`.

The theorem below machine-checks the subsequent coefficient accounting,
telescoping, gain retention, and expected stationarity/residual rates.
-/
structure StochasticExpectedGainSystem extends SafetyParameters where
  LP : ℝ
  LP_nonneg : 0 ≤ LP
  Pstar : ℝ
  EP : ℕ → ℝ
  ER : ℕ → ℝ
  EQ : ℕ → ℝ
  EGsq : ℕ → ℝ
  EGamma : ℕ → ℝ
  Eeps : ℕ → ℝ
  Eb : ℕ → ℝ
  Ed : ℕ → ℝ
  sigmaSq : ℕ → ℝ
  ER_nonneg : ∀ t, 0 ≤ ER t
  EGsq_nonneg : ∀ t, 0 ≤ EGsq t
  EGamma_nonneg : ∀ t, 0 ≤ EGamma t
  Eeps_nonneg : ∀ t, 0 ≤ Eeps t
  Eb_nonneg : ∀ t, 0 ≤ Eb t
  Ed_nonneg : ∀ t, 0 ≤ Ed t
  sigmaSq_nonneg : ∀ t, 0 ≤ sigmaSq t
  EP_lower : ∀ t, Pstar ≤ EP t
  expected_descent :
    ∀ t,
      EP (t + 1) ≤ EP t
        - eta / 2 * EGsq t
        + eta * lam ^ 2 / 2 * (CR * EQ t + Eb t)
        - eta * lam ^ 2 / 2 * EGamma t
        + LP * eta ^ 2 / 2 * sigmaSq t
  expected_drift :
    ∀ t,
      ER (t + 1) ≤
        (1 + CR * beta) * EQ t
          + 2 * Aeta * EGsq t
          + beta * Eb t
          - 2 * Aeta * lam ^ 2 * EGamma t
          + Ed t
          + Aeta * sigmaSq t
  expected_envelope_contraction :
    ∀ t, EQ t ≤ (1 - theta) * ER t + Eeps t

/-- Expected Lyapunov function. -/
def StochasticExpectedGainSystem.EPsi
    (S : StochasticExpectedGainSystem) (t : ℕ) : ℝ :=
  S.EP t + S.alpha * S.ER t

/-- Variance coefficient in the expected Lyapunov recursion. -/
def StochasticExpectedGainSystem.Csigma
    (S : StochasticExpectedGainSystem) : ℝ :=
  S.LP * S.eta ^ 2 / 2 + S.alpha * S.Aeta

/-- Expected accumulated right-hand side, including stochastic second moments. -/
def StochasticExpectedGainSystem.accumulatedRhs
    (S : StochasticExpectedGainSystem) (T : ℕ) : ℝ :=
  S.EPsi 0 - S.Pstar
    + S.Ceps * SeqSum T S.Eeps
    + S.Cb * SeqSum T S.Eb
    + S.Cd * SeqSum T S.Ed
    + S.Csigma * SeqSum T S.sigmaSq

/-- Expected joint stationarity and response-residual measure. -/
def StochasticExpectedGainSystem.jointMeasure
    (S : StochasticExpectedGainSystem) (t : ℕ) : ℝ :=
  S.EGsq t + S.lam ^ 2 * S.CR * S.ER t

/-- Gain-adjusted stochastic numerator. -/
def StochasticExpectedGainSystem.gainAdjustedRhs
    (S : StochasticExpectedGainSystem) (T : ℕ) : ℝ :=
  S.accumulatedRhs T - S.Cgain * SeqSum T S.EGamma

/-- The stochastic variance coefficient is nonnegative. -/
theorem StochasticExpectedGainSystem.Csigma_nonneg
    (S : StochasticExpectedGainSystem) :
    0 ≤ S.Csigma := by
  dsimp [StochasticExpectedGainSystem.Csigma]
  exact add_nonneg
    (div_nonneg
      (mul_nonneg S.LP_nonneg (sq_nonneg S.eta)) (by norm_num))
    (mul_nonneg S.toSafetyParameters.alpha_nonneg S.Aeta_nonneg)

/-- Lower bound for the expected Lyapunov function. -/
theorem StochasticExpectedGainSystem.EPsi_lower
    (S : StochasticExpectedGainSystem) (t : ℕ) :
    S.Pstar ≤ S.EPsi t := by
  have hR : 0 ≤ S.alpha * S.ER t :=
    mul_nonneg S.toSafetyParameters.alpha_nonneg (S.ER_nonneg t)
  dsimp [StochasticExpectedGainSystem.EPsi]
  linarith [S.EP_lower t]

/-- One-step expected Lyapunov descent with explicit stochastic second-moment
penalty. -/
theorem StochasticExpectedGainSystem.one_step_lyapunov
    (S : StochasticExpectedGainSystem) (t : ℕ) :
    S.EPsi (t + 1) ≤ S.EPsi t
      - S.eta / 4 * S.EGsq t
      - S.eta * S.lam ^ 2 * S.CR / 4 * S.ER t
      - S.Cgain * S.EGamma t
      + S.Ceps * S.Eeps t
      + S.Cb * S.Eb t
      + S.Cd * S.Ed t
      + S.Csigma * S.sigmaSq t := by
  dsimp [StochasticExpectedGainSystem.EPsi,
    StochasticExpectedGainSystem.Csigma,
    SafetyParameters.Cgain, SafetyParameters.Ceps,
    SafetyParameters.Cb, SafetyParameters.Cd]
  have hdes := S.expected_descent t
  have hdrift := S.expected_drift t
  have hcontr := S.expected_envelope_contraction t
  have hdrift_scaled :=
    mul_le_mul_of_nonneg_left hdrift S.toSafetyParameters.alpha_nonneg
  have hcombined :
      S.EP (t + 1) + S.alpha * S.ER (t + 1) ≤
        S.EP t
          - (S.eta / 2 - 2 * S.alpha * S.Aeta) * S.EGsq t
          + (S.eta * S.lam ^ 2 * S.CR / 2
            + S.alpha * (1 + S.CR * S.beta)) * S.EQ t
          + (S.eta * S.lam ^ 2 / 2
            + S.alpha * S.beta) * S.Eb t
          + S.alpha * S.Ed t
          - (S.eta * S.lam ^ 2 / 2
            + 2 * S.alpha * S.Aeta * S.lam ^ 2) * S.EGamma t
          + (S.LP * S.eta ^ 2 / 2
            + S.alpha * S.Aeta) * S.sigmaSq t := by
    nlinarith [hdes, hdrift_scaled]
  have hcontr_scaled :=
    mul_le_mul_of_nonneg_left hcontr
      S.toSafetyParameters.envelope_coeff_nonneg
  have htwo := S.toSafetyParameters.two_alpha_Aeta_le
  have hdrop := S.toSafetyParameters.residual_drop_coeff
  have heps :
      S.eta * S.lam ^ 2 * S.CR / 2
        + S.alpha * (1 + S.CR * S.beta)
        ≤ S.eta * S.lam ^ 2 * S.CR * (3 / 4 + 1 / S.theta) := by
    simpa [SafetyParameters.Ceps] using
      S.toSafetyParameters.eps_coeff_bound
  have hb :
      S.eta * S.lam ^ 2 / 2 + S.alpha * S.beta
        ≤ 3 / 4 * S.eta * S.lam ^ 2 := by
    simpa [SafetyParameters.Cb] using
      S.toSafetyParameters.b_coeff_bound
  have htwo_scaled :=
    mul_le_mul_of_nonneg_right htwo (S.EGsq_nonneg t)
  have hdrop_scaled :=
    mul_le_mul_of_nonneg_right hdrop (S.ER_nonneg t)
  have heps_scaled :=
    mul_le_mul_of_nonneg_right heps (S.Eeps_nonneg t)
  have hb_scaled :=
    mul_le_mul_of_nonneg_right hb (S.Eb_nonneg t)
  ring_nf at hcombined hcontr_scaled htwo_scaled hdrop_scaled
    heps_scaled hb_scaled ⊢
  linarith [hcombined, hcontr_scaled, htwo_scaled, hdrop_scaled,
    heps_scaled, hb_scaled]

/-- Exact finite-horizon expected budget. -/
theorem StochasticExpectedGainSystem.cumulative_budget_to_time
    (S : StochasticExpectedGainSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.EGsq
      + S.Cgain * SeqSum T S.EGamma
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.ER
      ≤ S.EPsi 0 - S.EPsi T
        + S.Ceps * SeqSum T S.Eeps
        + S.Cb * SeqSum T S.Eb
        + S.Cd * SeqSum T S.Ed
        + S.Csigma * SeqSum T S.sigmaSq := by
  induction T with
  | zero => simp [SeqSum]
  | succ T ih =>
      simp [SeqSum] at ih
      simp [SeqSum, Finset.sum_range_succ]
      have hstep := S.one_step_lyapunov T
      ring_nf at ih hstep ⊢
      nlinarith [ih, hstep]

/-- Exact finite-horizon expected budget with the terminal Lyapunov lower bound. -/
theorem StochasticExpectedGainSystem.cumulative_budget
    (S : StochasticExpectedGainSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.EGsq
      + S.Cgain * SeqSum T S.EGamma
      + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.ER
      ≤ S.accumulatedRhs T := by
  have htime := S.cumulative_budget_to_time T
  have hlower := S.EPsi_lower T
  dsimp [StochasticExpectedGainSystem.accumulatedRhs]
  nlinarith [htime, hlower]

/-- The exact expected budget gives a gain-adjusted joint partial-sum bound. -/
theorem StochasticExpectedGainSystem.joint_scaled_sum_le_gainAdjustedRhs
    (S : StochasticExpectedGainSystem) (T : ℕ) :
    (S.eta / 4) * SeqSum T S.jointMeasure ≤ S.gainAdjustedRhs T := by
  have hbudget := S.cumulative_budget T
  have hjoint :
      (S.eta / 4) * SeqSum T S.jointMeasure =
        (S.eta / 4) * SeqSum T S.EGsq
          + (S.eta * S.lam ^ 2 * S.CR / 4) * SeqSum T S.ER := by
    simp only [StochasticExpectedGainSystem.jointMeasure, SeqSum,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    ring
  rw [hjoint]
  dsimp [StochasticExpectedGainSystem.gainAdjustedRhs]
  linarith

/-- The gain-adjusted stochastic numerator is nonnegative. -/
theorem StochasticExpectedGainSystem.gainAdjustedRhs_nonneg
    (S : StochasticExpectedGainSystem) (T : ℕ) :
    0 ≤ S.gainAdjustedRhs T := by
  have hsum : 0 ≤ SeqSum T S.jointMeasure := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => by
      exact add_nonneg (S.EGsq_nonneg t)
        (mul_nonneg
          (mul_nonneg (sq_nonneg S.lam) (le_of_lt S.CR_pos))
          (S.ER_nonneg t)))
  have hcoef : 0 ≤ S.eta / 4 :=
    div_nonneg (le_of_lt S.eta_pos) (by norm_num)
  have hleft : 0 ≤ (S.eta / 4) * SeqSum T S.jointMeasure :=
    mul_nonneg hcoef hsum
  exact hleft.trans (S.joint_scaled_sum_le_gainAdjustedRhs T)

/-- Expected average stationarity/residual rate retaining the accumulated
certified gain and stochastic variance budget. -/
theorem StochasticExpectedGainSystem.joint_average_bound_with_gain
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by
  have hbase := S.joint_scaled_sum_le_gainAdjustedRhs T
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) :=
    le_of_lt (div_pos (by norm_num) hden)
  have hscaled := mul_le_mul_of_nonneg_left hbase hscale
  calc
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure
        = (4 / (S.eta * (T : ℝ))) *
            ((S.eta / 4) * SeqSum T S.jointMeasure) := by
              field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]
    _ ≤ (4 / (S.eta * (T : ℝ))) * S.gainAdjustedRhs T := hscaled
    _ = 4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by ring

/-- Some stochastic expected iterate on the horizon satisfies the same
 gain-adjusted joint bound. -/
theorem StochasticExpectedGainSystem.exists_joint_certificate_with_gain
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.jointMeasure t ≤
        4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) := by
  exact exists_le_of_seq_average_le hT S.jointMeasure _
    (S.joint_average_bound_with_gain hT)

/-- Safety-form expected rate obtained by dropping the nonnegative gain term. -/
theorem StochasticExpectedGainSystem.joint_average_bound
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by
  have hcoefBase : 0 ≤ S.eta * S.lam ^ 2 / 2 :=
    div_nonneg
      (mul_nonneg (le_of_lt S.eta_pos) (sq_nonneg S.lam))
      (by norm_num)
  have hcoef : 0 ≤ S.Cgain :=
    hcoefBase.trans S.toSafetyParameters.Cgain_lower
  have hsum : 0 ≤ SeqSum T S.EGamma := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.EGamma_nonneg t)
  have hgain : 0 ≤ S.Cgain * SeqSum T S.EGamma :=
    mul_nonneg hcoef hsum
  have hadj : S.gainAdjustedRhs T ≤ S.accumulatedRhs T := by
    dsimp [StochasticExpectedGainSystem.gainAdjustedRhs]
    linarith
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) :=
    le_of_lt (div_pos (by norm_num) hden)
  have hscaled := mul_le_mul_of_nonneg_left hadj hscale
  calc
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure
        ≤ 4 * S.gainAdjustedRhs T / (S.eta * (T : ℝ)) :=
          S.joint_average_bound_with_gain hT
    _ = (4 / (S.eta * (T : ℝ))) * S.gainAdjustedRhs T := by ring
    _ ≤ (4 / (S.eta * (T : ℝ))) * S.accumulatedRhs T := hscaled
    _ = 4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := by ring

/-- Uniform second-moment and certificate-error bounds produce an explicit
expected neighborhood. -/
theorem StochasticExpectedGainSystem.joint_average_bound_of_uniform_errors
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T)
    (epsBar bBar dBar sigmaBar : ℝ)
    (heps : ∀ t, S.Eeps t ≤ epsBar)
    (hb : ∀ t, S.Eb t ≤ bBar)
    (hd : ∀ t, S.Ed t ≤ dBar)
    (hsigma : ∀ t, S.sigmaSq t ≤ sigmaBar) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + 4 * (S.Ceps * epsBar + S.Cb * bBar + S.Cd * dBar
          + S.Csigma * sigmaBar) / S.eta := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsumEps : SeqSum T S.Eeps ≤ (T : ℝ) * epsBar := by
    calc
      SeqSum T S.Eeps ≤ SeqSum T (fun _ => epsBar) := by
        apply Finset.sum_le_sum
        intro t ht
        exact heps t
      _ = (T : ℝ) * epsBar := by simp [SeqSum]
  have hsumB : SeqSum T S.Eb ≤ (T : ℝ) * bBar := by
    calc
      SeqSum T S.Eb ≤ SeqSum T (fun _ => bBar) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hb t
      _ = (T : ℝ) * bBar := by simp [SeqSum]
  have hsumD : SeqSum T S.Ed ≤ (T : ℝ) * dBar := by
    calc
      SeqSum T S.Ed ≤ SeqSum T (fun _ => dBar) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hd t
      _ = (T : ℝ) * dBar := by simp [SeqSum]
  have hsumSigma : SeqSum T S.sigmaSq ≤ (T : ℝ) * sigmaBar := by
    calc
      SeqSum T S.sigmaSq ≤ SeqSum T (fun _ => sigmaBar) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hsigma t
      _ = (T : ℝ) * sigmaBar := by simp [SeqSum]
  have hCeps : 0 ≤ S.Ceps := S.toSafetyParameters.Ceps_nonneg
  have hCb : 0 ≤ S.Cb := S.toSafetyParameters.Cb_nonneg
  have hCd : 0 ≤ S.Cd := S.toSafetyParameters.Cd_nonneg
  have hCsigma : 0 ≤ S.Csigma := S.Csigma_nonneg
  have hrhs :
      S.accumulatedRhs T ≤ S.EPsi 0 - S.Pstar
        + (T : ℝ) * (S.Ceps * epsBar + S.Cb * bBar + S.Cd * dBar
          + S.Csigma * sigmaBar) := by
    dsimp [StochasticExpectedGainSystem.accumulatedRhs]
    have h1 := mul_le_mul_of_nonneg_left hsumEps hCeps
    have h2 := mul_le_mul_of_nonneg_left hsumB hCb
    have h3 := mul_le_mul_of_nonneg_left hsumD hCd
    have h4 := mul_le_mul_of_nonneg_left hsumSigma hCsigma
    nlinarith
  have hbase := S.joint_average_bound hT
  have hden : 0 < S.eta * (T : ℝ) := mul_pos S.eta_pos hTreal
  have hscale : 0 ≤ 4 / (S.eta * (T : ℝ)) :=
    le_of_lt (div_pos (by norm_num) hden)
  have hscaled := mul_le_mul_of_nonneg_left hrhs hscale
  calc
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure
        ≤ 4 * S.accumulatedRhs T / (S.eta * (T : ℝ)) := hbase
    _ = (4 / (S.eta * (T : ℝ))) * S.accumulatedRhs T := by ring
    _ ≤ (4 / (S.eta * (T : ℝ))) *
          (S.EPsi 0 - S.Pstar
            + (T : ℝ) * (S.Ceps * epsBar + S.Cb * bBar + S.Cd * dBar
              + S.Csigma * sigmaBar)) := hscaled
    _ = 4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + 4 * (S.Ceps * epsBar + S.Cb * bBar + S.Cd * dBar
            + S.Csigma * sigmaBar) / S.eta := by
            field_simp [ne_of_gt S.eta_pos, ne_of_gt hTreal]

end

end OUSVRBLO
