import OUSVRBLO.Asymptotics

open BigOperators Filter Topology
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- The residual-contraction error coefficient is nonnegative. -/
theorem SafetyParameters.Ceps_nonneg (P : SafetyParameters) :
    0 ≤ P.Ceps := by
  have hbase : 0 ≤ P.eta * P.lam ^ 2 * P.CR :=
    mul_nonneg
      (mul_nonneg (le_of_lt P.eta_pos) (sq_nonneg P.lam))
      (le_of_lt P.CR_pos)
  have hinv : 0 ≤ 1 / P.theta :=
    div_nonneg (by norm_num) (le_of_lt P.theta_pos)
  dsimp [SafetyParameters.Ceps]
  exact mul_nonneg hbase (add_nonneg (by norm_num) hinv)

/-- The value-gradient bias coefficient is nonnegative. -/
theorem SafetyParameters.Cb_nonneg (P : SafetyParameters) :
    0 ≤ P.Cb := by
  dsimp [SafetyParameters.Cb]
  exact mul_nonneg
    (mul_nonneg (by norm_num) (le_of_lt P.eta_pos))
    (sq_nonneg P.lam)

/-- The residual-drift error coefficient is nonnegative. -/
theorem SafetyParameters.Cd_nonneg (P : SafetyParameters) :
    0 ≤ P.Cd := by
  simpa [SafetyParameters.Cd] using P.alpha_nonneg

/-- The finite upper bound obtained from summable perturbation sequences in the
fallback-safe theorem. -/
def CertifiedSafetySystem.summableRhs (S : CertifiedSafetySystem) : ℝ :=
  S.Psi 0 - S.Pstar
    + S.Ceps * ∑' t, S.eps t
    + S.Cb * ∑' t, S.b t
    + S.Cd * ∑' t, S.d t

/-- Summability of all nonnegative perturbation sequences gives the uniform
accumulated-budget bound required by `Asymptotics.lean`. -/
theorem CertifiedSafetySystem.accumulatedRhs_le_summableRhs
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    ∀ T, S.accumulatedRhs T ≤ S.summableRhs := by
  intro T
  have hepsSum : SeqSum T S.eps ≤ ∑' t, S.eps t := by
    simpa [SeqSum] using
      heps.sum_le_tsum (Finset.range T) (fun t _ => S.eps_nonneg t)
  have hbSum : SeqSum T S.b ≤ ∑' t, S.b t := by
    simpa [SeqSum] using
      hb.sum_le_tsum (Finset.range T) (fun t _ => S.b_nonneg t)
  have hdSum : SeqSum T S.d ≤ ∑' t, S.d t := by
    simpa [SeqSum] using
      hd.sum_le_tsum (Finset.range T) (fun t _ => S.d_nonneg t)
  have hCeps : 0 ≤ S.Ceps := by
    simpa [CertifiedSafetySystem.Ceps] using
      S.toSafetyParameters.Ceps_nonneg
  have hCb : 0 ≤ S.Cb := by
    simpa [CertifiedSafetySystem.Cb] using S.toSafetyParameters.Cb_nonneg
  have hCd : 0 ≤ S.Cd := by
    simpa [CertifiedSafetySystem.Cd] using S.toSafetyParameters.Cd_nonneg
  have hepsScaled := mul_le_mul_of_nonneg_left hepsSum hCeps
  have hbScaled := mul_le_mul_of_nonneg_left hbSum hCb
  have hdScaled := mul_le_mul_of_nonneg_left hdSum hCd
  dsimp [CertifiedSafetySystem.accumulatedRhs,
    CertifiedSafetySystem.summableRhs]
  linarith

/-- Summable safety perturbations imply average stationarity convergence. -/
theorem CertifiedSafetySystem.gradient_average_tendsto_zero_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.Gsq)
      atTop (𝓝 0) :=
  S.gradient_average_tendsto_zero S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd)

/-- Summable safety perturbations imply average residual convergence. -/
theorem CertifiedSafetySystem.residual_average_tendsto_zero_of_summable
    (S : CertifiedSafetySystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.R)
      atTop (𝓝 0) :=
  S.residual_average_tendsto_zero S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd)

/-- The finite upper bound obtained from summable perturbations in the
certified-gain theorem. -/
def CertifiedGainStepSystem.summableRhs
    (S : CertifiedGainStepSystem) : ℝ :=
  S.Psi 0 - S.Pstar
    + S.Ceps * ∑' t, S.eps t
    + S.Cb * ∑' t, S.b t
    + S.Cd * ∑' t, S.d t

/-- Summability supplies the uniform accumulated right-hand-side bound for the
certified-gain theorem. -/
theorem CertifiedGainStepSystem.accumulatedRhs_le_summableRhs
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    ∀ T, S.accumulatedRhs T ≤ S.summableRhs := by
  intro T
  have hepsSum : SeqSum T S.eps ≤ ∑' t, S.eps t := by
    simpa [SeqSum] using
      heps.sum_le_tsum (Finset.range T) (fun t _ => S.eps_nonneg t)
  have hbSum : SeqSum T S.b ≤ ∑' t, S.b t := by
    simpa [SeqSum] using
      hb.sum_le_tsum (Finset.range T) (fun t _ => S.b_nonneg t)
  have hdSum : SeqSum T S.d ≤ ∑' t, S.d t := by
    simpa [SeqSum] using
      hd.sum_le_tsum (Finset.range T) (fun t _ => S.d_nonneg t)
  have hCeps : 0 ≤ S.Ceps := by
    simpa [CertifiedGainStepSystem.Ceps] using
      S.toSafetyParameters.Ceps_nonneg
  have hCb : 0 ≤ S.Cb := by
    simpa [CertifiedGainStepSystem.Cb] using S.toSafetyParameters.Cb_nonneg
  have hCd : 0 ≤ S.Cd := by
    simpa [CertifiedGainStepSystem.Cd] using S.toSafetyParameters.Cd_nonneg
  have hepsScaled := mul_le_mul_of_nonneg_left hepsSum hCeps
  have hbScaled := mul_le_mul_of_nonneg_left hbSum hCb
  have hdScaled := mul_le_mul_of_nonneg_left hdSum hCd
  dsimp [CertifiedGainStepSystem.accumulatedRhs,
    CertifiedGainStepSystem.summableRhs]
  linarith

/-- Summable certified-gain perturbations imply average stationarity
convergence. -/
theorem CertifiedGainStepSystem.gradient_average_tendsto_zero_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.Gsq)
      atTop (𝓝 0) :=
  S.gradient_average_tendsto_zero S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd)

/-- Summable certified-gain perturbations imply average residual convergence. -/
theorem CertifiedGainStepSystem.residual_average_tendsto_zero_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.R)
      atTop (𝓝 0) :=
  S.residual_average_tendsto_zero S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd)

/-- Under summable perturbations, the average uncertainty-adjusted certified
gain also converges to zero. -/
theorem CertifiedGainStepSystem.gain_average_tendsto_zero_of_summable
    (S : CertifiedGainStepSystem)
    (heps : Summable S.eps) (hb : Summable S.b) (hd : Summable S.d) :
    Tendsto (fun T : ℕ => (1 / (T : ℝ)) * SeqSum T S.Gamma)
      atTop (𝓝 0) :=
  S.gain_average_tendsto_zero S.summableRhs
    (S.accumulatedRhs_le_summableRhs heps hb hd)

end

end OUSVRBLO
