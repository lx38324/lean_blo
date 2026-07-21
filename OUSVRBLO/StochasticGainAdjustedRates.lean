import OUSVRBLO.StochasticExpectedGain

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- The exact certified-gain coefficient in the expectation-level theorem is
strictly positive. -/
theorem StochasticExpectedGainSystem.gain_coefficient_pos
    (S : StochasticExpectedGainSystem) :
    0 < S.Cgain := by
  have hlamSq : 0 < S.lam ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt S.lam_pos)
  have hbase : 0 < S.eta * S.lam ^ 2 / 2 :=
    div_pos (mul_pos S.eta_pos hlamSq) (by norm_num)
  exact lt_of_lt_of_le hbase S.toSafetyParameters.Cgain_lower

/-- Retaining expected certified gain never weakens the safety-only expected
numerator. -/
theorem StochasticExpectedGainSystem.gainAdjustedRhs_le_accumulatedRhs
    (S : StochasticExpectedGainSystem) (T : ℕ) :
    S.gainAdjustedRhs T ≤ S.accumulatedRhs T := by
  have hsum : 0 ≤ SeqSum T S.EGamma := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.EGamma_nonneg t)
  have hgain : 0 ≤ S.Cgain * SeqSum T S.EGamma :=
    mul_nonneg S.gain_coefficient_pos.le hsum
  dsimp [StochasticExpectedGainSystem.gainAdjustedRhs]
  linarith

/-- Positive accumulated expected certified gain strictly tightens the expected
selected-trajectory numerator. -/
theorem StochasticExpectedGainSystem.gainAdjustedRhs_lt_accumulatedRhs_of_positive_gain
    (S : StochasticExpectedGainSystem) (T : ℕ)
    (hgainSum : 0 < SeqSum T S.EGamma) :
    S.gainAdjustedRhs T < S.accumulatedRhs T := by
  have hgain : 0 < S.Cgain * SeqSum T S.EGamma :=
    mul_pos S.gain_coefficient_pos hgainSum
  dsimp [StochasticExpectedGainSystem.gainAdjustedRhs]
  linarith

end

end OUSVRBLO
