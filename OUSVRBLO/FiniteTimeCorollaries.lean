import OUSVRBLO.CertifiedSafety
import OUSVRBLO.CertifiedGainDescent

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- The uniform expectation over `Finset.range T` is the arithmetic average used
throughout the finite-horizon theorem statements. -/
theorem range_expect_eq_seq_average {T : ℕ} (hT : 0 < T)
    (a : ℕ → ℝ) :
    Finset.expect (Finset.range T) a =
      (1 / (T : ℝ)) * SeqSum T a := by
  simp only [Finset.expect, Finset.card_range, SeqSum]
  rw [← NNRat.cast_smul_eq_nnqsmul ℝ]
  simp [smul_eq_mul, div_eq_mul_inv, Nat.ne_of_gt hT]

/-- Every nonempty finite horizon contains an iterate no larger than the
arithmetic average. -/
theorem exists_le_seq_average {T : ℕ} (hT : 0 < T)
    (a : ℕ → ℝ) :
    ∃ t < T, a t ≤ (1 / (T : ℝ)) * SeqSum T a := by
  have hrange : (Finset.range T).Nonempty := by
    exact ⟨0, Finset.mem_range.mpr hT⟩
  have hexpect :
      ∃ t ∈ Finset.range T, a t ≤ Finset.expect (Finset.range T) a := by
    exact Finset.exists_le_of_expect_le hrange le_rfl
  rcases hexpect with ⟨t, ht, hle⟩
  refine ⟨t, Finset.mem_range.mp ht, ?_⟩
  rw [range_expect_eq_seq_average hT a] at hle
  exact hle

/-- A reusable best-iterate principle: an averaged upper bound yields one
finite-horizon iterate satisfying the same bound. -/
theorem exists_le_of_seq_average_le {T : ℕ} (hT : 0 < T)
    (a : ℕ → ℝ) (B : ℝ)
    (havg : (1 / (T : ℝ)) * SeqSum T a ≤ B) :
    ∃ t < T, a t ≤ B := by
  rcases exists_le_seq_average hT a with ⟨t, ht, hle⟩
  exact ⟨t, ht, hle.trans havg⟩

/-- ICML-style finite-time stationarity statement for the fallback-safe
system: at least one iterate in the first `T` rounds satisfies the advertised
finite-horizon bound. -/
theorem CertifiedSafetySystem.exists_stationary_iterate
    (S : CertifiedSafetySystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t
        ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
          + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
          + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ)) := by
  exact exists_le_of_seq_average_le hT S.Gsq _
    (S.gradient_average_bound hT)

/-- At least one residual in the finite horizon is no larger than the averaged
residual guarantee. -/
theorem CertifiedSafetySystem.exists_small_residual_iterate
    (S : CertifiedSafetySystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.R t
        ≤ 4 * (S.Psi 0 - S.Pstar) /
            (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
          + 4 * S.Ceps * SeqSum T S.eps /
            (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
          + 4 * S.Cb * SeqSum T S.b /
            (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
          + 4 * S.Cd * SeqSum T S.d /
            (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  exact exists_le_of_seq_average_le hT S.R _
    (S.residual_average_bound hT)

/-- The certified-gain theorem also supplies an ordinary best-iterate
stationarity guarantee after dropping its nonnegative gain term. -/
theorem CertifiedGainStepSystem.exists_stationary_iterate
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.Gsq t
        ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
          + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
          + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ)) := by
  have hgainSum : 0 ≤ SeqSum T S.Gamma := by
    simpa [SeqSum] using Finset.sum_nonneg (fun t _ => S.Gamma_nonneg t)
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hgainAverage :
      0 ≤ 2 * S.lam ^ 2 * ((1 / (T : ℝ)) * SeqSum T S.Gamma) := by
    positivity
  have hjoint := S.gradient_gain_average_bound hT
  have havg :
      (1 / (T : ℝ)) * SeqSum T S.Gsq
        ≤ 4 * (S.Psi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + 4 * S.Ceps * SeqSum T S.eps / (S.eta * (T : ℝ))
          + 4 * S.Cb * SeqSum T S.b / (S.eta * (T : ℝ))
          + 4 * S.Cd * SeqSum T S.d / (S.eta * (T : ℝ)) := by
    nlinarith
  exact exists_le_of_seq_average_le hT S.Gsq _ havg

/-- Best-iterate residual guarantee for the certified-gain system. -/
theorem CertifiedGainStepSystem.exists_small_residual_iterate
    (S : CertifiedGainStepSystem) {T : ℕ} (hT : 0 < T) :
    ∃ t < T,
      S.R t
        ≤ 4 * (S.Psi 0 - S.Pstar) /
            (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
          + 4 * S.Ceps * SeqSum T S.eps /
            (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
          + 4 * S.Cb * SeqSum T S.b /
            (S.eta * S.lam ^ 2 * S.CR * (T : ℝ))
          + 4 * S.Cd * SeqSum T S.d /
            (S.eta * S.lam ^ 2 * S.CR * (T : ℝ)) := by
  exact exists_le_of_seq_average_le hT S.R _
    (S.residual_average_bound hT)

end

end OUSVRBLO
