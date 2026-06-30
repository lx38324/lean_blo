import Mathlib

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

lemma sum_nonneg_range {T : ℕ} {a : ℕ → ℝ}
    (ha : ∀ t, 0 ≤ a t) :
    0 ≤ ∑ t ∈ Finset.range T, a t := by
  exact Finset.sum_nonneg (fun t _ => ha t)

lemma drop_nonneg_add_right {a b c : ℝ}
    (h : a + b ≤ c) (hb : 0 ≤ b) :
    a ≤ c := by
  linarith

lemma scale_eta_quarter {eta T x : ℝ}
    (heta : eta ≠ 0) (hT : T ≠ 0) :
    (4 / (eta * T)) * ((eta / 4) * x) = (1 / T) * x := by
  field_simp [heta, hT]

lemma scale_eta_lam_CR_quarter {eta lam CR T x : ℝ}
    (heta : eta ≠ 0) (hlam : lam ≠ 0) (hCR : CR ≠ 0) (hT : T ≠ 0) :
    (4 / (eta * lam ^ 2 * CR * T)) *
      ((eta * lam ^ 2 * CR / 4) * x) = (1 / T) * x := by
  field_simp [heta, hlam, hCR, hT]

end

end OUSVRBLO
