import OUSVRBLO.StochasticExpectedGain
import OUSVRBLO.ManuscriptParameters

open BigOperators
open scoped BigOperators

namespace OUSVRBLO

noncomputable section

/-- The stochastic variance neighborhood coefficient before substituting the
manuscript formula for `Aeta`. -/
theorem StochasticExpectedGainSystem.four_Csigma_div_eta
    (S : StochasticExpectedGainSystem) :
    4 * S.Csigma / S.eta =
      2 * S.LP * S.eta +
        4 * S.lam ^ 2 * S.CR * S.Aeta / S.theta := by
  dsimp [StochasticExpectedGainSystem.Csigma, SafetyParameters.alpha]
  field_simp [ne_of_gt S.eta_pos, ne_of_gt S.theta_pos]
  ring

/-- With the manuscript drift coefficient, the stochastic variance neighborhood
is linear plus quadratic in the step size. -/
theorem StochasticExpectedGainSystem.four_Csigma_div_eta_manuscript
    (S : StochasticExpectedGainSystem) (LR : ℝ)
    (hAeta :
      S.Aeta = S.eta / (2 * sqrtTwo * S.lam) + LR * S.eta ^ 2 / 2) :
    4 * S.Csigma / S.eta =
      S.eta *
        (2 * S.LP
          + sqrtTwo * S.lam * S.CR / S.theta
          + 2 * S.lam ^ 2 * S.CR * LR * S.eta / S.theta) := by
  rw [S.four_Csigma_div_eta, hAeta]
  field_simp [sqrtTwo_ne_zero, ne_of_gt S.lam_pos,
    ne_of_gt S.theta_pos]
  ring_nf
  rw [sqrtTwo_sq]
  ring

/-- With zero certificate bias and uniformly bounded stochastic second moment,
the expected joint stationarity/residual average has the standard
`gap / (eta*T) + variance(eta)` form. -/
theorem StochasticExpectedGainSystem.joint_average_bound_of_variance_only
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T)
    (sigmaBar : ℝ)
    (heps : ∀ t, S.Eeps t = 0)
    (hb : ∀ t, S.Eb t = 0)
    (hd : ∀ t, S.Ed t = 0)
    (hsigma : ∀ t, S.sigmaSq t ≤ sigmaBar) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + (2 * S.LP * S.eta
          + 4 * S.lam ^ 2 * S.CR * S.Aeta / S.theta) * sigmaBar := by
  have hbase := S.joint_average_bound_of_uniform_errors hT
    0 0 0 sigmaBar
    (fun t => (heps t).le)
    (fun t => (hb t).le)
    (fun t => (hd t).le)
    hsigma
  have hbase' :
      (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
        4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + 4 * (S.Csigma * sigmaBar) / S.eta := by
    simpa using hbase
  calc
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure
        ≤ 4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
            + 4 * (S.Csigma * sigmaBar) / S.eta := hbase'
    _ = 4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + (4 * S.Csigma / S.eta) * sigmaBar := by ring
    _ = 4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + (2 * S.LP * S.eta
            + 4 * S.lam ^ 2 * S.CR * S.Aeta / S.theta) * sigmaBar := by
        rw [S.four_Csigma_div_eta]

/-- Manuscript-specialized stochastic rate. The variance contribution is
`eta * K(eta) * sigmaBar`, so the checked theorem has the usual
`O(1/(eta*T) + eta*sigma^2)` dependence when the bracket is bounded. -/
theorem StochasticExpectedGainSystem.joint_average_bound_of_variance_only_manuscript
    (S : StochasticExpectedGainSystem) {T : ℕ} (hT : 0 < T)
    (LR sigmaBar : ℝ)
    (hAeta :
      S.Aeta = S.eta / (2 * sqrtTwo * S.lam) + LR * S.eta ^ 2 / 2)
    (heps : ∀ t, S.Eeps t = 0)
    (hb : ∀ t, S.Eb t = 0)
    (hd : ∀ t, S.Ed t = 0)
    (hsigma : ∀ t, S.sigmaSq t ≤ sigmaBar) :
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure ≤
      4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + S.eta *
          (2 * S.LP
            + sqrtTwo * S.lam * S.CR / S.theta
            + 2 * S.lam ^ 2 * S.CR * LR * S.eta / S.theta) * sigmaBar := by
  have hbase := S.joint_average_bound_of_variance_only hT sigmaBar
    heps hb hd hsigma
  calc
    (1 / (T : ℝ)) * SeqSum T S.jointMeasure
        ≤ 4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
          + (2 * S.LP * S.eta
            + 4 * S.lam ^ 2 * S.CR * S.Aeta / S.theta) * sigmaBar := hbase
    _ = 4 * (S.EPsi 0 - S.Pstar) / (S.eta * (T : ℝ))
        + S.eta *
          (2 * S.LP
            + sqrtTwo * S.lam * S.CR / S.theta
            + 2 * S.lam ^ 2 * S.CR * LR * S.eta / S.theta) * sigmaBar := by
      have hcoeff := S.four_Csigma_div_eta_manuscript LR hAeta
      have hgeneric := S.four_Csigma_div_eta
      linarith

end

end OUSVRBLO
