import Mathlib

namespace OUSVRBLO

noncomputable section

/--
Legacy symmetric proxy-comparison certificate.

`ehatO` and `ehatB` are computable proxy errors, while `eO` and `eB` are the
true value-gradient approximation errors.
-/
structure ProxyComparison where
  eO : ℝ
  eB : ℝ
  ehatO : ℝ
  ehatB : ℝ
  DeltaHat : ℝ
  rho : ℝ
  rho_nonneg : 0 ≤ rho
  calibO_abs : |ehatO - eO| ≤ rho
  calibB_abs : |ehatB - eB| ≤ rho
  proxy_improves : ehatO ≤ ehatB - DeltaHat

theorem ProxyComparison.true_error_improves
    (C : ProxyComparison) :
    C.eO ≤ C.eB - C.DeltaHat + 2 * C.rho := by
  have hO : C.eO ≤ C.ehatO + C.rho := by
    have h := abs_le.mp C.calibO_abs
    linarith [h.1]
  have hB : C.ehatB ≤ C.eB + C.rho := by
    have h := abs_le.mp C.calibB_abs
    linarith [h.2]
  linarith [hO, hB, C.proxy_improves]

/--
Legacy combination of a baseline error bound and the symmetric proxy
comparison. The new public theorem below uses an uncertainty-adjusted gain.
-/
structure ProxyR2Plus where
  CR : ℝ
  Rhat : ℝ
  b : ℝ
  eO : ℝ
  eB : ℝ
  DeltaHat : ℝ
  rho : ℝ
  baseline_bound : eB ≤ CR * Rhat + b
  proxy_bound : eO ≤ eB - DeltaHat + 2 * rho

theorem ProxyR2Plus.r2plus
    (C : ProxyR2Plus) :
    C.eO ≤ C.CR * C.Rhat + C.b - C.DeltaHat + 2 * C.rho := by
  nlinarith [C.baseline_bound, C.proxy_bound]

/--
Asymmetric calibrated proxy comparison with an explicit acceptance tolerance.

The uncertainty-adjusted certified gain is
`DeltaHat - tauE - rhoO - rhoB`. It is this quantity, rather than the nominal
proxy margin, that can safely enter the Lyapunov budget.
-/
structure CalibratedProxyGain where
  eO : ℝ
  eB : ℝ
  ehatO : ℝ
  ehatB : ℝ
  DeltaHat : ℝ
  tauE : ℝ
  rhoO : ℝ
  rhoB : ℝ
  rhoO_nonneg : 0 ≤ rhoO
  rhoB_nonneg : 0 ≤ rhoB
  tauE_nonneg : 0 ≤ tauE
  calibO_abs : |ehatO - eO| ≤ rhoO
  calibB_abs : |ehatB - eB| ≤ rhoB
  proxy_improves : ehatO ≤ ehatB - DeltaHat + tauE

/-- Nominal proxy improvement after subtracting tolerance and calibration
uncertainty. -/
def CalibratedProxyGain.gain (C : CalibratedProxyGain) : ℝ :=
  C.DeltaHat - C.tauE - C.rhoO - C.rhoB

/-- Proxy calibration converts the computable comparison into a true-error
improvement by exactly the uncertainty-adjusted gain. -/
theorem CalibratedProxyGain.true_error_improves
    (C : CalibratedProxyGain) :
    C.eO ≤ C.eB - C.gain := by
  have hO : C.eO ≤ C.ehatO + C.rhoO := by
    have h := abs_le.mp C.calibO_abs
    linarith [h.1]
  have hB : C.ehatB ≤ C.eB + C.rhoB := by
    have h := abs_le.mp C.calibB_abs
    linarith [h.2]
  dsimp [CalibratedProxyGain.gain]
  linarith [hO, hB, C.proxy_improves]

/-- Unified scalar interface consumed by the certified-gain descent theorem. -/
structure CertifiedGainInterface where
  CR : ℝ
  Q : ℝ
  b : ℝ
  eO : ℝ
  eB : ℝ
  gain : ℝ
  gain_nonneg : 0 ≤ gain
  baseline_bound : eB ≤ CR * Q + b
  comparison_bound : eO ≤ eB - gain

/-- Baseline residual control and calibrated comparison yield the strengthened
`R2` certificate with a nonnegative true gain. -/
theorem CertifiedGainInterface.r2_certified
    (C : CertifiedGainInterface) :
    C.eO ≤ C.CR * C.Q + C.b - C.gain := by
  nlinarith [C.baseline_bound, C.comparison_bound]

/-- Construct the public certified-gain interface from a calibrated proxy
comparison, a baseline residual bound, and the acceptance test `0 ≤ gain`. -/
def CalibratedProxyGain.toCertifiedGainInterface
    (C : CalibratedProxyGain) (CR Q b : ℝ)
    (hbaseline : C.eB ≤ CR * Q + b)
    (hgain : 0 ≤ C.gain) : CertifiedGainInterface where
  CR := CR
  Q := Q
  b := b
  eO := C.eO
  eB := C.eB
  gain := C.gain
  gain_nonneg := hgain
  baseline_bound := hbaseline
  comparison_bound := C.true_error_improves

/-- Fallback is the zero-gain special case: the accepted response equals the
baseline response and therefore preserves the same residual-to-error bound. -/
def CertifiedGainInterface.fallback
    (CR Q b eB : ℝ) (hbaseline : eB ≤ CR * Q + b) :
    CertifiedGainInterface where
  CR := CR
  Q := Q
  b := b
  eO := eB
  eB := eB
  gain := 0
  gain_nonneg := le_rfl
  baseline_bound := hbaseline
  comparison_bound := by simp

end

end OUSVRBLO
