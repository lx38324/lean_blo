import Mathlib

namespace OUSVRBLO

noncomputable section

/--
Scalar proxy-comparison certificate from the manuscript.

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
Combines a baseline value-gradient error bound with the proxy comparison
certificate to produce the enhanced `R2+` interface.
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

end

end OUSVRBLO
