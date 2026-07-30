import OUSVRBLO.ValueGradientErrorEmbedding

namespace OUSVRBLO

noncomputable section

/-- Calibration radius induced by a proxy-gradient error `delta` and a candidate
value-gradient error bound `B`. -/
def proxyCalibrationRadius (delta B : ℝ) : ℝ :=
  delta * (2 * B + delta)

/-- The induced calibration radius is nonnegative for nonnegative inputs. -/
theorem proxyCalibrationRadius_nonneg
    (delta B : ℝ) (hdelta : 0 ≤ delta) (hB : 0 ≤ B) :
    0 ≤ proxyCalibrationRadius delta B := by
  exact mul_nonneg hdelta (add_nonneg (mul_nonneg (by norm_num) hB) hdelta)

/--
A proxy-gradient approximation bound produces a computable calibration radius
for the squared candidate error.

If `gProxy` approximates the represented value gradient `gValue` within
`delta`, and the candidate response gradient is within `B` of `gValue`, then

`| ||gCandidate-gProxy||^2 - ||gCandidate-gValue||^2 |
   <= delta * (2*B + delta)`.

No separate `B >= 0` premise is needed: it follows automatically whenever the
candidate norm is bounded above by `B`.
-/
theorem proxy_squared_error_calibrated_of_gradient_bounds
    {G : Type*} [NormedAddCommGroup G]
    (gCandidate gProxy gValue : G) (delta B : ℝ)
    (hdelta : 0 ≤ delta)
    (hproxy : ‖gProxy - gValue‖ ≤ delta)
    (hcandidate : ‖gCandidate - gValue‖ ≤ B) :
    |‖gCandidate - gProxy‖ ^ 2 - ‖gCandidate - gValue‖ ^ 2| ≤
      proxyCalibrationRadius delta B := by
  let u : ℝ := ‖gCandidate - gProxy‖
  let v : ℝ := ‖gCandidate - gValue‖
  have hproxyRev : ‖gValue - gProxy‖ ≤ delta := by
    simpa [norm_sub_rev] using hproxy
  have hproxyForward : ‖gProxy - gValue‖ ≤ delta := hproxy
  have hv_bound : v ≤ B := by
    simpa [v] using hcandidate
  have hu_le_v_add : u ≤ v + delta := by
    calc
      u = ‖(gCandidate - gValue) + (gValue - gProxy)‖ := by
        dsimp [u, v]
        congr 1
        abel
      _ ≤ ‖gCandidate - gValue‖ + ‖gValue - gProxy‖ := norm_add_le _ _
      _ ≤ v + delta := by
        dsimp [v]
        exact add_le_add le_rfl hproxyRev
  have hv_le_u_add : v ≤ u + delta := by
    calc
      v = ‖(gCandidate - gProxy) + (gProxy - gValue)‖ := by
        dsimp [u, v]
        congr 1
        abel
      _ ≤ ‖gCandidate - gProxy‖ + ‖gProxy - gValue‖ := norm_add_le _ _
      _ ≤ u + delta := by
        dsimp [u]
        exact add_le_add le_rfl hproxyForward
  have habs : |u - v| ≤ delta := by
    apply abs_le.mpr
    constructor <;> linarith
  have hu_bound : u ≤ B + delta := by
    linarith [hu_le_v_add, hv_bound]
  have hsum : u + v ≤ 2 * B + delta := by
    linarith [hu_bound, hv_bound]
  have hsum_nonneg : 0 ≤ u + v :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hprod := mul_le_mul habs hsum hsum_nonneg hdelta
  calc
    |‖gCandidate - gProxy‖ ^ 2 - ‖gCandidate - gValue‖ ^ 2|
        = |u ^ 2 - v ^ 2| := by rfl
    _ = |(u - v) * (u + v)| := by
      congr 1
      ring
    _ = |u - v| * |u + v| := abs_mul _ _
    _ = |u - v| * (u + v) := by rw [abs_of_nonneg hsum_nonneg]
    _ ≤ delta * (2 * B + delta) := hprod
    _ = proxyCalibrationRadius delta B := by
      rfl

/-- Asymmetric proposal/base calibration radii generated from one proxy-gradient
error bound and separate candidate-gradient error bounds. -/
theorem asymmetric_proxy_squared_error_calibration
    {G : Type*} [NormedAddCommGroup G]
    (gProp gBase gProxy gValue : G)
    (delta BProp BBase : ℝ)
    (hdelta : 0 ≤ delta)
    (hproxy : ‖gProxy - gValue‖ ≤ delta)
    (hprop : ‖gProp - gValue‖ ≤ BProp)
    (hbase : ‖gBase - gValue‖ ≤ BBase) :
    |‖gProp - gProxy‖ ^ 2 - ‖gProp - gValue‖ ^ 2| ≤
        proxyCalibrationRadius delta BProp ∧
      |‖gBase - gProxy‖ ^ 2 - ‖gBase - gValue‖ ^ 2| ≤
        proxyCalibrationRadius delta BBase := by
  constructor
  · exact proxy_squared_error_calibrated_of_gradient_bounds
      gProp gProxy gValue delta BProp hdelta hproxy hprop
  · exact proxy_squared_error_calibrated_of_gradient_bounds
      gBase gProxy gValue delta BBase hdelta hproxy hbase

/-- Sequence-level form used to instantiate asymmetric calibration assumptions at
each proposal round. -/
theorem asymmetric_proxy_squared_error_calibration_sequence
    {G : Type*} [NormedAddCommGroup G]
    (gProp gBase gProxy gValue : ℕ → G)
    (delta BProp BBase : ℕ → ℝ)
    (hdelta : ∀ t, 0 ≤ delta t)
    (hproxy : ∀ t, ‖gProxy t - gValue t‖ ≤ delta t)
    (hprop : ∀ t, ‖gProp t - gValue t‖ ≤ BProp t)
    (hbase : ∀ t, ‖gBase t - gValue t‖ ≤ BBase t)
    (t : ℕ) :
    |‖gProp t - gProxy t‖ ^ 2 - ‖gProp t - gValue t‖ ^ 2| ≤
        proxyCalibrationRadius (delta t) (BProp t) ∧
      |‖gBase t - gProxy t‖ ^ 2 - ‖gBase t - gValue t‖ ^ 2| ≤
        proxyCalibrationRadius (delta t) (BBase t) :=
  asymmetric_proxy_squared_error_calibration
    (gProp t) (gBase t) (gProxy t) (gValue t)
    (delta t) (BProp t) (BBase t)
    (hdelta t) (hproxy t) (hprop t) (hbase t)

end

end OUSVRBLO