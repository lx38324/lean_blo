import OUSVRBLO.ProxyCertificate

namespace OUSVRBLO

noncomputable section

/--
Sequence-level asymmetric proxy comparison.  Its accepted gain is already
required to be nonnegative, so it can enter the Lyapunov budget directly.
-/
structure ProxyGainSequence where
  eO : ℕ → ℝ
  eB : ℕ → ℝ
  ehatO : ℕ → ℝ
  ehatB : ℕ → ℝ
  DeltaHat : ℕ → ℝ
  tauE : ℕ → ℝ
  rhoO : ℕ → ℝ
  rhoB : ℕ → ℝ
  rhoO_nonneg : ∀ t, 0 ≤ rhoO t
  rhoB_nonneg : ∀ t, 0 ≤ rhoB t
  tauE_nonneg : ∀ t, 0 ≤ tauE t
  calibO_abs : ∀ t, |ehatO t - eO t| ≤ rhoO t
  calibB_abs : ∀ t, |ehatB t - eB t| ≤ rhoB t
  proxy_improves :
    ∀ t, ehatO t ≤ ehatB t - DeltaHat t + tauE t
  accepted_gain_nonneg :
    ∀ t, 0 ≤ DeltaHat t - tauE t - rhoO t - rhoB t

/-- Uncertainty-adjusted true gain at round `t`. -/
def ProxyGainSequence.Gamma (S : ProxyGainSequence) (t : ℕ) : ℝ :=
  S.DeltaHat t - S.tauE t - S.rhoO t - S.rhoB t

/-- Scalar calibrated comparison extracted at one round. -/
def ProxyGainSequence.comparison
    (S : ProxyGainSequence) (t : ℕ) : CalibratedProxyGain where
  eO := S.eO t
  eB := S.eB t
  ehatO := S.ehatO t
  ehatB := S.ehatB t
  DeltaHat := S.DeltaHat t
  tauE := S.tauE t
  rhoO := S.rhoO t
  rhoB := S.rhoB t
  rhoO_nonneg := S.rhoO_nonneg t
  rhoB_nonneg := S.rhoB_nonneg t
  tauE_nonneg := S.tauE_nonneg t
  calibO_abs := S.calibO_abs t
  calibB_abs := S.calibB_abs t
  proxy_improves := S.proxy_improves t

@[simp]
theorem ProxyGainSequence.comparison_gain
    (S : ProxyGainSequence) (t : ℕ) :
    (S.comparison t).gain = S.Gamma t := by
  rfl

/-- Proxy calibration gives the true-error comparison at every round. -/
theorem ProxyGainSequence.true_error_improves
    (S : ProxyGainSequence) (t : ℕ) :
    S.eO t ≤ S.eB t - S.Gamma t := by
  simpa using (S.comparison t).true_error_improves

/-- The sequence of accepted uncertainty-adjusted gains is nonnegative. -/
theorem ProxyGainSequence.Gamma_nonneg
    (S : ProxyGainSequence) (t : ℕ) :
    0 ≤ S.Gamma t := by
  exact S.accepted_gain_nonneg t

/--
Add the common residual envelope and the baseline residual-to-error control.
-/
structure ProxyResidualCertificate extends ProxyGainSequence where
  CR : ℝ
  Q : ℕ → ℝ
  b : ℕ → ℝ
  baseline_bound : ∀ t, eB t ≤ CR * Q t + b t

/-- Per-round scalar interface consumed by the certified-gain theorem. -/
def ProxyResidualCertificate.interface
    (S : ProxyResidualCertificate) (t : ℕ) : CertifiedGainInterface where
  CR := S.CR
  Q := S.Q t
  b := S.b t
  eO := S.eO t
  eB := S.eB t
  gain := S.Gamma t
  gain_nonneg := S.Gamma_nonneg t
  baseline_bound := S.baseline_bound t
  comparison_bound := S.true_error_improves t

/-- Baseline residual control and proxy calibration yield sequence-level R2+. -/
theorem ProxyResidualCertificate.r2_certified
    (S : ProxyResidualCertificate) (t : ℕ) :
    S.eO t ≤ S.CR * S.Q t + S.b t - S.Gamma t := by
  exact (S.interface t).r2_certified

/--
If the actual inexact-gradient vector has squared norm bounded by
`lambda^2 * eO_t`, then proxy calibration produces the exact certified error
bound used by `AnalyticGainSystem`.
-/
theorem ProxyResidualCertificate.certified_error_bound
    {E : Type*} [NormedAddCommGroup E]
    (S : ProxyResidualCertificate) (lam : ℝ) (Err : ℕ → E)
    (hErr : ∀ t, ‖Err t‖ ^ 2 ≤ lam ^ 2 * S.eO t)
    (t : ℕ) :
    ‖Err t‖ ^ 2 ≤
      lam ^ 2 * (S.CR * S.Q t + S.b t - S.Gamma t) := by
  have hr2 := S.r2_certified t
  have hscaled := mul_le_mul_of_nonneg_left hr2 (sq_nonneg lam)
  exact (hErr t).trans hscaled

/--
Fallback sequence constructor.  The accepted response equals the baseline,
proxy gain is zero, and the baseline residual error bound is preserved.
-/
def ProxyResidualCertificate.fallback
    (CR : ℝ) (Q b eB : ℕ → ℝ)
    (hbaseline : ∀ t, eB t ≤ CR * Q t + b t) :
    ProxyResidualCertificate where
  eO := eB
  eB := eB
  ehatO := eB
  ehatB := eB
  DeltaHat := fun _ => 0
  tauE := fun _ => 0
  rhoO := fun _ => 0
  rhoB := fun _ => 0
  rhoO_nonneg := fun _ => le_rfl
  rhoB_nonneg := fun _ => le_rfl
  tauE_nonneg := fun _ => le_rfl
  calibO_abs := by intro t; simp
  calibB_abs := by intro t; simp
  proxy_improves := by intro t; simp
  accepted_gain_nonneg := by intro t; simp
  CR := CR
  Q := Q
  b := b
  baseline_bound := hbaseline

@[simp]
theorem ProxyResidualCertificate.fallback_Gamma
    (CR : ℝ) (Q b eB : ℕ → ℝ)
    (hbaseline : ∀ t, eB t ≤ CR * Q t + b t)
    (t : ℕ) :
    (ProxyResidualCertificate.fallback CR Q b eB hbaseline).Gamma t = 0 := by
  rfl

end

end OUSVRBLO
