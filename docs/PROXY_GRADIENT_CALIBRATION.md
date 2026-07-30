# Proxy-gradient calibration certificate

## 1. Purpose

The proposal selector compares computable squared proxy errors with true squared
value-gradient errors. The main theorem permits calibration radii as explicit
interfaces. `OUSVRBLO/ProxyCalibrationFromGradient.lean` now gives a local
sufficient condition for those radii from vector-gradient bounds.

## 2. Scalar certificate

Let

```text
gValue       represented value gradient,
gProxy       computable proxy gradient,
gCandidate   response-induced candidate gradient.
```

Assume

```text
||gProxy - gValue|| <= delta,
||gCandidate - gValue|| <= B,
delta >= 0.
```

Define

```text
eTrue  = ||gCandidate - gValue||^2,
eProxy = ||gCandidate - gProxy||^2,
rho    = delta * (2 * B + delta).
```

The reverse triangle inequality gives

```text
| ||gCandidate-gProxy|| - ||gCandidate-gValue|| | <= delta.
```

The ordinary triangle inequality gives

```text
||gCandidate-gProxy|| + ||gCandidate-gValue||
  <= 2 * B + delta.
```

Therefore

```text
|eProxy - eTrue|
  = |u^2 - v^2|
  = |u-v| * (u+v)
  <= delta * (2 * B + delta)
  = rho.
```

Lean declaration:

```text
proxy_squared_error_calibrated_of_gradient_bounds
```

No independent nonnegativity premise for `B` is required: if a norm is bounded
above by `B`, then `B` is automatically nonnegative.

## 3. Asymmetric proposal/base radii

For proposal and base gradients with separate candidate bounds,

```text
||gProp - gValue|| <= BProp,
||gBase - gValue|| <= BBase,
```

the same proxy-gradient error bound produces

```text
rhoProp = delta * (2 * BProp + delta),
rhoBase = delta * (2 * BBase + delta).
```

Lean verifies both calibration inequalities simultaneously:

```text
| ||gProp-gProxy||^2 - ||gProp-gValue||^2 | <= rhoProp,
| ||gBase-gProxy||^2 - ||gBase-gValue||^2 | <= rhoBase.
```

Declarations:

```text
asymmetric_proxy_squared_error_calibration
asymmetric_proxy_squared_error_calibration_sequence
```

## 4. Connection to acceptance

The selector's uncertainty-adjusted margin is

```text
Gamma = DeltaHat - tauE - rhoProp - rhoBase.
```

The new certificate permits the calibration terms to be instantiated as

```text
rhoProp = delta * (2 * BProp + delta),
rhoBase = delta * (2 * BBase + delta).
```

Thus the nonnegative-gain acceptance condition becomes the interpretable test

```text
DeltaHat >= tauE
  + delta * (2 * BProp + delta)
  + delta * (2 * BBase + delta).
```

Only nominal proxy improvement that exceeds acceptance tolerance and both
vector-derived calibration radii enters the Lyapunov budget.

## 5. Claim boundary

The theorem does not by itself construct `gProxy`, `delta`, `BProp`, or `BBase`
for a concrete neural model. It proves the deterministic implication

```text
proxy-gradient accuracy + candidate-gradient bounds
  => squared-error proxy calibration.
```

How these quantities are estimated for a specific LLM/LoRA trajectory remains a
model-specific analytic interface.
