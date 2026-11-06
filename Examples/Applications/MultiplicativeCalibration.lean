/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Multiplicative calibration

Estimate two positive quantities `x` and `y` from positive multiplicative measurements
`zᵢ ≈ x ^ aᵢ * y ^ bᵢ`. Write `cᵢ = log zᵢ` for the observed log measurements
and fit their squared residuals:

```math
\begin{array}{ll}
\text{minimize} & \sum_i (a_i \log x + b_i \log y - c_i)^2 \\
\text{subject to} & x > 0, \quad y > 0.
\end{array}
```

This models errors in the log measurements; it is not a reformulation of
least squares on the original measurements. For example, measurements of
`x`, `y`, and `x * y` use `a = (1, 0, 1)` and `b = (0, 1, 1)`.

The substitutions `x = exp u` and `y = exp v` reveal an unconstrained linear
least-squares problem in `u` and `v`. Positivity ensures that every original
feasible point has these logarithmic coordinates. Combining this substitution
with an epigraph lift gives one rotated second-order cone constraint:

```math
\begin{array}{ll}
\text{minimize} & t \\
\text{subject to} & (t, 1/2, (a_i u + b_i v - c_i)_i) \in \mathrm{RSOC}.
\end{array}
```

The certificates apply to every choice of measurement coefficients and log
observations. No rank assumption is needed for the reformulations.
-/

namespace Examples.Applications.MultiplicativeCalibration

open Morew
noncomputable section

def calibration (a b c : Fin m → ℝ) :=
  problem (x y : ℝ)
    minimize ∑ i, (a i * Real.log x + b i * Real.log y - c i) ^ 2
    subject to
      positiveX : 0 < x
      positiveY : 0 < y

variable (a b c : Fin m → ℝ)

-- Introduce the epigraph first, keeping a linear objective throughout the substitutions.
-- Each positivity constraint supplies the coverage proof for its substitution.
reformulation logEpigraphCalibration : (calibration a b c) := by
  epigraph t as residualBound
  substitute x := Real.exp u
  substitute y := Real.exp v

#printp calibration
#printp logEpigraphCalibration

example : GlobalEquiv (calibration a b c) (logEpigraphCalibration a b c) :=
  logEpigraphCalibration.equiv a b c

-- Lift the entire sum of squares into a single rotated second-order cone.
reformulation conicCalibration : (logEpigraphCalibration a b c) := by
  conic at residualBound
  rename residualBound_conic_1 to residualCone
  conic

#printp conicCalibration

def calibrationEquivConic : GlobalEquiv (calibration a b c) (conicCalibration a b c) :=
  (logEpigraphCalibration.equiv a b c).trans (conicCalibration.equiv a b c)

example : IsConic (conicCalibration a b c) := conicCalibration.isConic a b c
example : (conicCalibration.conicForm a b c).data.toProblem = conicCalibration a b c :=
  (conicCalibration.conicForm a b c).represents

-- Recover positive quantities from the logarithmic coordinates.
example (u v : ℝ) : (calibration a b c).feasible (Real.exp u, Real.exp v) :=
  ⟨Real.exp_pos u, Real.exp_pos v⟩

example (u v : ℝ) :
    (calibration a b c).objective (Real.exp u, Real.exp v) =
      ∑ i, (a i * u + b i * v - c i) ^ 2 := by
  simp [calibration]

-- A proof of target optimality transfers through the composed certificate.
example {z : FeasiblePoint (conicCalibration a b c)}
    (hz : (conicCalibration a b c).IsGlobalOptimum z) :
    (calibration a b c).IsGlobalOptimum ((calibrationEquivConic a b c).backward.map z) :=
  (calibrationEquivConic a b c).map_isGlobalOptimum_backward hz

end
end Examples.Applications.MultiplicativeCalibration
