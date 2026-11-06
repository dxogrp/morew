/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Multiplicative calibration

Given positive measurements `zᵢ`, fit the model `zᵢ ≈ x ^ aᵢ * y ^ bᵢ`
with parameters `x, y > 0`. Set `cᵢ = log zᵢ` and minimize the squared
errors in the logarithms:

```math
\begin{array}{ll}
\text{minimize} & \sum_i (a_i \log x + b_i \log y - c_i)^2 \\
\text{subject to} & x > 0, \quad y > 0.
\end{array}
```

Set `x = exp u` and `y = exp v`. The error becomes `aᵢ u + bᵢ v - cᵢ`,
which is linear in `u` and `v`. Let `t` bound the sum of squares:

```math
\begin{array}{ll}
\text{minimize} & t \\
\text{subject to} & \sum_i (a_i u + b_i v - c_i)^2 \leq t.
\end{array}
```

Morew writes this quadratic inequality as a rotated second-order cone constraint.
The original variables are recovered as `x = exp u` and `y = exp v`.
-/

namespace Examples.Applications.Calibration

open Morew
noncomputable section

def calibration (a b c : Fin m → ℝ) :=
  problem (x y : ℝ)
    minimize ∑ i, (a i * Real.log x + b i * Real.log y - c i) ^ 2
    subject to
      positiveX : 0 < x
      positiveY : 0 < y

variable (a b c : Fin m → ℝ)

-- Change variables, then bound the objective by t.
reformulation logEpigraphCalibration : (calibration a b c) := by
  substitute x := Real.exp u
  substitute y := Real.exp v
  epigraph t as residualBound

#printp calibration
#printp logEpigraphCalibration

example : GlobalEquiv (calibration a b c) (logEpigraphCalibration a b c) :=
  logEpigraphCalibration.equiv a b c

-- Write the quadratic bound as a cone constraint.
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

-- Recover x = exp u and y = exp v.
example (u v : ℝ) : (calibration a b c).feasible (Real.exp u, Real.exp v) :=
  ⟨Real.exp_pos u, Real.exp_pos v⟩

example (u v : ℝ) :
    (calibration a b c).objective (Real.exp u, Real.exp v) =
      ∑ i, (a i * u + b i * v - c i) ^ 2 := by
  simp [calibration]

-- An optimal point of the conic problem gives an optimal point of the original problem.
example {z : FeasiblePoint (conicCalibration a b c)}
    (hz : (conicCalibration a b c).IsGlobalOptimum z) :
    (calibration a b c).IsGlobalOptimum ((calibrationEquivConic a b c).backward.map z) :=
  (calibrationEquivConic a b c).map_isGlobalOptimum_backward hz

end
end Examples.Applications.Calibration
