/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite exponential modeling functions

Log-sum-exp, softplus, and relative entropy use the total real logarithm and
real division. Their conic representations impose the domains stated below.
-/

namespace Morew.Fn

/-- The logarithm of a finite sum of exponentials. At dimension zero its value
is `Real.log 0 = 0`; the exponential-cone representation requires `0 < n`. -/
noncomputable def logSumExp {n : Nat} (xs : Fin n → ℝ) : ℝ :=
  Real.log (∑ i, Real.exp (xs i))

/-- Softplus, the two-term log-sum-exp of zero and its argument. -/
noncomputable def softplus (a : ℝ) : ℝ :=
  Real.log (1 + Real.exp a)

/-- The total real formula for relative entropy. Its conic epigraph requires
`0 ≤ a` and `0 < b`, including the boundary `a = 0`. The formula evaluates to
zero when `b = 0`. -/
noncomputable def relativeEntropy (a b : ℝ) : ℝ :=
  a * Real.log (a / b)

end Morew.Fn
