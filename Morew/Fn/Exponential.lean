/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Finite exponential modeling functions

Log-sum-exp, softplus, relative entropy, and KL divergence use the total real
logarithm and real division. Their conic representations impose the domains
stated below. Entropy uses Mathlib's `Real.negMulLog`.
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
noncomputable def relEntr (a b : ℝ) : ℝ :=
  a * Real.log (a / b)

/-- The total real formula for KL divergence. Its conic epigraph requires
`0 ≤ a` and `0 < b`, including the boundary `a = 0`. -/
noncomputable def klDiv (a b : ℝ) : ℝ :=
  relEntr a b - a + b

/-- Relative entropy against one is the negative entropy contribution. -/
theorem relEntr_one_right (a : ℝ) : relEntr a 1 = -Real.negMulLog a := by
  simp [relEntr, Real.negMulLog]

/-- KL divergence at a zero first argument equals its second argument. -/
@[simp] theorem klDiv_zero_left (b : ℝ) : klDiv 0 b = b := by
  simp [klDiv, relEntr]

/-- The total KL formula vanishes when its arguments agree. -/
@[simp] theorem klDiv_self (a : ℝ) : klDiv a a = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [klDiv, relEntr, ha]

/-- KL divergence is nonnegative on its conic representation domain. -/
theorem klDiv_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ klDiv a b := by
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg ha hb.le)) hb.le
  have hba : b * (a / b) = a := mul_div_cancel₀ a hb.ne'
  rw [mul_sub, mul_one, ← mul_assoc, hba] at h
  change 0 ≤ a * Real.log (a / b) - a + b
  linarith

end Morew.Fn
