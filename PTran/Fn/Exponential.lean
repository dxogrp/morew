import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite exponential modeling functions

These are ordinary real-valued functions, with the totalized semantics of
`Real.log` and real division. In particular, empty log-sum-exp is zero and
relative entropy is zero when its denominator is zero. Exact conic rewrites
therefore certify nonempty indexing and the intended domains separately.
-/

namespace PTran.Fn

/-- The logarithm of a finite sum of exponentials. At dimension zero its value
is `Real.log 0 = 0`; the exponential-cone representation requires `0 < n`. -/
noncomputable def logSumExp {n : Nat} (xs : Fin n → ℝ) : ℝ :=
  Real.log (∑ i, Real.exp (xs i))

/-- Softplus, the two-term log-sum-exp of zero and its argument. -/
noncomputable def softplus (a : ℝ) : ℝ :=
  Real.log (1 + Real.exp a)

/-- The real formula for relative entropy. Its usual finite domain is
`0 ≤ a` and `0 < b`, including the zero boundary `a = 0`. This definition
does not encode an infinite value outside that domain. -/
noncomputable def relativeEntropy (a b : ℝ) : ℝ :=
  a * Real.log (a / b)

end PTran.Fn
