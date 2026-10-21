import PTran

open PTran

/-
Second-order cone rewriting
-/
namespace soc
noncomputable

def leastSquares :=
  problem (x : Fin 2 → ℝ)
    minimize (x 0 - 1) ^ 2 + (x 1 + 2) ^ 2
    subject to
      radius : ‖WithLp.toLp 2 x‖ ≤ 5

reformulation coneBound : leastSquares := by
  conic at radius
  epigraph t as objectiveBound

#printp coneBound
#check coneBound.equivalence

end soc

namespace quadoverlin
noncomputable

def original :=
  problem (x y : ℝ)
    minimize x ^ 2 / y
    subject to
      denominator : 1 ≤ y

-- The retained denominator bound certifies positivity for the quotient rewrite.
reformulation lowered : original := by
  epigraph t as quadraticBound
  conic at quadraticBound

#printp original
#printp lowered
#check lowered.equivalence

end quadoverlin
