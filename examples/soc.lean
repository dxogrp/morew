import PTran

open PTran

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

-- The generated row is (t, y / 2, ![x]) ∈ RSOC 1.
#printp original
#printp lowered
#check lowered.equivalence

end quadoverlin
