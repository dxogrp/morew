import PTran

/-!
# Certified complete conic reformulations

Bare `conic` finishes a script and stores the affine cone program data. Objective
bounds and coordinate substitutions remain explicit steps chosen by the user.
-/

namespace Examples.Conic

open PTran
open Real
noncomputable section

namespace Linear

def p :=
  problem (x y : ℝ)
    minimize x + 2 * y
    subject to
      nonnegative : 0 ≤ x ∧ 0 ≤ y
      balance : x + y = 1

reformulation conicProb : p := by
  conic

#printp conicProb
#check conicProb.conicForm.data
example : GlobalEquivalence p conicProb := conicProb.equivalence
example : conicProb.conicForm.data.toProblem = conicProb := conicProb.conicForm.represents
example : IsConic conicProb := conicProb.isConic

end Linear

namespace LogSquared

def p :=
  problem (x : ℝ)
    minimize (log x) ^ 2
    subject to
      positive : 0 < x

reformulation conicProb : p := by
  substitute x := exp u
  epigraph t
  conic

#printp conicProb
example : GlobalEquivalence p conicProb := conicProb.equivalence
example : IsConic conicProb := conicProb.isConic

end LogSquared

namespace Softplus

def p :=
  problem (x : ℝ)
    minimize Fn.softplus x
    subject to
      lower : -2 ≤ x

-- Terminal validation introduces the
-- finite auxiliary vector belonging to the softplus representation.
reformulation conicProb : p := by
  epigraph t as loss
  conic

#printp conicProb
#check conicProb.conicForm.data
example : GlobalEquivalence p conicProb := conicProb.equivalence

end Softplus
end
end Examples.Conic
