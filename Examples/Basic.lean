import PTran

open PTran
open Real

/-
Epigraph rewriting example
-/
namespace Examples.Basic

namespace Epigraph
noncomputable

def p :=
  problem (x : ℝ)
    minimize x^2
    subject to
      nonneg : x ≥ 0

#printp p

-- Default epigraph rewriting
reformulation epigraphForm : p := by
  epigraph t

#printp epigraphForm
#check epigraphForm.equivalence

-- Epigraph rewriting with explicit label
reformulation labeledEpigraphForm : p := by
  epigraph t as objectiveBound

#printp labeledEpigraphForm
#check labeledEpigraphForm.equivalence

end Epigraph

/-
Parameterized problem examples
-/
namespace Parameterized
noncomputable section

def p (a : ℝ) :=
  problem (x : ℝ)
    minimize (x - a)^2
    subject to
      lower : x ≥ a

-- Printing the family retains the parameter `a` symbolically.
#printp p

-- Reformulate a particular member of the problem family.
reformulation concreteEpigraph : (p 3) := by
  epigraph t

#printp concreteEpigraph
example : GlobalEquivalence (p 3) concreteEpigraph := concreteEpigraph.equivalence

section

variable (shift : ℝ)

-- A local argument produces a reformulation family with the same parameter.
reformulation shiftedEpigraph : (p shift) := by
  epigraph t

example : GlobalEquivalence (p shift) (shiftedEpigraph shift) :=
  shiftedEpigraph.equivalence shift

end

#printp shiftedEpigraph

end
end Parameterized

/-
Substitute and epigraph rewriting example
-/
namespace LogSquared
noncomputable section

def p :=
  problem (x : ℝ)
    minimize (log x)^2
    subject to
      pos : x > 0

#printp p

reformulation exponentialEpigraph : p := by
  substitute x := exp u
  epigraph t

#printp exponentialEpigraph
example : GlobalEquivalence p exponentialEpigraph := exponentialEpigraph.equivalence

end
end LogSquared

/-
Targeted polyhedral rewriting
-/
namespace Polyhedral
noncomputable section

def p :=
  problem (x : ℝ)
    minimize |x - 2|
    subject to
      magnitude : |x| ≤ 5
      nonnegative : 0 ≤ x

reformulation linearBounds : p := by
  conic at magnitude
  epigraph t as distance
  conic at distance

#printp linearBounds
example : GlobalEquivalence p linearBounds := linearBounds.equivalence

end
end Polyhedral

end Examples.Basic
