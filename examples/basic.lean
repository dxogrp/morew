import PTran

open PTran
open Real

/-
Epigraph rewriting example
-/
namespace epi_rw
noncomputable

def p :=
  problem (x : ℝ)
    minimize x^2
    subject to
      nonneg : x ≥ 0

#printp p

-- Default epigraph rewriting
reformulation pepi : p := by
  epigraph t

#printp pepi
#check pepi.equivalence

-- Epigraph rewriting with explicit label
reformulation pepi_lb : p := by
  epigraph t as epi_constr

#printp pepi_lb
#check pepi_lb.equivalence

end epi_rw

/-
Parameterized problem examples
-/
namespace parameterized
noncomputable section

def p (a : ℝ) :=
  problem (x : ℝ)
    minimize (x - a)^2
    subject to
      lower : x ≥ a

-- Printing the family retains the parameter `a` symbolically.
#printp p
#check p 3

end
end parameterized

/-
Substitute and epigraph rewriting example
-/
namespace log_sq
noncomputable section

def p :=
  problem (x : ℝ)
    minimize (log x)^2
    subject to
      pos : x > 0

#printp p

reformulation pexp : p := by
  substitute x := exp u
  epigraph t

#printp pexp
example : GlobalEquivalence p pexp := pexp.equivalence

end
end log_sq

/-
Targeted polyhedral rewriting
-/
namespace polyhedral
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
end polyhedral
