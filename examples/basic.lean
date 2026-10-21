import PTran

open PTran

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
noncomputable

def shifted (a : ℝ) :=
  problem (x : ℝ)
    minimize (x - a)^2
    subject to
      lower : x ≥ a

-- Printing the family retains the parameter `a` symbolically.
#printp shifted
#check shifted 3

end parameterized
