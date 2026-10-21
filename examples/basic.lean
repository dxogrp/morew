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

/-
Targeted polyhedral rewriting
-/
namespace polyhedral
noncomputable

def absoluteObjective :=
  problem (x : ℝ)
    minimize |x - 2|
    subject to
      magnitude : |x| ≤ 5
      nonnegative : 0 ≤ x

reformulation linearBounds : absoluteObjective := by
  conic at magnitude
  epigraph t as distance
  conic at distance

#printp linearBounds
#check linearBounds.equivalence

end polyhedral

/-
Targeted second-order cone rewriting
-/
namespace secondOrder
noncomputable

def leastSquares :=
  problem (x : Fin 2 → ℝ)
    minimize (x 0 - 1) ^ 2 + (x 1 + 2) ^ 2
    subject to
      radius : ‖WithLp.toLp 2 x‖ ≤ 5

reformulation coneBound : leastSquares := by
  conic at radius
  epigraph t as objectiveBound

-- The retained bound is an actual cone-membership row; the certificate relates
-- the original problem to the result after both exact transformations.
#printp coneBound
#check coneBound.equivalence

end secondOrder
