import PTran.Reformulation

/-!
# Exported second-order reformulations

The producer retains section dimensions and coefficients, positive-margin
constraints, and generated cone-row labels for a later module.
-/

namespace PTranTest.ImportCompatibility.SecondOrder

open PTran PTran.Conic
noncomputable section

class Parameter where
  size : Nat
  offset : ℝ

variable [Parameter]

def source :=
  problem (v : Fin Parameter.size → ℝ) (x y t : ℝ)
    minimize t
    subject to
      norm : ‖WithLp.toLp 2 v‖ ≤ t
      margin : 1 / 2 ≤ y
      quotient : (x - Parameter.offset) ^ 2 / y ≤ t
      remaining : |x| ≤ 5

reformulation lowered : source := by
  conic at norm
  conic at quotient

example : GlobalEquivalence source lowered := lowered.equivalence

end
end PTranTest.ImportCompatibility.SecondOrder
