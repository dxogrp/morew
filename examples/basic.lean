import PTran

open PTran
noncomputable

section noneg_quad

def p :=
  problem (x : ℝ)
    minimize x^2
    subject to
      nonneg : x ≥ 0

reformulation pepi : p := by
  epigraph t as objective_bound

#printp p
#printp pepi
#check pepi.equivalence

end noneg_quad
