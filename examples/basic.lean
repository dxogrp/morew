import PTran

open PTran
noncomputable

/-
Epigraph rewriting example
-/
section epi_rw

def p :=
  problem (x : ℝ)
    minimize x^2
    subject to
      nonneg : x ≥ 0

#printp p

-- Default epigraph rewriting
section
reformulation pepi : p := by
  epigraph t

#printp pepi
#check pepi.equivalence
end

-- Epigraph rewriting with explicit label
section
reformulation pepi_lb : p := by
  epigraph t as epi_constr

#printp pepi_lb
#check pepi_lb.equivalence
end

end epi_rw
