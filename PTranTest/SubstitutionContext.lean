import PTran

/-!
# Substitution elaboration contexts

Public reformulation scripts preserve source types and constraints across
section boundaries, instantiated parameters, and macro expansion. Nested
positivity aliases also compose through manual and automatic substitutions.
-/

namespace PTranTest.SubstitutionContext

open PTran
noncomputable section

namespace MacroGeneratedSubstitution

def source :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      positive : 0 < x

macro "contextGeneratedSubstitution " target:ident : command =>
  `(reformulation $target : source := by
      substitute x := Real.exp u)

contextGeneratedSubstitution target

example : GlobalEquivalence source target := target.equivalence

example (u : ℝ) : target.objective u = u := rfl
example (u : ℝ) : target.feasible u ↔ True := Iff.rfl

reformulation bounded : target := by
  epigraph t

example : GlobalEquivalence target bounded := bounded.equivalence

example (u t : ℝ) : bounded.objective (u, t) = t := rfl
example (u t : ℝ) : bounded.feasible (u, t) ↔ u ≤ t := Iff.rfl

end MacroGeneratedSubstitution

end
end PTranTest.SubstitutionContext
