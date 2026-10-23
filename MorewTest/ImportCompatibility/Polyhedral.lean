import MorewTest.ImportCompatibility.Polyhedral.Defined

/-!
# Imported targeted-rewrite presentation

Generated row names survive module serialization, and a retained constraint can
be selected by a subsequent reformulation in the importing module. The symbolic
vector case also extends the domain and then composes with an epigraph step.
-/

namespace MorewTest.ImportCompatibility.Polyhedral

open Morew
noncomputable section

/--
info: problem (x : ℝ)
  minimize x ^ 2
  subject to
    loss_conic_1 : x ≤ 3
    loss_conic_2 : -x ≤ 3
    remaining : max x (-x) ≤ 5
-/
#guard_msgs in
#printp lowered

reformulation continued : lowered := by
  conic at remaining

example : GlobalEquivalence lowered continued := continued.equivalence

example (x : ℝ) : continued.feasible x ↔ x ≤ 3 ∧ -x ≤ 3 ∧ x ≤ 5 ∧ -x ≤ 5 := Iff.rfl

namespace SymbolicDimension

variable [Dimension]

reformulation continued : lowered := by
  conic at one
  epigraph bound as value

example : GlobalEquivalence lowered continued := continued.equivalence

example : GlobalEquivalence source continued :=
  lowered.equivalence.trans continued.equivalence

example (v u : Fin Dimension.size → ℝ) (t bound : ℝ) :
    continued.objective (((v, t), u), bound) = bound := rfl

example (v u : Fin Dimension.size → ℝ) (t bound : ℝ) :
    continued.feasible (((v, t), u), bound) ↔
      0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) ∧
        v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t ∧ t ≤ bound := Iff.rfl

end SymbolicDimension

end
end MorewTest.ImportCompatibility.Polyhedral
