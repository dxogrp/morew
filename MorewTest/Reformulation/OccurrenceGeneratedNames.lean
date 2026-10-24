import Morew.Reformulation.Command

/-!
# Occurrence selectors referencing generated decisions

Selectors use the current visible decision names after lifts and substitution.
Nested lexical binders and macro scopes still retain their own identities.
-/

namespace MorewTest.Reformulation.OccurrenceGeneratedNames

open Morew
noncomputable section

def source :=
  problem (x : ℝ)
    minimize Real.exp (x ^ 2) + |x|

reformulation chained : source := by
  epigraph a at (x ^ 2)
  epigraph b at (Real.exp a)

example : GlobalEquivalence source chained := chained.equivalence
example (x a b : ℝ) : chained.objective ((x, a), b) = b + |x| := rfl
example (x a b : ℝ) : chained.feasible ((x, a), b) ↔
    x ^ 2 ≤ a ∧ Real.exp a ≤ b := Iff.rfl

/--
info: problem (x a b : ℝ)
  minimize b + |x|
  subject to
    epigraph_a : x ^ 2 ≤ a
    epigraph_b : Real.exp a ≤ b
-/
#guard_msgs in
#printp chained

reformulation inConstraint : source := by
  epigraph t
  epigraph a at (x ^ 2) in epigraph_t
  epigraph b at (Real.exp a) in epigraph_t

example : GlobalEquivalence source inConstraint := inConstraint.equivalence
example (x t a b : ℝ) : inConstraint.objective (((x, t), a), b) = t := rfl
example (x t a b : ℝ) : inConstraint.feasible (((x, t), a), b) ↔
    b + |x| ≤ t ∧ x ^ 2 ≤ a ∧ Real.exp a ≤ b := Iff.rfl

reformulation wholeThenSelection : source := by
  epigraph t
  epigraph s at (t)

example : GlobalEquivalence source wholeThenSelection := wholeThenSelection.equivalence
example (x t s : ℝ) : wholeThenSelection.objective ((x, t), s) = s := rfl
example (x t s : ℝ) : wholeThenSelection.feasible ((x, t), s) ↔
    Real.exp (x ^ 2) + |x| ≤ t ∧ t ≤ s := Iff.rfl

def logarithmic :=
  problem (x : ℝ)
    minimize (Real.log x) ^ 2 + |Real.log x|
    subject to
      positive : 0 < x

reformulation substituted : logarithmic := by
  substitute x := Real.exp u
  epigraph t at (u ^ 2)

example : GlobalEquivalence logarithmic substituted := substituted.equivalence
example (u t : ℝ) : substituted.objective (u, t) = t + |u| := rfl
example (u t : ℝ) : substituted.feasible (u, t) ↔ u ^ 2 ≤ t := Iff.rfl

reformulation first : source := by
  epigraph a at (x ^ 2)

reformulation continued : first := by
  epigraph b at (Real.exp a)

example : GlobalEquivalence first continued := continued.equivalence
example (x a b : ℝ) : continued.objective ((x, a), b) = b + |x| := rfl
example (x a b : ℝ) : continued.feasible ((x, a), b) ↔
    x ^ 2 ≤ a ∧ Real.exp a ≤ b := Iff.rfl

private def applyFunction (f : ℝ → ℝ) (value : ℝ) : ℝ := f value

def nestedBinder :=
  problem (x : ℝ)
    minimize applyFunction (fun a : ℝ => a) (x ^ 2) + |x|

-- The selector's lambda-bound `a` must remain distinct from the generated
-- decision `a` used as the function's argument.
reformulation nestedBinderLifted : nestedBinder := by
  epigraph a at (x ^ 2) using (by
    refine { atValue := ?_, backward := ?_ }
    · intro point
      rfl
    · intro point _ auxiliary bound
      change point ^ 2 + |point| ≤ auxiliary + |point|
      exact add_le_add bound le_rfl)
  epigraph b at (applyFunction (fun a : ℝ => a) a)

example : GlobalEquivalence nestedBinder nestedBinderLifted := nestedBinderLifted.equivalence
example (x a b : ℝ) : nestedBinderLifted.objective ((x, a), b) = b + |x| := rfl
example (x a b : ℝ) : nestedBinderLifted.feasible ((x, a), b) ↔
    x ^ 2 ≤ a ∧ a ≤ b := Iff.rfl

macro "liftGenerated " target:ident " from " original:ident " with " decision:ident : command =>
  `(reformulation $target : $original := by
    epigraph a at ($decision ^ 2)
    epigraph b at (Real.exp a))

liftGenerated macroLifted from source with x

example : GlobalEquivalence source macroLifted := macroLifted.equivalence
example (x a b : ℝ) : macroLifted.objective ((x, a), b) = b + |x| := rfl
example (x a b : ℝ) : macroLifted.feasible ((x, a), b) ↔
    x ^ 2 ≤ a ∧ Real.exp a ≤ b := Iff.rfl

def projected := problem (x : ℝ) minimize (x, x).1

-- Field notation must resolve the generated base name before its projection.
reformulation projectedLifted : projected := by
  epigraph a at ((x, x)) using (by
    refine { atValue := ?_, backward := ?_ }
    · intro point
      rfl
    · intro point _ auxiliary bound
      exact bound.1)
  epigraph t at (a.1)

example : GlobalEquivalence projected projectedLifted := projectedLifted.equivalence
example (x a b t : ℝ) : projectedLifted.objective ((x, (a, b)), t) = t := rfl
example (x a b t : ℝ) : projectedLifted.feasible ((x, (a, b)), t) ↔
    (x ≤ a ∧ x ≤ b) ∧ a ≤ t := Iff.rfl

end
end MorewTest.Reformulation.OccurrenceGeneratedNames
