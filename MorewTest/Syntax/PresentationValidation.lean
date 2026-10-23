import Morew.Syntax

/-!
# Problem presentation validation

Reject declarations whose recorded presentation is not a whole problem, and
reject structurally invalid or unprintable metadata with specific diagnostics.
-/

namespace MorewTest.Syntax.PresentationValidation

open Morew

def nestedProblem : Nat × Problem Nat Nat :=
  (37, problem (x : Nat) minimize x)

/--
error: declaration `MorewTest.Syntax.PresentationValidation.nestedProblem` has problem presentation metadata but is not a `Morew.Problem`
-/
#guard_msgs in
#printp nestedProblem

def parameterizedNestedProblem (a : Nat) : Nat × Problem Nat Nat :=
  (a, problem (x : Nat) minimize x + a)

/--
error: declaration `MorewTest.Syntax.PresentationValidation.parameterizedNestedProblem` has problem presentation metadata but is not a `Morew.Problem`
-/
#guard_msgs in
#printp parameterizedNestedProblem

/-! Structurally invalid presentation metadata is rejected explicitly. -/

def malformedProblem : Problem Nat Nat where
  objective := id
  feasible := fun _ => True

run_cmd do
  Morew.Syntax.registerProblemView `MorewTest.Syntax.PresentationValidation.malformedProblem {
    sense := .minimize
    binders := #[]
    objective := Lean.Syntax.mkNumLit "0"
  }

/-- error: problem presentation metadata contains no decision-variable binders -/
#guard_msgs in
#printp malformedProblem

def duplicateBinderProblem : Problem (Nat × Nat) Nat where
  objective := fun x => x.1
  feasible := fun _ => True

run_cmd do
  Morew.Syntax.registerProblemView `MorewTest.Syntax.PresentationValidation.duplicateBinderProblem {
    sense := .minimize
    binders := #[
      { name := `x, typeSyntax := Lean.mkIdent `Nat },
      { name := `x, typeSyntax := Lean.mkIdent `Nat }
    ]
    objective := Lean.mkIdent `x
  }

/-- error: problem presentation metadata contains duplicate decision variable name `x` -/
#guard_msgs in
#printp duplicateBinderProblem

def duplicateConstraintProblem : Problem Nat Nat where
  objective := id
  feasible := fun _ => True

run_cmd do
  Morew.Syntax.registerProblemView `MorewTest.Syntax.PresentationValidation.duplicateConstraintProblem {
    sense := .minimize
    binders := #[{ name := `x, typeSyntax := Lean.mkIdent `Nat }]
    objective := Lean.mkIdent `x
    constraints := #[
      { name := `c, proposition := Lean.mkIdent `True },
      { name := `c, proposition := Lean.mkIdent `True }
    ]
  }

/-- error: problem presentation metadata contains duplicate constraint name `c` -/
#guard_msgs in
#printp duplicateConstraintProblem

def unprintableProblem : Problem Nat Nat where
  objective := id
  feasible := fun _ => True

run_cmd do
  Morew.Syntax.registerProblemView `MorewTest.Syntax.PresentationValidation.unprintableProblem {
    sense := .minimize
    binders := #[{ name := `x, typeSyntax := Lean.mkIdent `Nat }]
    objective := .missing
  }

/-- error: problem presentation metadata contains unprintable objective syntax -/
#guard_msgs in
#printp unprintableProblem

def anonymousBinderProblem : Problem Nat Nat where
  objective := id
  feasible := fun _ => True

run_cmd do
  Morew.Syntax.registerProblemView `MorewTest.Syntax.PresentationValidation.anonymousBinderProblem {
    sense := .minimize
    binders := #[{ name := .anonymous, typeSyntax := Lean.mkIdent `Nat }]
    objective := Lean.Syntax.mkNumLit "0"
  }

/--
error: problem presentation metadata contains unprintable decision variable name
-/
#guard_msgs in
#printp anonymousBinderProblem

def anonymousConstraintProblem : Problem Nat Nat where
  objective := id
  feasible := fun _ => True

run_cmd do
  Morew.Syntax.registerProblemView `MorewTest.Syntax.PresentationValidation.anonymousConstraintProblem {
    sense := .minimize
    binders := #[{ name := `x, typeSyntax := Lean.mkIdent `Nat }]
    objective := Lean.mkIdent `x
    constraints := #[{ name := .anonymous, proposition := Lean.mkIdent `True }]
  }

/--
error: problem presentation metadata contains unprintable constraint name
-/
#guard_msgs in
#printp anonymousConstraintProblem

def anonymousTermProblem : Problem Nat Nat where
  objective := id
  feasible := fun _ => True

run_cmd do
  Morew.Syntax.registerProblemView `MorewTest.Syntax.PresentationValidation.anonymousTermProblem {
    sense := .minimize
    binders := #[{ name := `x, typeSyntax := Lean.mkIdent `Nat }]
    objective := Lean.mkIdent .anonymous
  }

/--
error: problem presentation metadata contains unprintable objective syntax
-/
#guard_msgs in
#printp anonymousTermProblem

end MorewTest.Syntax.PresentationValidation
