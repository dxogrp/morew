import PTran.Syntax

/-!
# Problem presentation metadata edge cases

A `problem` term nested inside an unrelated declaration must not make that
declaration printable as though the whole declaration were a problem.
-/

namespace PTranTest.SyntaxEdge

open PTran

def nestedProblem : Nat × Problem Nat Nat :=
  (37, problem (x : Nat) minimize x)

/--
error: declaration `PTranTest.SyntaxEdge.nestedProblem` has problem presentation metadata but is not a `PTran.Problem`
-/
#guard_msgs in
#printp nestedProblem

/-! The guard must not reject a genuine top-level problem declaration. -/

def genuineProblem :=
  problem (x : Nat)
    minimize x

/--
info: problem (x : Nat)
  minimize x
-/
#guard_msgs in
#printp genuineProblem

/-! Transparent aliases of `Problem` are still genuine problem types. -/

abbrev NatProblem := Problem Nat Nat

def aliasedProblem : NatProblem :=
  problem (x : Nat)
    minimize x + 1

/--
info: problem (x : Nat)
  minimize x + 1
-/
#guard_msgs in
#printp aliasedProblem

/-! Structurally invalid presentation metadata is rejected explicitly. -/

def malformedProblem : Problem Nat Nat where
  objective := id
  feasible := fun _ => True

run_cmd do
  PTran.Syntax.registerProblemView `PTranTest.SyntaxEdge.malformedProblem {
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
  PTran.Syntax.registerProblemView `PTranTest.SyntaxEdge.duplicateBinderProblem {
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
  PTran.Syntax.registerProblemView `PTranTest.SyntaxEdge.duplicateConstraintProblem {
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
  PTran.Syntax.registerProblemView `PTranTest.SyntaxEdge.unprintableProblem {
    sense := .minimize
    binders := #[{ name := `x, typeSyntax := Lean.mkIdent `Nat }]
    objective := .missing
  }

/-- error: problem presentation metadata contains unprintable objective syntax -/
#guard_msgs in
#printp unprintableProblem

end PTranTest.SyntaxEdge
