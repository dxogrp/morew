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
info: minimize x
over (x : Nat)
-/
#guard_msgs in
#printp genuineProblem

/-! Transparent aliases of `Problem` are still genuine problem types. -/

abbrev NatProblem := Problem Nat Nat

def aliasedProblem : NatProblem :=
  problem (x : Nat)
    minimize x + 1

/--
info: minimize x + 1
over (x : Nat)
-/
#guard_msgs in
#printp aliasedProblem

end PTranTest.SyntaxEdge
