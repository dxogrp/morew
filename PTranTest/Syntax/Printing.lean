import PTran.Syntax

/-!
# Problem presentation printing

The narrow `PTran.Syntax` import provides both objective senses and the printer.
Check source rendering, transparent problem types, identifier hygiene, and binder grouping.
-/

namespace PTranTest.Syntax.Printing

open PTran

def genuineProblem :=
  problem (x : Nat)
    minimize x

/--
info: problem (x : Nat)
  minimize x
-/
#guard_msgs in
#printp genuineProblem

def boundedMaximum : Problem Nat (OrderDual Nat) :=
  problem (n : Nat)
    maximize n
    subject to
      upper : n ≤ 3

example (n : Nat) : boundedMaximum.objective n = n := rfl
example (n : Nat) : boundedMaximum.feasible n ↔ n ≤ 3 := Iff.rfl

/--
info: problem (n : Nat)
  maximize n
  subject to
    upper : n ≤ 3
-/
#guard_msgs in
#printp boundedMaximum

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

/-! Identifier escaping and hygiene are normalized in printer output. -/

def quotedIdentifierProblem :=
  problem («minimize» : Nat)
    minimize «minimize»
    subject to
      «subject» : True

/--
info: problem («minimize» : Nat)
  minimize «minimize»
  subject to
    «subject» : True
-/
#guard_msgs in
#printp quotedIdentifierProblem

macro "generatedProblemTerm" : term =>
  `(problem (x : Nat) minimize x subject to c : True)

def macroGeneratedProblem := generatedProblemTerm

/--
info: problem (x : Nat)
  minimize x
  subject to
    c : True
-/
#guard_msgs in
#printp macroGeneratedProblem

/-! Adjacent binders with equal rendered types remain grouped. -/

def adjacentEqualTypeBinders :=
  problem (x : Nat) (y : Nat)
    minimize x + y

/--
info: problem (x y : Nat)
  minimize x + y
-/
#guard_msgs in
#printp adjacentEqualTypeBinders

end PTranTest.Syntax.Printing
