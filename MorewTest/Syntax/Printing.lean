import Morew.Syntax
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Problem presentation printing

The narrow `Morew.Syntax` import provides both objective senses and the printer.
Check source rendering, transparent problem types, identifier hygiene, and binder grouping.
-/

namespace MorewTest.Syntax.Printing

open Morew

def genuineProblem :=
  problem (x : Nat)
    minimize x

/--
info: problem (x : Nat)
  minimize x
-/
#guard_msgs in
#printp genuineProblem

def parameterizedProblem (a : Nat) :=
  problem (x : Nat)
    minimize x + a

/--
info: problem (x : Nat)
  minimize x + a
-/
#guard_msgs in
#printp parameterizedProblem

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

/-! Family parameters remain source references after their section closes. -/

section

variable {α : Type} [Preorder α] (n : Nat) (score : (Fin n → α) → α) (bound : α)

def parameterizedMaximum : Problem (Fin n → α) (OrderDual α) :=
  problem (x : Fin n → α)
    maximize score x
    subject to
      upper : ∀ i, x i ≤ bound

end

/--
info: problem (x : Fin n → α)
  maximize score x
  subject to
    upper : ∀ i, x i ≤ bound
-/
#guard_msgs in
#printp parameterizedMaximum

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

abbrev NatProblemFamily := Nat → NatProblem

def aliasedParameterizedProblem (a : Nat) : NatProblemFamily :=
  fun b =>
    problem (x : Nat)
      minimize x + a + b

/--
info: problem (x : Nat)
  minimize x + a + b
-/
#guard_msgs in
#printp aliasedParameterizedProblem

/-! Matrix dimensions and data stay visible in a least-squares presentation. -/

open scoped BigOperators

noncomputable def leastSquares {m n : Nat}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Problem (Fin n → ℝ) ℝ :=
  problem (x : Fin n → ℝ)
    minimize ∑ i, ((∑ j, A i j * x j) - b i) ^ 2
    subject to
      upper : ∀ i, (∑ j, A i j * x j) ≤ b i

/--
info: problem (x : Fin n → ℝ)
  minimize ∑ i, ((∑ j, A i j * x j) - b i) ^ 2
  subject to
    upper : ∀ i, (∑ j, A i j * x j) ≤ b i
-/
#guard_msgs in
#printp leastSquares

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

end MorewTest.Syntax.Printing
