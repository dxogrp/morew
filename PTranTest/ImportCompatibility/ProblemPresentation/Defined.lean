import PTran.Syntax.Elab

/-!
# Imported problem declarations

Compile source presentations without the printer. The consumer checks that their
metadata and pre-resolved names survive the compiled-module boundary.
-/

assert_not_exists PTran.elabPrintProblem

namespace PTranTest.ImportCompatibility.ProblemPresentation.Defined

open PTran

namespace Source

abbrev Coordinate := Nat

def value (x : Nat) := x + 1

def within (x y : Nat) : Prop := x ≤ y

end Source

open Source

def minimum : Problem (Nat × Nat) Nat :=
  problem (x y : Coordinate)
    minimize value x + y
    subject to
      lower : within x y
      positive : 0 < y

def maximum : Problem Nat (OrderDual Nat) :=
  problem (n : Nat)
    maximize value n

macro "importedGeneratedProblem" : term =>
  `(problem (z : Nat) minimize z subject to generated : True)

def generated := importedGeneratedProblem

end PTranTest.ImportCompatibility.ProblemPresentation.Defined
