/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Type aliases in final cone membership

Definitionally constant vector codomains and singleton collection aliases work
through final conversion, continuation, checked forms, and presentation replay.
-/

namespace MorewTest.Reformulation.ConeMembershipAliases

open Morew
noncomputable section

abbrev Coordinate {n : Nat} (_ : Fin n) := ℝ
abbrev Reals := Set ℝ
abbrev Vectors (n : Nat) := Set ((i : Fin n) → Coordinate i)

def vectors (n : Nat) :=
  problem (v w : (_i : Fin n) → Coordinate _i)
    minimize (0 : ℝ)
    subject to
      lower : v ≤ w
      upper : v ≥ w
      equal : v = w

section
variable (n : Nat)

reformulation vectorTarget : (vectors n) := by
  conic

example : GlobalEquivalence (vectors n) (vectorTarget n) := vectorTarget.equivalence n
example : (vectorTarget.conicForm n).data.toProblem = vectorTarget n :=
  (vectorTarget.conicForm n).represents
example : (vectorTarget.conicForm n).data.rowCount = 3 := rfl
example (v w : (i : Fin n) → Coordinate i) : (vectorTarget n).feasible (v, w) ↔
    w - v ∈ ℝ₊^n ∧ v - w ∈ ℝ₊^n ∧ v - w ∈ ({0} : Vectors n) := Iff.rfl

end

reformulation vectorAgain : (vectorTarget 2) := by
  conic

example : GlobalEquivalence (vectorTarget 2) vectorAgain := vectorAgain.equivalence
example : vectorAgain.conicForm.data.toProblem = vectorAgain := vectorAgain.conicForm.represents

reformulation emptyVector : (vectorTarget 0) := by
  conic

example : emptyVector.conicForm.data.rowCount = 3 := rfl
example : emptyVector.conicForm.data.toProblem = emptyVector := emptyVector.conicForm.represents

def singletons :=
  problem (x : ℝ) (v : (_i : Fin 2) → Coordinate _i)
    minimize x
    subject to
      scalar : x ∈ ({0} : Reals)
      vector : v ∈ ({0} : Vectors 2)

reformulation singletonTarget : singletons := by
  conic

example : GlobalEquivalence singletons singletonTarget := singletonTarget.equivalence
example : singletonTarget.conicForm.data.toProblem = singletonTarget :=
  singletonTarget.conicForm.represents

reformulation singletonAgain : singletonTarget := by
  conic

example : GlobalEquivalence singletonTarget singletonAgain := singletonAgain.equivalence
example : singletonAgain.conicForm.data.rowCount = 2 := rfl
example : singletonAgain.conicForm.data.toProblem = singletonAgain :=
  singletonAgain.conicForm.represents

run_cmd do
  for (source, copied) in #[(``vectorAgain, `replayedVector),
      (``emptyVector, `replayedEmptyVector), (``singletonAgain, `replayedSingleton)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) source
      | Lean.throwError "missing aliased membership presentation for replay"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copied
    Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (v w : (i : Fin 2) → Coordinate i) :
    replayedVector.feasible (v, w) ↔ vectorAgain.feasible (v, w) := Iff.rfl
example (v w : (i : Fin 0) → Coordinate i) :
    replayedEmptyVector.feasible (v, w) ↔ emptyVector.feasible (v, w) := Iff.rfl
example (x : ℝ) (v : (i : Fin 2) → Coordinate i) :
    replayedSingleton.feasible (x, v) ↔ singletonAgain.feasible (x, v) := Iff.rfl

end
end MorewTest.Reformulation.ConeMembershipAliases
