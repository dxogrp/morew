/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic
import Mathlib.Tactic.NormNum

/-!
# Certified affine constraint normalization

Scalar and componentwise vector relations produce equivalent cone rows.
Asymmetric examples check relation orientation, and rejected constraints
retain their labels and operand context in diagnostics.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.elabProblem Morew.elabPrintProblem

namespace MorewTest.Affine.ConstraintNormalization

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Morew

noncomputable section

/-- Test witnesses retain the generated equivalence for kernel checking. -/
structure CertifiedRow {X : Type} [AddCommGroup X] [Module ℝ X]
    (predicate : X → Prop) where
  row : Conic.Constraint X
  equivalent : ∀ x, row.Holds x ↔ predicate x

elab "certified_row% " source:term : term => do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  match ← Morew.Elab.Conic.normalizeRow predicate with
  | .error error => throwError "expected an affine row: {error.reason}"
  | .ok result => mkAppM ``CertifiedRow.mk #[result.constraint, result.pointwiseIff]

def scalarEquality :
    CertifiedRow (fun x : ℝ => 2 * x + 1 = 3 * x - 4) :=
  certified_row% (fun x : ℝ => 2 * x + 1 = 3 * x - 4)

def scalarLE : CertifiedRow (fun x : ℝ => x + 1 ≤ 4) :=
  certified_row% (fun x : ℝ => x + 1 ≤ 4)

def scalarGE : CertifiedRow (fun x : ℝ => x + 1 ≥ 4) :=
  certified_row% (fun x : ℝ => x + 1 ≥ 4)

example : scalarEquality.row.Holds 5 := (scalarEquality.equivalent 5).2 (by norm_num)
example : scalarLE.row.Holds 2 := (scalarLE.equivalent 2).2 (by norm_num)
example : ¬ scalarLE.row.Holds 4 := by
  rw [scalarLE.equivalent]
  norm_num
example : scalarGE.row.Holds 4 := (scalarGE.equivalent 4).2 (by norm_num)
example : ¬ scalarGE.row.Holds 2 := by
  rw [scalarGE.equivalent]
  norm_num

def productRow : CertifiedRow (fun x : ℝ × ℝ => x.1 + 2 ≤ x.2 - 3) :=
  certified_row% (fun x : ℝ × ℝ => x.1 + 2 ≤ x.2 - 3)

example : productRow.row.Holds (0, 5) := (productRow.equivalent _).2 (by norm_num)

def productPatternRow :
    CertifiedRow (show (ℝ × ℝ) → Prop from fun (x, y) => x + 2 ≤ y - 3) :=
  certified_row% (show (ℝ × ℝ) → Prop from fun (x, y) => x + 2 ≤ y - 3)

example : productPatternRow.row.Holds (0, 5) :=
  (productPatternRow.equivalent _).2 (by norm_num)

def vectorEquality (n : Nat) : CertifiedRow (fun x : Fin n → ℝ => x = 0) :=
  certified_row% (fun x : Fin n → ℝ => x = 0)

def vectorLE (n : Nat) :
    CertifiedRow (fun x : Fin n → ℝ => x ≤ fun _ => (3 : ℝ)) :=
  certified_row% (fun x : Fin n → ℝ => x ≤ fun _ => (3 : ℝ))

def vectorGE (n : Nat) :
    CertifiedRow (fun x : Fin n → ℝ => x ≥ fun _ => (3 : ℝ)) :=
  certified_row% (fun x : Fin n → ℝ => x ≥ fun _ => (3 : ℝ))

example (n : Nat) (x : Fin n → ℝ) :
    (vectorLE n).row.Holds x ↔ ∀ i, x i ≤ 3 := (vectorLE n).equivalent x

example (n : Nat) (x : Fin n → ℝ) :
    (vectorGE n).row.Holds x ↔ ∀ i, 3 ≤ x i := (vectorGE n).equivalent x

example (x : Fin 0 → ℝ) : (vectorEquality 0).row.Holds x :=
  ((vectorEquality 0).equivalent x).2 (Subsingleton.elim x 0)

example (x : Fin 0 → ℝ) : (vectorLE 0).row.Holds x :=
  ((vectorLE 0).equivalent x).2 (fun i => Fin.elim0 i)

/-! The semantic constructors also work without row recognition. -/

example {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →ᵃ[ℝ] ℝ) (x : X) :
    (Conic.Constraint.eqZero f).Holds x ↔ f x = 0 := by simp

example {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : Nat) (f : X →ᵃ[ℝ] (Fin n → ℝ)) (x : X) :
    (Conic.Constraint.nonnegative f).Holds x ↔ ∀ i, 0 ≤ f x i := by
  simp [Pi.le_def]

private def expectRejected (source : TSyntax `term) (fragment : String) :
    TermElabM Unit := do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  let entry : Morew.Elab.Reformulation.ConstraintEntry := {
    name := `bad_row
    predicate
  }
  let .error error ← Morew.Elab.Conic.normalizeConstraint entry
    | throwError "unsupported constraint was accepted"
  let diagnostic ← error.reason.toString
  unless diagnostic.contains "bad_row" && diagnostic.contains fragment do
    throwError "missing diagnostic context: {diagnostic}"

run_cmd Lean.Elab.Command.liftTermElabM do
  expectRejected (← `(fun x : ℝ => x < 1)) "non-strict"
  expectRejected (← `(fun x : ℝ => x < 1)) "point"
  expectRejected (← `(fun x : ℝ => x ≠ 1)) "equality"
  expectRejected (← `(fun x : ℝ => x * x ≤ 1)) "left-hand side"
  expectRejected (← `(fun x : ℝ => 1 ≤ x * x)) "right-hand side"
  expectRejected (← `(fun x : ℝ => 0 ≤ x ∧ x ≤ 1)) "equality"
  expectRejected (← `(fun x : ℝ => @LE.le ℝ ⟨fun a b => a + 1 ≤ b⟩ x 1))
    "unsupported order"
  expectRejected (← `(fun x : ℝ => @LE.le ℝ ⟨fun a _ => a ≤ a⟩ x x))
    "unsupported order"


end

end MorewTest.Affine.ConstraintNormalization
