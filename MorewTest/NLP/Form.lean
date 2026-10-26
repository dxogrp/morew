/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Form
import MorewTest.NLP.DomainSupport

/-!
# Persistent complete smooth-NLP forms

These compiled examples check concrete row data, exact representation, shared
domains, symbolic families, and the contract for cached certificates. They use
the internal metaprogramming API without adding modeling syntax.
-/

namespace MorewTest.NLP.Form

open Lean Lean.Meta Lean.Elab.Term
open Morew
open Morew.Elab.NLP

noncomputable section

private def presentationFor (source : Expr) (sense : ObjectiveSense := .minimize)
    (empty : Bool := false) : MetaM Elab.Reformulation.PresentationState := do
  let type ← whnf (← inferType source)
  unless type.isAppOfArity ``Problem 2 do throwError "expected a problem"
  let domain := type.getAppArgs[0]!
  let feasible ← mkAppM ``Problem.feasible #[source]
  return {
    sense, domainType := domain, valueType := type.getAppArgs[1]!
    binders := #[{ name := `x, type := domain }]
    objective := ← mkAppM ``Problem.objective #[source]
    constraints := if empty then #[] else
      #[{ name := `bounds, predicate := feasible }]
  }

private def requireForm (presentation : Elab.Reformulation.PresentationState)
    (cached : Array (Option Rows.Result) := #[]) : MetaM Expr := do
  match ← buildForm presentation cached with
  | .error error => throwError "expected smooth-NLP form: {error.reason}"
  | .ok form =>
    if form.hasMVar || form.hasSorry then throwError "incomplete NLP form"
    checkWithKernel form
    return form

elab "nlp_form_for% " source:term : term => do
  requireForm (← presentationFor (← Domain.elaborate source))

elab "max_nlp_form_for% " source:term : term => do
  requireForm (← presentationFor (← Domain.elaborate source) .maximize)

def polynomial : Problem ℝ ℝ where
  objective x := -x ^ 4 + x ^ 2
  feasible x := (True ∧ x ^ 2 ≤ 4) ∧ (x ≥ -1 ∧ x ^ 3 = 0)

def polynomialForm : NLP.Form polynomial := nlp_form_for% polynomial
def inferredPolynomialForm := nlp_form_for% polynomial

example : polynomialForm.data.rowCount = 3 := rfl
example : polynomialForm.data.sense = .minimize := rfl
example : polynomialForm.data.toProblem = polynomial := polynomialForm.represents
example : IsSmoothNLP polynomial := polynomialForm.isSmoothNLP
example (x : ℝ) : polynomialForm.data.objective x = -x ^ 4 + x ^ 2 := rfl
example : (polynomialForm.data.rows (0 : Fin 3)).bounds = NLP.Bounds.upperBound 0 := rfl
example : (polynomialForm.data.rows (1 : Fin 3)).bounds = NLP.Bounds.lowerBound 0 := rfl
example : (polynomialForm.data.rows (2 : Fin 3)).bounds = NLP.Bounds.fixed 0 := rfl
example (x : ℝ) : (polynomialForm.data.rows (0 : Fin 3)).residual x = x ^ 2 - 4 := rfl
example (x : ℝ) : (polynomialForm.data.rows (1 : Fin 3)).residual x = x - -1 := rfl
example (x : ℝ) : (polynomialForm.data.rows (2 : Fin 3)).residual x = x ^ 3 - 0 := rfl
example (x : ℝ) :
    (∀ i, (polynomialForm.data.rows i).Holds x) ↔ polynomial.feasible x := by
  change polynomialForm.data.toProblem.feasible x ↔ polynomial.feasible x
  rw [polynomialForm.represents]
example : inferredPolynomialForm.data.rowCount = 3 := rfl

def maximizing : Problem (ℝ × ℝ) (OrderDual ℝ) where
  objective x := x.1 * x.2
  feasible x := x.1 ^ 2 + x.2 ^ 2 ≤ 1

def maximizingForm := max_nlp_form_for% maximizing
example : maximizingForm.data.sense = .maximize := rfl
example : maximizingForm.data.toProblem = maximizing := maximizingForm.represents
example (x : ℝ × ℝ) : maximizingForm.data.objective x = x.1 * x.2 := rfl

def logProblem : Problem ℝ ℝ where
  objective := Real.log
  feasible x := 1 ≤ x ∧ Real.log x ≤ 2

def logForm := nlp_form_for% logProblem
example : logForm.data.rowCount = 2 := rfl
example (x : ℝ) : logForm.data.objective x = Real.log x := rfl
example (x : ℝ) (h : logProblem.feasible x) : x ∈ logForm.data.domain := by
  apply logForm.data.feasible_mem_domain x
  change logForm.data.toProblem.feasible x
  rwa [logForm.represents]

def vectorForm (n : Nat) := nlp_form_for%
  (show Problem (Fin n → ℝ) ℝ from
    ⟨fun x => ∑ i, x i ^ 4, fun x => x ≤ fun _ => 1⟩)

example (n : Nat) : (vectorForm n).data.rowCount = n := by
  change (∑ _ : Fin n, (1 : ℕ)) = n
  simp
example : (vectorForm 0).data.rowCount = 0 := by
  change (∑ _ : Fin 0, (1 : ℕ)) = 0
  simp

def nestedFamilyForm (n m : Nat) := nlp_form_for%
  (show Problem (Fin n → Fin m → ℝ) ℝ from
    ⟨fun x => ∑ i, ∑ j, x i j ^ 2,
      fun x => ∀ i, ∀ j, (0 ≤ x i j ∧ x i j ≤ 1)⟩)

example (n m : Nat) : (nestedFamilyForm n m).data.rowCount = n * (m * 2) := by
  change (∑ _ : Fin n, ∑ _ : Fin m, (1 + 1 : ℕ)) = n * (m * 2)
  simp

-- Flattening preserves increasing outer/inner coordinates, then left-to-right
-- conjunction order. Exact feasible-set equality alone cannot detect a row swap.
example (x : Fin 2 → Fin 2 → ℝ) :
    ((nestedFamilyForm 2 2).data.rows (0 : Fin 8)).residual x = 0 - x 0 0 := rfl
example (x : Fin 2 → Fin 2 → ℝ) :
    ((nestedFamilyForm 2 2).data.rows (1 : Fin 8)).residual x = x 0 0 - 1 := rfl
example (x : Fin 2 → Fin 2 → ℝ) :
    ((nestedFamilyForm 2 2).data.rows (2 : Fin 8)).residual x = 0 - x 0 1 := rfl
example (x : Fin 2 → Fin 2 → ℝ) :
    ((nestedFamilyForm 2 2).data.rows (7 : Fin 8)).residual x = x 1 1 - 1 := rfl
example : ((nestedFamilyForm 2 2).data.rows (7 : Fin 8)).bounds =
    NLP.Bounds.upperBound 0 := rfl

def matrixForm := nlp_form_for%
  (show Problem (Matrix (Fin 2) (Fin 3) ℝ) ℝ from
    ⟨fun x => x 0 1, fun x => x 0 1 ≤ 1⟩)
example : matrixForm.data.rowCount = 1 := rfl

def emptyForm := nlp_form_for%
  (show Problem ℝ ℝ from ⟨fun x => x ^ 2, fun _ => True ∧ True⟩)
example : emptyForm.data.rowCount = 0 := rfl

-- Failures report a specific unsupported row even for a smooth objective; no
-- restricted operation is rescued by a tautology or cancellation.
private def requireFailure (term : TSyntax `term) (kind : Smooth.SmoothFailureKind) :
    TermElabM Unit := do
  let presentation ← presentationFor (← Domain.elaborate term)
  let .error error ← buildForm presentation | throwError "unsupported problem was certified"
  unless error.kind == kind do throwError "wrong form failure: {error.reason}"

run_elab requireFailure (← `(show Problem ℝ ℝ from
  ⟨fun x => x ^ 2, fun x => 0 < x⟩)) .unsupportedRow
run_elab requireFailure (← `(show Problem ℝ ℝ from
  ⟨Real.log, fun x => 0 ≤ x⟩)) .feasibleInclusion
run_elab requireFailure (← `(show Problem ℝ ℝ from
  ⟨fun _ => Real.log (-1), fun _ => True⟩)) .feasibleInclusion
run_elab requireFailure (← `(show Problem ℝ ℝ from
  ⟨fun x => |x|, fun _ => True⟩)) .nonsmooth

-- Cache validation rejects a certificate for a different predicate, even if
-- both rows happen to be smooth. The successful control reuses exact row data.
run_elab do
  let source ← Domain.elaborate (← `(polynomial))
  let presentation ← presentationFor source
  let canonical ← presentation.canonicalProblem
  let feasible ← mkAppM ``Problem.feasible #[canonical]
  let .ok cached ← Rows.certifyRows feasible #[presentation.constraints[0]!.predicate]
    | throwError "failed cache setup"
  discard <| requireForm presentation #[some cached]
  let other ← Domain.elaborate (← `(fun x : ℝ => x ≤ 5))
  let wrong := { presentation with constraints := #[{ name := `bounds, predicate := other }] }
  let .error _ ← buildForm wrong #[some cached]
    | throwError "accepted cache for a different problem"

-- Cached rows and their inferred domain survive an added auxiliary coordinate.
run_elab do
  let feasible ← Domain.elaborate (← `(fun x : ℝ => 1 ≤ x))
  let row ← Domain.elaborate (← `(fun x : ℝ => Real.log x ≤ 4))
  let .ok cached ← Rows.certifyRows feasible #[row] | throwError "failed cache setup"
  let next ← Domain.elaborate (← `(fun z : ℝ × ℝ => 1 ≤ z.1 ∧ z.2 = 0))
  let backward ← Domain.elaborate (← `(fun (z : ℝ × ℝ) (h : 1 ≤ z.1 ∧ z.2 = 0) => h.1))
  let transported ← cached.transport next backward (some (mkConst ``Real))
  for block in transported.rowBlocks do checkWithKernel block

end

end MorewTest.NLP.Form
