/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Rows
import MorewTest.NLP.DomainSupport

/-! # Generated rows, projected domain evidence, and grouped finite families -/

namespace MorewTest.NLP.Rows

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.NLP

private def check (feasible : Expr) (rows : Array Expr)
    (failure? : Option Smooth.SmoothFailureKind := none) : MetaM Unit := do
  match ← Rows.certifyRows feasible rows with
  | .error error =>
    if failure? != some error.kind then
      throwError "unexpected generated-row failure ({repr error.kind}): {error.reason}"
  | .ok result =>
    if failure?.isSome then throwError "unsupported generated rows were certified"
    unless result.rowCertificates.size == rows.size do throwError "wrong generated-row count"
    for i in [:rows.size] do
      let expected ← mkAppM ``Morew.NLP.Rows.Certified #[result.domain, rows[i]!]
      unless ← isDefEq (← inferType result.rowCertificates[i]!) expected do
        throwError "generated row or common domain changed"
    for proof in result.rowCertificates ++ #[result.domainIsOpen, result.feasibleMemDomain] do
      if proof.hasMVar || proof.hasSorry then throwError "incomplete generated-row evidence"
      checkWithKernel proof

private def assertRows (term : TSyntax `term) (parameters : Nat := 0)
    (failure? : Option Smooth.SmoothFailureKind := none) : TermElabM Unit :=
  Domain.withInput term parameters fun feasible rows => check feasible rows failure?

-- Generated equalities and margins supply domain evidence only after exactness
-- has been independently checked by the caller of this internal adapter.
run_elab assertRows (← `(((fun u : ℝ => u = 1 ∧ Real.log u = 0),
  #[fun u : ℝ => u = 1, fun u : ℝ => Real.log u = 0])))

run_elab assertRows (← `(((fun u : ℝ => u = 0 ∧ Real.log u = 0),
  #[fun u : ℝ => u = 0, fun u : ℝ => Real.log u = 0]))) 0 (some .feasibleInclusion)

run_elab assertRows (← `(((fun u : ℝ => Real.log u = 0),
  #[fun u : ℝ => Real.log u = 0]))) 0 (some .feasibleInclusion)

-- An untouched strict or opaque predicate supplies no evidence and does not
-- prevent certification of generated polynomials or guarded logarithms.
def hiddenPositive (x : ℝ) : Prop := 0 < x

run_elab assertRows (← `(((fun x : ℝ => x < 10 ∧ hiddenPositive x ∧ x = 1),
  #[fun x : ℝ => x ^ 2 ≤ 4, fun x : ℝ => Real.log x ≤ 0])))

run_elab assertRows (← `(((fun x : ℝ => hiddenPositive x),
  #[fun x : ℝ => Real.log x ≤ 0]))) 0 (some .feasibleInclusion)

run_elab assertRows (← `(((fun x : ℝ => 0 < x),
  #[fun x : ℝ => Real.log x ≤ 0]))) 0 (some .feasibleInclusion)

run_elab assertRows (← `(((fun x : ℝ => True),
  #[fun x : ℝ => x < 1]))) 0 (some .unsupportedRow)

run_elab assertRows (← `(((fun x : ℝ => True),
  #[fun x : ℝ => hiddenPositive x]))) 0 (some .unsupportedRow)

-- Every grouped row is checked, including nested conjunctions and empty families.
run_elab assertRows (← `(((fun x : ℝ => True),
  #[fun x : ℝ => True ∧ (x ^ 2 ≥ 0 ∧ Real.exp x = 1)])))

run_elab assertRows (← `(fun n : ℕ =>
  ((fun x : Fin n → ℝ => ∀ i, 1 ≤ x i),
    #[fun x : Fin n → ℝ => ∀ i, Real.log (x i) ≤ 0]))) 1

run_elab assertRows (← `(fun n : ℕ =>
  ((fun x : Fin n → ℝ => (fun _ => (1 : ℝ)) ≤ x),
    #[fun x : Fin n → ℝ => (fun i => Real.log (x i)) ≤ (fun _ => 0)]))) 1

run_elab assertRows (← `(fun n : ℕ =>
  ((fun x : Fin n → ℝ => x = (fun _ => 1)),
    #[fun x : Fin n → ℝ => (fun i => Real.log (x i)) = (fun _ => 0)]))) 1

run_elab assertRows (← `(fun n : ℕ =>
  ((fun _ : (i : Fin n) → (fun _ => ℝ) i => True),
    #[fun x : (i : Fin n) → (fun _ => ℝ) i => x ≤ (fun _ => 1)]))) 1

run_elab assertRows (← `(fun n : ℕ =>
  ((fun _ : EuclideanSpace ℝ (Fin n) => True),
    #[fun x : EuclideanSpace ℝ (Fin n) => WithLp.ofLp x ≤ (fun _ => 1)]))) 1

run_elab assertRows (← `(((fun x : Fin 2 → ℝ => ∀ i, 1 ≤ x i),
  #[fun x : Fin 2 → ℝ => Real.log (x 0) + Real.log (x 1) ≤ 0])))

run_elab assertRows (← `(fun n : ℕ =>
  ((fun x : Fin n → ℝ => ∀ i, 1 ≤ x i),
    #[fun x : Fin n → ℝ => (∑ i, Real.log (x i)) ≤ 0]))) 1

run_elab assertRows (← `(fun (n : ℕ) (s : Finset (Fin n)) =>
  ((fun x : Fin n → ℝ => ∀ i ∈ s, 1 ≤ x i),
    #[fun x : Fin n → ℝ => (∑ i ∈ s, Real.log (x i)) ≤ 0]))) 2

run_elab assertRows (← `(fun (s : Finset ℕ) (a : ℕ → ℝ) =>
  ((fun x : ℝ => ∀ i ∈ s, 1 ≤ a i * x),
    #[fun x : ℝ => (∑ i ∈ s, Real.log (a i * x)) ≤ 0]))) 2

run_elab assertRows (← `(fun s : Finset (Fin 2) =>
  ((fun x : Fin 2 → ℝ => ∀ i ∈ s, 1 ≤ x i),
    #[fun x : Fin 2 → ℝ => Real.log (x 0) ≤ 0]))) 1 (some .feasibleInclusion)

-- A custom membership relation cannot masquerade as native finite support.
run_elab assertRows (← `(fun s : Finset (Fin 2) =>
  ((fun x : Fin 2 → ℝ => ∀ i, @Membership.mem (Fin 2) (Finset (Fin 2))
      ⟨fun _ _ => True⟩ s i → 1 ≤ x i),
    #[fun x : Fin 2 → ℝ => (∑ i ∈ s, Real.log (x i)) ≤ 0]))) 1 (some .feasibleInclusion)

run_elab assertRows (← `(((fun _ : Fin 0 → ℝ => True),
  #[fun x : Fin 0 → ℝ => ∀ i, Real.log (x i) ≤ 0])))

run_elab assertRows (← `(((fun _ : Fin 0 → ℝ => True),
  #[fun x : Fin 0 → ℝ => ∀ i, x i < 0]))) 0 (some .unsupportedRow)

-- Finset extrema reindex coordinates without losing independent membership evidence.
run_elab assertRows (← `(fun (s : Finset ℕ) (a : ℕ → ℝ)
    (_ha : ∀ i ∈ s, 0 < a i) =>
  ((fun _ : ℝ => True),
    #[fun x : ℝ => ∀ j : Fin s.card, Real.log (a (s.equivFin.symm j)) + x ≤ 0]))) 3

-- Checked independent proof lets belong to the row's local scope. They may
-- depend on its finite index, but must not escape as free variables in evidence.
def coefficient (c : ℝ) : ℝ := c ^ 2 + 1

theorem coefficient_pos (c : ℝ) : 0 < coefficient c := by
  unfold coefficient
  positivity

run_elab assertRows (← `(fun c : ℝ =>
  ((fun _ : ℝ => True),
    #[fun x : ℝ =>
      let _h : 0 < coefficient c := coefficient_pos c
      Real.log (coefficient c) * x ≤ 0]))) 1

run_elab assertRows (← `(fun (n : ℕ) (a : Fin n → ℝ) =>
  ((fun _ : ℝ => True),
    #[fun x : ℝ => ∀ i : Fin n,
      let _h : 0 < coefficient (a i) := coefficient_pos (a i)
      Real.log (coefficient (a i)) * x ≤ 0]))) 2

run_elab assertRows (← `(fun c : ℝ =>
  ((fun _ : ℝ => True),
    #[fun x : ℝ =>
      (let _h : 0 < coefficient c := coefficient_pos c
       (Real.log (coefficient c) * x ≤ 0, True)).1]))) 1

-- A decision-dependent binding stays inside the residual traversal.
run_elab assertRows (← `(((fun _ : ℝ => True),
  #[fun x : ℝ =>
    let _h : 0 < Real.exp x := Real.exp_pos x
    Real.log (Real.exp x) ≤ 0])))

run_elab assertRows (← `(fun c : ℝ =>
  ((fun _ : ℝ => True),
    #[fun x : ℝ =>
      let _h : 0 < coefficient c := (fun _ : ℝ => coefficient_pos c) x
      Real.log (coefficient c) * x ≤ 0]))) 1 (some .feasibleInclusion)

run_elab assertRows (← `(fun c : ℝ =>
  ((fun _ : ℝ => True),
    #[fun _ : ℝ =>
        let _h : 0 < coefficient c := coefficient_pos c
        True,
      fun x : ℝ => Real.log (coefficient c) * x ≤ 0]))) 1 (some .feasibleInclusion)

-- An unselected predicate and every original residual remain outside the target
-- grammar; an empty supplied row list still checks the decision space.
run_elab assertRows (← `(((fun x : ℝ => x < 0 ∨ 1 < x), (#[] : Array (ℝ → Prop)))))

end MorewTest.NLP.Rows
