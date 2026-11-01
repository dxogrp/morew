/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Substitution.Evidence
import Morew.Substitution
import MorewTest.Affine.Support
import MorewTest.Environment

/-! # Bounded range evidence and independent declaration premises -/

namespace MorewTest.Substitution.Evidence

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command Qq
open MorewTest.Affine
open Morew.Elab.Substitution.Evidence

private def verify (point goal : Expr) (action : MetaM (Option Expr)) (success : Bool) :
    MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let result ← action
  unless result.isSome == success do throwError "unexpected coverage result for {goal}"
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "coverage evidence changed caller metavariables"
  if let some proof := result then
    checkWithKernel proof
    unless ← isDefEq (← inferType proof) goal do throwError "wrong coverage evidence type"
    unless !(← Morew.Elab.Expr.hasUnresolved proof) &&
        !(← Morew.Elab.Conic.Evidence.hasPlaceholders proof) do
      throwError "coverage evidence contains placeholders"
    discard <| Morew.Elab.Expr.depends point proof
  else if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
    throwError "failed coverage evidence leaked declaration {name}"

private def check (term : TSyntax `term) (parameters : Nat) (success : Bool)
    (independent := false) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ source => do
    lambdaTelescope source fun points body => do
      unless points.size == 1 do throwError "expected one source point"
      let feasible ← Morew.Elab.Expr.reduceStructure (.proj ``Prod 0 body)
      let goal := Expr.proj ``Prod 1 body
      withLocalDeclD `sourceFeasible feasible fun proof => do
        verify points[0]! goal
          (if independent then proveIndependent? points[0]! goal
           else proveRange? points[0]! goal proof) success

private def NonnegativeAlias (x : ℝ) := 0 ≤ x
private def ConjunctionAlias (x : ℝ) := True ∧ (0 < x ∧ True)
private def NonnegativeConjunctionAlias (x : ℝ) := True ∧ (0 ≤ x ∧ True)

run_cmd liftTermElabM do
  check (← `(fun (x : ℝ) => (0 ≤ x, 0 ≤ x))) 0 true
  check (← `(fun (x : ℝ) => (True ∧ (0 < x ∧ x ≤ 2), 0 ≤ x ∧ x ≠ 0))) 0 true
  check (← `(fun (x : ℝ) => (ConjunctionAlias x, 0 ≤ x))) 0 true
  check (← `(fun (x : ℝ) => (NonnegativeAlias x, 0 ≤ x))) 0 true
  check (← `(fun (x : ℝ) => (0 ≤ x, NonnegativeAlias x))) 0 true
  check (← `(fun (x : ℝ) => ((let y := x; 0 < y), 0 ≤ x))) 0 true
  check (← `(fun (x : ℝ) => (1 ≤ x, 0 < x))) 0 true
  check (← `(fun (x : ℝ) => (x ≥ 1, x > 0))) 0 true
  check (← `(fun (x : ℝ) => (0 ≤ x, True))) 0 true
  check (← `(fun (x : ℝ) => (x < 0, x ≠ 0))) 0 true
  check (← `(fun (x : ℝ) => (0 < x, (0 : ℝ) ≠ x))) 0 true
  check (← `(fun (x : ℝ) => ((0 : ℝ) ≠ x, x ≠ 0))) 0 true
  check (← `(fun (x : ℝ) => (x ≠ 0, (0 : ℝ) ≠ x))) 0 true
  check (← `(fun (x : ℝ × ℝ) => (0 < x.2, x.2 ≠ 0))) 0 true
  check (← `(fun (epsilon : ℝ) (_h : 0 < epsilon) (x : ℝ) =>
    (epsilon ≤ x, 0 < x))) 2 true
  check (← `(fun (epsilon : ℝ) (_h : 0 ≤ epsilon) (x : ℝ) =>
    (epsilon ≤ x, 0 ≤ x))) 2 true
  check (← `(fun (epsilon : ℝ) (_h : 0 < epsilon) (x : ℝ) =>
    (epsilon ≤ x, 0 ≤ x))) 2 true
  check (← `(fun (epsilon : ℝ) (_h : ConjunctionAlias epsilon) (x : ℝ) =>
    (epsilon ≤ x, 0 < x))) 2 true
  check (← `(fun (epsilon : ℝ) (_h : ConjunctionAlias epsilon) (x : ℝ) =>
    (epsilon ≤ x, 0 ≤ x))) 2 true
  check (← `(fun (epsilon : ℝ) (_h : NonnegativeConjunctionAlias epsilon) (x : ℝ) =>
    (epsilon ≤ x, 0 ≤ x))) 2 true
  check (← `(fun (epsilon : ℝ) (x : ℝ) =>
    (ConjunctionAlias epsilon ∧ epsilon ≤ x, 0 < x))) 1 false
  check (← `(fun (epsilon : ℝ) (x : ℝ) => (epsilon ≤ x, 0 < x))) 1 false
  check (← `(fun (x : ℝ) => (0 ≤ x, 0 < x))) 0 false
  check (← `(fun (x : ℝ) => (0 ≤ x, x ≠ 0))) 0 false
  check (← `(fun (x : ℝ) => (x ≤ 2, 0 ≤ x))) 0 false
  check (← `(fun (x : ℝ × ℝ) => (0 < x.1 ∧ x.1 ≤ x.2, 0 < x.2))) 0 false
  check (← `(fun (x : ℝ) => (0 ≤ x, 1 ≤ x))) 0 false
  check (← `(fun (x : ℝ) => (False, 0 ≤ x))) 0 false

run_cmd liftTermElabM do
  check (← `(fun (_ : ℝ) => (True, True))) 0 true true
  check (← `(fun (_ : ℝ) => (True, (2 : ℝ) ≠ 0))) 0 true true
  check (← `(fun (_ : ℝ) => (True, (-2 / 3 : ℝ) ≠ 0))) 0 true true
  check (← `(fun (_ : ℝ) => (True, (0 : ℝ) ≠ 0))) 0 false true
  check (← `(fun (a : ℝ) (_h : 0 < a) (_ : ℝ) =>
    (True, 0 ≤ a ∧ a ≠ 0))) 2 true true
  check (← `(fun (a : ℝ) (_h : a < 0) (_ : ℝ) => (True, a ≠ 0))) 2 true true
  check (← `(fun (a : ℝ) (_h : a ≠ 0) (_ : ℝ) => (True, a ≠ 0))) 2 true true
  check (← `(fun (a : ℝ) (_h : (0 : ℝ) ≠ a) (_ : ℝ) => (True, a ≠ 0))) 2 true true
  check (← `(fun (a : ℝ) (_h : a ≠ 0) (_ : ℝ) => (True, (0 : ℝ) ≠ a))) 2 true true
  check (← `(fun (a : ℝ) (_ : ℝ) => (a ≠ 0, a ≠ 0))) 1 false true
  check (← `(fun (a : ℝ) (_ : ℝ) => (0 < a, a ≠ 0))) 1 false true
  check (← `(fun (x : ℝ) => (0 < x, 0 < x))) 0 false true

run_cmd liftTermElabM do
  check (← `(fun (x : ℝ) =>
    (0 ≤ x, Morew.Substitution.square.range () x))) 0 true
  check (← `(fun (x : ℝ) =>
    (1 ≤ x, Morew.Substitution.exp.range () x))) 0 true
  check (← `(fun (x : ℝ) =>
    (True, (Morew.Substitution.mulLeft (fun _ : Unit => 2)).range () x))) 0 true
  check (← `(fun (x : ℝ) =>
    (True, (Morew.Substitution.mulLeft (fun _ : ℝ => 2)).range x x))) 0 true
  check (← `(fun (x : ℝ) =>
    (True, (Morew.Substitution.mulLeft (fun _ : ℝ => -3)).range x x))) 0 true
  check (← `(fun (x : ℝ) =>
    (True, (Morew.Substitution.affine (fun _ : Unit => -2) (fun _ => 1)).range () x)))
    0 true
  check (← `(fun (x : ℝ × ℝ) =>
    (0 < x.1, (Morew.Substitution.affine (fun a : ℝ => a) (fun _ => 2)).range x.1 x.2)))
    0 true

-- An altered order can be used as an exact typed fact, but not as evidence
-- about the canonical real order or as a premise to the sign implications.
run_cmd liftTermElabM do
  check (← `(fun (x : ℝ) =>
    ((letI : LT ℝ := ⟨fun _ _ => True⟩; 0 < x), 0 ≤ x))) 0 false
  check (← `(fun (x : ℝ) =>
    ((letI : LE ℝ := ⟨fun _ _ => True⟩; 1 ≤ x), 0 < x))) 0 false
  check (← `(fun (x : ℝ) =>
    (0 < x, (letI : LE ℝ := ⟨fun a b => b ≤ a⟩; 0 ≤ x)))) 0 false

-- Hidden placeholders and unresolved caller metavariables cannot become
-- evidence, even when they appear behind a local declaration.
run_cmd liftTermElabM do
  withLocalDeclD `point q(ℝ) fun point => do
    let point : Q(ℝ) := point
    let goal := q(0 ≤ $point)
    withLetDecl `badEvidence goal (← mkSorry goal true) fun proof => do
      verify point goal (proveRange? point goal proof) false
    let hole ← mkFreshExprMVar q(ℝ)
    let hole : Q(ℝ) := hole
    let unresolved := q(0 ≤ $hole)
    withLocalDeclD `sourceFeasible q(True) fun proof => do
      verify point unresolved (proveRange? point unresolved proof) false
      if ← hole.mvarId!.isAssigned then throwError "coverage assigned a caller metavariable"

end MorewTest.Substitution.Evidence
