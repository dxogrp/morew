/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Normalize
import MorewTest.Affine.Support

/-!
# Checked final membership normalization

Exercise actual typed predicates, their exact equivalences, preserved binding
identities and native operations before surface printing is involved.
-/

namespace MorewTest.Conic.Normalize

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew.Elab.Conic MorewTest.Affine

private def assertNormalization (sourceSyntax targetSyntax : TSyntax `term)
    (parameterCount : Nat := 0) (changed : Bool := true) : TermElabM Unit := do
  let source ← elaborate sourceSyntax
  let target ← elaborate targetSyntax
  lambdaBoundedTelescope source parameterCount fun parameters predicate => do
    let result ← normalizePredicate predicate
    unless result.changed == changed do
      throwError "membership normalization reported the wrong change status"
    let expected := target.beta parameters
    unless ← isDefEq result.predicate expected do
      throwError "wrong normalized predicate: {result.predicate}; expected {expected}"
    if result.predicate.hasMVar || result.pointwiseIff.hasMVar || result.pointwiseIff.hasSorry then
      throwError "membership normalization returned incomplete evidence"
    checkWithKernel result.pointwiseIff

-- A syntactically dependent codomain can reduce to the supported real space.
private abbrev Coordinate {n : Nat} (_ : Fin n) := ℝ

run_cmd liftTermElabM do
  assertNormalization
    (← `(fun n : Nat => fun x : (i : Fin n) → Coordinate i => 0 ≤ x ∧ x = 0))
    (← `(fun n : Nat => fun x : (i : Fin n) → Coordinate i =>
      x ∈ ℝ₊^n ∧ x ∈ ({0} : Set ((i : Fin n) → Coordinate i)))) 1

run_cmd liftTermElabM do
  assertNormalization
    (← `(fun p : ℝ × ℝ => 2 * p.1 + 1 ≤ 3 * p.2 + 4))
    (← `(fun p : ℝ × ℝ => (3 * p.2 + 4) - (2 * p.1 + 1) ∈ ℝ₊))
  assertNormalization
    (← `(fun p : ℝ × ℝ => 2 * p.1 + 1 ≥ 3 * p.2 + 4))
    (← `(fun p : ℝ × ℝ => (2 * p.1 + 1) - (3 * p.2 + 4) ∈ ℝ₊))
  assertNormalization
    (← `(fun p : ℝ × ℝ => 2 * p.1 + 1 = 3 * p.2 + 4))
    (← `(fun p : ℝ × ℝ => (2 * p.1 + 1) - (3 * p.2 + 4) ∈ ({0} : Set ℝ)))
  assertNormalization
    (← `(fun x : ℝ => (True ∧ 0 ≤ x) ∧ ((x ≤ 0 ∧ x = 0) ∧ True)))
    (← `(fun x : ℝ => (True ∧ x ∈ ℝ₊) ∧ ((-x ∈ ℝ₊ ∧ x ∈ ({0} : Set ℝ)) ∧ True)))
  assertNormalization
    (← `(fun _ : ℝ => (2 : ℝ) ≤ 3 ∧ (0 : ℝ) = 0))
    (← `(fun _ : ℝ => ((3 : ℝ) - 2) ∈ ℝ₊ ∧ (0 : ℝ) ∈ ({0} : Set ℝ)))
  assertNormalization
    (← `(fun n : Nat => fun x : Fin n → ℝ => 0 ≤ x ∧ x = 0))
    (← `(fun n : Nat => fun x : Fin n → ℝ => x ∈ ℝ₊^n ∧ x ∈ ({0} : Set (Fin n → ℝ)))) 1
  assertNormalization
    (← `(fun x : Fin 0 → ℝ => x ≤ 0))
    (← `(fun x : Fin 0 → ℝ => -x ∈ ℝ₊^0))
  assertNormalization
    (← `(fun _ : ℝ => True ∧ True))
    (← `(fun _ : ℝ => True ∧ True)) 0 false
  assertNormalization
    (← `(fun x : ℝ × (Fin 2 → ℝ) => x ∈ (Morew.Conic.Cone.secondOrder 2).carrier))
    (← `(fun x : ℝ × (Fin 2 → ℝ) => x ∈ (Morew.Conic.Cone.secondOrder 2).carrier)) 0 false

-- Source helpers are operands, and their implementations stay uninspected.
private def helper (x : ℝ) : ℝ := 2 * x + 1
private def zeroHelper (_ : ℝ) : ℝ := 0

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun x : ℝ => zeroHelper x ≤ helper x))
  let result ← normalizePredicate source
  unless result.predicate.find? (·.isConstOf ``helper) |>.isSome do
    throwError "normalization unfolded an affine helper"
  unless result.predicate.find? (·.isConstOf ``zeroHelper) |>.isSome do
    throwError "normalization simplified a helper whose value happens to be zero"
  unless result.predicate.find? (·.isConstOf ``HSub.hSub) |>.isSome do
    throwError "normalization dropped a named zero operand"

-- In a surface model, local definitions are free let variables until the row
-- is rendered. Equal definition bodies must not merge their binding identities.
run_cmd liftTermElabM do
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let zero ← elaborate (← `((0 : ℝ)))
    withLetDecl `first (mkConst ``Real) zero fun first => do
      withLetDecl `second (mkConst ``Real) zero fun second => do
        let lhs ← mkAppM ``LE.le #[first, x]
        let rhs ← mkAppM ``LE.le #[second, x]
        let result ← normalizeBody (mkApp2 (mkConst ``And) lhs rhs)
        unless result.body.containsFVar first.fvarId! &&
            result.body.containsFVar second.fvarId! do
          throwError "normalization erased or conflated local definitions"
        checkWithKernel result.iff

-- Unused lets and named aliases survive predicate normalization itself.
run_cmd liftTermElabM do
  let source ← elaborate (← `(fun x : ℝ =>
    let first := x + 1
    let second := first
    let unused : ℝ := 7
    second ≤ 4))
  let result ← normalizePredicate source
  lambdaTelescope result.predicate fun _ body => do
    unless body.isLet do throwError "normalization erased the local-definition prefix"
    let .letE _ _ _ rest _ := body | unreachable!
    unless rest.isLet do throwError "normalization erased a chained local definition"
    let .letE _ _ _ rest _ := rest | unreachable!
    unless rest.isLet do throwError "normalization erased an unused local definition"

-- Direct API calls reject an altered order even when it agrees with the
-- canonical relation at the particular equal operands in this row.
run_cmd liftTermElabM do
  let source ← elaborate (← `(letI : LE ℝ := ⟨fun a b => b ≤ a⟩
    fun x : ℝ => x ≤ x))
  let accepted ← try
    let _ ← normalizePredicate source
    pure true
  catch _ => pure false
  if accepted then throwError "normalization accepted a nonstandard order instance"

-- The generated difference uses native operations despite unrelated local
-- arithmetic instances; none of those instance arguments may escape into it.
run_cmd liftTermElabM do
  let source ← elaborate (← `(fun [HSub ℝ ℝ ℝ] [Neg ℝ] [Zero ℝ] =>
    fun x : ℝ × ℝ => x.1 ≤ x.2))
  lambdaBoundedTelescope source 3 fun parameters predicate => do
    let result ← normalizePredicate predicate
    for parameter in parameters do
      if result.predicate.containsFVar parameter.fvarId! then
        throwError "generated membership captured an unrelated operation instance"

-- Failed normalization cannot complete an unresolved operand, including one
-- hidden behind an apparently fully elaborated local let reference.
run_cmd liftTermElabM do
  let hole ← mkFreshExprMVar (mkConst ``Real)
  withLetDecl `hidden (mkConst ``Real) hole fun hidden => do
    let body ← mkAppM ``Eq #[hidden, hidden]
    let accepted ← try
      let _ ← normalizeBody body
      pure true
    catch _ => pure false
    if accepted then throwError "normalization accepted an unresolved local let"
    if ← hole.mvarId!.isAssigned then
      throwError "failed normalization assigned its caller's metavariable"

end MorewTest.Conic.Normalize
