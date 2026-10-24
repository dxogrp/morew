/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.ObjectiveContext
import Morew.Transform.Context
import Lean.Elab.Command

/-!
# Bound-context recognition and polarity regressions

Test the proof-producing recognizer independently of occurrence selection. The
source bounds are hypotheses; successful results are checked against the exact
requested inequality or predicate and checked by the kernel.
-/

namespace MorewTest.ObjectiveContextAutomation

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.ObjectiveContext

private def checkInequality (stx : TSyntax `term) (success : Bool := true) : TermElabM Unit := do
  let term ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let term ← instantiateMVars term
  lambdaTelescope term fun args relation => do
    let operands := relation.getAppArgs
    let point := args[args.size - 3]!
    let bound := args.back!
    let before ← getMCtx
    let result ← proveInequality point operands[2]! operands[3]! bound
    let after ← getMCtx
    unless before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
      throwError "context recognition leaked scratch metavariables"
    match result with
    | .error reason => if success then throwError "expected context proof: {reason}"
    | .ok proof =>
      unless success do throwError "unexpected context proof for {relation}"
      unless ← isDefEq (← inferType proof) relation do
        throwError "context proof has the wrong type: {← inferType proof}"
      checkWithKernel proof

private def checkPredicate (stx : TSyntax `term) (success : Bool := true) : TermElabM Unit := do
  let term ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let term ← instantiateMVars term
  lambdaTelescope term fun args target => do
    let point := args[args.size - 4]!
    let bound := args[args.size - 2]!
    let sourceProof := args.back!
    let result ← provePredicate point (← inferType sourceProof) target bound sourceProof
    match result with
    | .error reason => if success then throwError "expected constraint context proof: {reason}"
    | .ok proof =>
      unless success do throwError "unexpected predicate proof for {target}"
      unless ← isDefEq (← inferType proof) target do
        throwError "predicate context proof has the wrong type"
      checkWithKernel proof

noncomputable def hiddenMonotone (x : ℝ) : ℝ := Real.exp x
private def wrappedBound (x t : ℝ) : Prop := x ≤ t

run_cmd Lean.Elab.Command.liftTermElabM do
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => x ^ 2 ≤ t))
  checkInequality (← `(fun (x t : ℝ) (_ : wrappedBound x t) => x + 1 ≤ t + 1))
  checkInequality (← `(fun (x t : ℝ) (_ : Morew.BoundDirection.upper.Rel x t) =>
    x + 1 ≤ t + 1))
  checkInequality (← `(fun (x t : ℝ) (_ : Morew.BoundDirection.lower.Rel x t) =>
    t + 1 ≤ x + 1))
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => x ^ 2 + |x| ≤ t + |x|))
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) =>
    Real.exp (2 * x ^ 2 + 3 - |x|) ≤ Real.exp (2 * t + 3 - |x|)))
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => -t ≤ -(x ^ 2)))
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => x - t ≤ x - x ^ 2))
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => (-2) * t ≤ (-2) * x ^ 2))
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => t * (-2) ≤ x ^ 2 * (-2)))
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => 0 * t ≤ 0 * x ^ 2))
  checkInequality (← `(fun (c : ℝ) (_ : 0 ≤ c) (x t : ℝ) (_ : x ^ 2 ≤ t) =>
    c * x ^ 2 ≤ c * t))
  checkInequality (← `(fun (c : ℝ) (_ : 0 < c) (x t : ℝ) (_ : x ^ 2 ≤ t) =>
    x ^ 2 * c ≤ t * c))
  checkInequality (← `(fun (c : ℝ) (_ : c ≤ 0) (x t : ℝ) (_ : x ^ 2 ≤ t) =>
    c * t ≤ c * x ^ 2))
  checkInequality (← `(fun (c : ℝ) (_ : c < 0) (x t : ℝ) (_ : x ^ 2 ≤ t) =>
    t * c ≤ x ^ 2 * c))
  checkInequality (← `(fun (x t : ℝ) (_ : t ≤ x ^ 2) => t + x ≤ x ^ 2 + x))

run_cmd Lean.Elab.Command.liftTermElabM do
  checkPredicate (← `(fun (x t : ℝ) (_ : |x| ≤ t) (_ : t + x ^ 2 ≤ 10) =>
    |x| + x ^ 2 ≤ 10))
  checkPredicate (← `(fun (x t : ℝ) (_ : t ≤ x ^ 2) (_ : 1 ≤ t) => 1 ≤ x ^ 2))
  checkPredicate (← `(fun (x t : ℝ) (_ : |x| ≤ t) (_ : 10 ≥ t + x ^ 2) =>
    10 ≥ |x| + x ^ 2))
  checkPredicate (← `(fun (x t : ℝ) (_ : |x| ≤ t)
    (_ : (t + x ^ 2 ≤ 10 ∧ x ≠ 0) ∧ True) =>
    (|x| + x ^ 2 ≤ 10 ∧ x ≠ 0) ∧ True))

run_cmd Lean.Elab.Command.liftTermElabM do
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => t ≤ x ^ 2)) false
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) =>
    hiddenMonotone (x ^ 2) ≤ hiddenMonotone t)) false
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => |x ^ 2| ≤ |t|)) false
  checkInequality (← `(fun (c : ℝ) (x t : ℝ) (_ : x ^ 2 ≤ t) =>
    c * x ^ 2 ≤ c * t)) false
  checkInequality (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) => x * x ^ 2 ≤ x * t)) false
  checkPredicate (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) (_ : 1 ≤ t) => 1 ≤ x ^ 2)) false
  checkPredicate (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) (_ : t = 1) => x ^ 2 = 1)) false
  checkPredicate (← `(fun (x t : ℝ) (_ : x ^ 2 ≤ t) (_ : t < 1) => x ^ 2 < 1)) false
  checkInequality (← `(fun (x t : ℝ) (_ : x ≤ t) =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a * b⟩ x 1 ≤
      @HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a * b⟩ t 1)) false
  checkPredicate (← `(fun (x t : ℝ) (_ : x ≤ t)
    (_ : @LE.le ℝ ⟨fun a b => b ≤ a⟩ t 1) =>
    @LE.le ℝ ⟨fun a b => b ≤ a⟩ x 1)) false

run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← elabTerm (← `(fun (x t : ℝ) (_ : x ≤ t) => x ≤ t)) none
  synthesizeSyntheticMVarsNoPostponing
  lambdaTelescope (← instantiateMVars source) fun args _ => do
    let unknown ← mkFreshExprMVar (Lean.mkConst ``Real)
    let before ← getMCtx
    let .error _ ← proveInequality args[0]! unknown args[1]! args[2]!
      | throwError "an unresolved selected value was accepted"
    if ← unknown.mvarId!.isAssigned then
      throwError "context recognition assigned a caller metavariable"
    let after ← getMCtx
    unless before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
      throwError "failed context recognition leaked scratch metavariables"

run_cmd Lean.Elab.Command.liftTermElabM do
  let value ← elabTerm (← `((2 : ℝ))) none
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  withLetDecl `first (Lean.mkConst ``Real) value fun first =>
  withLetDecl `second (Lean.mkConst ``Real) value fun second => do
    if ← sameExpression first second then
      throwError "structural matching confused two local definitions with identical bodies"
    if ← sameExpression first value then
      throwError "structural matching unfolded a local definition"
    unless ← sameExpression first second (reduceStructure := true) do
      throwError "post-selection context comparison did not reduce local definitions"

end MorewTest.ObjectiveContextAutomation
