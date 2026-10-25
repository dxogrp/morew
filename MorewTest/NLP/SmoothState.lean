/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.SmoothSupport

/-!
# Dependency checking and caller-state isolation

Unresolved values, types, and arithmetic instances can hide in local
declarations. Certification must inspect those declarations without assigning
caller metavariables, and successful proofs must survive state restoration.
-/

namespace MorewTest.NLP.Smooth

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.NLP.Smooth

private def checkUnchanged (before : MetavarContext) : MetaM Unit := do
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "smoothness certification leaked scratch metavariables"
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "smoothness certification changed a caller assignment"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "smoothness certification assigned an unresolved caller metavariable"

private def rejectUnresolved (source : Expr) : MetaM Unit := do
  let before ← getMCtx
  let .error error ← certifyGlobal source
    | throwError "an unresolved smoothness source was certified"
  checkUnchanged before
  unless error.kind == .unresolved do
    throwError "expected an unresolved-source diagnostic, got {repr error.kind}: {error.reason}"
  unless error.source == source do
    throwError "unresolved-source diagnostic changed the original source"

run_cmd Lean.Elab.Command.liftTermElabM do
  let good ← elaborate (← `(fun x : ℝ => Real.exp (x * x) + x ^ 3))
  let bad ← elaborate (← `(fun x : ℝ => Real.log x))
  let unresolved ← mkFreshExprMVar (mkConst ``Nat)
  let assigned ← mkFreshExprMVar (mkConst ``Nat)
  assigned.mvarId!.assign (mkNatLit 7)
  for _ in [:3] do
    let before ← getMCtx
    let .ok proof ← certifyGlobal good
      | throwError "state-isolation positive control was rejected"
    checkUnchanged before
    checkCertificate good proof
    let before ← getMCtx
    let .error error ← certifyGlobal bad
      | throwError "state-isolation negative control was certified"
    checkUnchanged before
    unless error.kind == .restrictedDomain do
      throwError "negative control failed before reaching its logarithm"
  if ← unresolved.mvarId!.isAssigned then
    throwError "certification assigned an unrelated caller hole"
  unless (← instantiateMVars assigned) == mkNatLit 7 do
    throwError "certification lost a caller assignment"

/-! Direct holes and holes hidden behind local value/type declarations. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => c + x))
  let missing ← mkFreshExprMVar real
  rejectUnresolved (mkApp builder missing)
  withLetDecl `coefficient real missing fun coefficient => do
    let source := mkApp builder coefficient
    if source.hasMVar then
      throwError "hidden-value regression no longer hides its metavariable"
    rejectUnresolved source
  if ← missing.mvarId!.isAssigned then
    throwError "certification assigned a missing coefficient"
  let missingType ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `coefficient missingType fun coefficient => do
    let source ← withLocalDeclD `x real fun x => mkLambdaFVars #[x] coefficient
    if source.hasMVar then
      throwError "hidden-type regression no longer hides its metavariable"
    rejectUnresolved source
  if ← missingType.mvarId!.isAssigned then
    throwError "certification assigned a missing coefficient type"

/-! An unresolved native-operation instance is not canonical evidence. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let instanceType ← elaborate (← `(HMul ℝ ℝ ℝ))
  let missing ← mkFreshExprMVar instanceType
  withLocalDeclD `x real fun x => do
    let body := mkAppN (mkConst ``HMul.hMul [.zero, .zero, .zero])
      #[real, real, real, missing, x, x]
    rejectUnresolved (← mkLambdaFVars #[x] body)
    withLetDecl `hiddenInstance instanceType missing fun hidden => do
      let body := mkAppN (mkConst ``HMul.hMul [.zero, .zero, .zero])
        #[real, real, real, hidden, x, x]
      let source ← mkLambdaFVars #[x] body
      if source.hasMVar then
        throwError "hidden-instance regression no longer hides its metavariable"
      rejectUnresolved source
  if ← missing.mvarId!.isAssigned then
    throwError "certification solved an operation instance to force acceptance"

/-! Assigned values and types are positive controls for hidden-hole checks. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => c * x))
  let assigned ← mkFreshExprMVar real
  let two ← mkNumeral real 2
  assigned.mvarId!.assign two
  withLetDecl `coefficient real assigned fun coefficient => do
    let source := mkApp builder coefficient
    let before ← getMCtx
    let .ok proof ← certifyGlobal source
      | throwError "an assigned coefficient hidden in a local value was rejected"
    checkUnchanged before
    checkCertificate source proof
  let assignedType ← mkFreshExprMVar (mkSort (.succ .zero))
  assignedType.mvarId!.assign real
  withLocalDeclD `coefficient assignedType fun coefficient => do
    let source := mkApp builder coefficient
    let before ← getMCtx
    let .ok proof ← certifyGlobal source
      | throwError "an assigned coefficient type was rejected"
    checkUnchanged before
    checkCertificate source proof

/-! Index sets and natural exponents must be independent of the decision. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : Fin 2 → ℝ => x (if x 0 ≤ 0 then 0 else 1))) .dependency
  assertRejected (← `(fun x : ℝ => x ^ (if x ≤ 0 then 1 else 2 : ℕ))) .dependency
  assertRejected (← `(fun x : ℝ =>
    ∑ _i ∈ ({0, 1} : Finset ℕ).filter (fun _ => x ≤ 0), x)) .dependency
  assertRejected (← `(fun x : Fin 2 → ℝ =>
    let i : Fin 2 := if x 0 ≤ 0 then 0 else 1
    x i)) .dependency
  assertRejected (← `(fun x : ℝ =>
    let n : ℕ := if x ≤ 0 then 1 else 2
    x ^ n)) .dependency
  assertSmooth (← `(fun i : Fin 2 => fun x : Fin 2 → ℝ => x i)) 1
  assertSmooth (← `(fun n : ℕ => fun x : ℝ => x ^ n)) 1

/-! Ambient analytic instances do not change the fixed native certificate. -/

private def checkAmbient (term : TSyntax `term) (parameterCount : Nat := 0) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let baseline ← checkSuccess source
    let baselineType ← inferType baseline
    let .forallE _ decision _ _ ← whnf (← inferType source)
      | throwError "ambient-instance control is not a function"
    let groupType ← mkAppM ``NormedAddCommGroup #[decision]
    withLocalDecl `ambientGroup .instImplicit groupType fun ambientGroup => do
      let spaceType ← mkAppM ``NormedSpace #[Lean.mkConst ``Real, decision]
      withLocalDecl `ambientSpace .instImplicit spaceType fun ambientSpace => do
        let proof ← checkSuccess source
        if proof.containsFVar ambientGroup.fvarId! || proof.containsFVar ambientSpace.fvarId! then
          throwError "smoothness certificate captured unrelated ambient analytic instances"
        unless ← isDefEq (← inferType proof) baselineType do
          throwError "ambient instances changed the native smoothness proposition"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAmbient (← `(fun x : ℝ => x * x))
  checkAmbient (← `(fun x : ℝ × ℝ => x.1 * x.2))
  checkAmbient (← `(fun x : Fin 2 → ℝ => x 0 * x 1))
  checkAmbient (← `(fun n : ℕ => fun x : ℝ × (Fin n → ℝ) =>
    x.1 + ∑ i, x.2 i ^ 2)) 1
  let source ← elaborate (← `(fun x : Fin 2 → ℝ => x 0 + x 1))
  let baseline ← checkSuccess source
  let baselineType ← inferType baseline
  let finiteType ← elaborate (← `(Fintype (Fin 2)))
  withLocalDecl `ambientFintype .instImplicit finiteType fun ambient => do
    let proof ← checkSuccess source
    if proof.containsFVar ambient.fvarId! then
      throwError "coordinate smoothness captured an unrelated finite enumeration"
    unless ← isDefEq (← inferType proof) baselineType do
      throwError "ambient enumeration changed coordinate smoothness"

end MorewTest.NLP.Smooth
