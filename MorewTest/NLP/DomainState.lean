/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.DomainSupport
import MorewTest.NLP

/-!
# Domain certification state and source preservation

Hidden incomplete values must not become domain evidence. Successful results
are checked after caller state has been restored, including when the source is
an applied function or an objective imported from a semantic problem module.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.NLP.Domain

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.NLP

private def checkUnchanged (before : MetavarContext) : MetaM Unit := do
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "domain certification leaked scratch metavariables"
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "domain certification changed a caller assignment"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "domain certification assigned an unresolved caller metavariable"

private def isolatedSuccess (feasible : Expr) (sources : Array Expr) :
    MetaM Domain.DomainResult := do
  let before ← getMCtx
  let result ← Domain.certify feasible sources
  checkUnchanged before
  let .ok result := result
    | match result with
      | .error error => throwError "expected a complete domain certificate: {error.reason}"
      | .ok _ => throwError "unreachable domain result"
  checkResult feasible sources result
  return result

private def isolatedFailure (feasible : Expr) (sources : Array Expr)
    (kind : Smooth.SmoothFailureKind) : MetaM Domain.DomainError := do
  let before ← getMCtx
  let result ← Domain.certify feasible sources
  checkUnchanged before
  let .error error := result
    | throwError "incomplete or unsupported domain input was certified"
  unless error.kind == kind do
    throwError "wrong domain failure kind: {repr error.kind}\n{error.reason}"
  if (← error.reason.toString).isEmpty then
    throwError "domain rejection has no diagnostic"
  return error

/-! A later failing source rolls back an attempt that already certified an
earlier source. Neither success nor failure changes unrelated caller holes. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let feasible ← elaborate (← `(fun x : ℝ => 1 ≤ x))
  let good ← elaborate (← `(fun x : ℝ => Real.log x))
  let bad ← elaborate (← `(fun x : ℝ => Real.log (-x)))
  let unresolved ← mkFreshExprMVar (Lean.mkConst ``Nat)
  let assigned ← mkFreshExprMVar (Lean.mkConst ``Nat)
  assigned.mvarId!.assign (mkNatLit 7)
  discard <| isolatedSuccess feasible #[good]
  let environment ← getEnv
  let error ← isolatedFailure feasible #[good, bad] .feasibleInclusion
  unless error.sourceIndex? == some 1 do
    throwError "failure did not identify the later source"
  unless (← getEnv).constants.toList.length == environment.constants.toList.length do
    throwError "failed domain certification leaked auxiliary declarations"
  discard <| isolatedSuccess feasible #[good]
  if ← unresolved.mvarId!.isAssigned then
    throwError "domain certification assigned an unrelated caller hole"
  unless (← instantiateMVars assigned) == mkNatLit 7 do
    throwError "domain certification lost a caller assignment"

/-! Incomplete coefficient values/types and operation instances can be hidden
behind local declarations; the corresponding completed values are accepted. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let feasible ← elaborate (← `(fun _x : ℝ => True))
  let sourceBuilder ← elaborate (← `(fun c : ℝ => fun x : ℝ => c * x))
  let missing ← mkFreshExprMVar real
  withLetDecl `coefficient real missing fun coefficient => do
    let source := mkApp sourceBuilder coefficient
    if source.hasMVar then throwError "coefficient hole was not hidden in the local context"
    discard <| isolatedFailure feasible #[source] .unresolved
  let two ← mkNumeral real 2
  missing.mvarId!.assign two
  withLetDecl `coefficient real missing fun coefficient =>
    discard <| isolatedSuccess feasible #[mkApp sourceBuilder coefficient]
  let missingType ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `coefficient missingType fun coefficient => do
    let source ← withLocalDeclD `x real fun x => mkLambdaFVars #[x] coefficient
    if source.hasMVar then throwError "coefficient type hole was not hidden"
    discard <| isolatedFailure feasible #[source] .unresolved
  if ← missingType.mvarId!.isAssigned then
    throwError "domain certification solved an unknown coefficient type"
  missingType.mvarId!.assign real
  withLocalDeclD `coefficient missingType fun coefficient =>
    discard <| isolatedSuccess feasible #[mkApp sourceBuilder coefficient]
  let operationType ← elaborate (← `(HMul ℝ ℝ ℝ))
  let missingOperation ← mkFreshExprMVar operationType
  withLetDecl `operation operationType missingOperation fun operation =>
    withLocalDeclD `x real fun x => do
      let body := mkAppN (Lean.mkConst ``HMul.hMul [.zero, .zero, .zero])
        #[real, real, real, operation, x, x]
      let source ← mkLambdaFVars #[x] body
      if source.hasMVar then throwError "operation hole was not hidden"
      discard <| isolatedFailure feasible #[source] .unresolved
  if ← missingOperation.mvarId!.isAssigned then
    throwError "domain certification solved an unknown arithmetic instance"

/-! Placeholders remain incomplete when hidden by local aliases or by a type
that reduces to Nat. Complete controls exercise the same local structures. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let nat := Lean.mkConst ``Nat
  let feasible ← elaborate (← `(fun _x : ℝ => True))
  let sourceBuilder ← elaborate (← `(fun n : ℕ => fun x : ℝ => x ^ n))
  let typeBuilder ← elaborate (← `(fun _ : ℕ => ℕ))
  for synthetic in [false, true] do
    let placeholder ← mkSorry nat synthetic
    withLetDecl `exponent nat placeholder fun exponent =>
      withLetDecl `exponentAlias nat exponent fun binding => do
        let source := mkApp sourceBuilder binding
        if source.hasSorry || source.hasMVar then throwError "placeholder was not hidden"
        discard <| isolatedFailure feasible #[source] .unresolved
    withLocalDeclD `exponent (mkApp typeBuilder placeholder) fun exponent => do
      let source := mkApp sourceBuilder exponent
      if source.hasSorry || source.hasMVar then throwError "type placeholder was not hidden"
      discard <| isolatedFailure feasible #[source] .unresolved
  withLetDecl `exponent nat (mkNatLit 2) fun exponent =>
    withLetDecl `exponentAlias nat exponent fun binding =>
      discard <| isolatedSuccess feasible #[mkApp sourceBuilder binding]
  withLocalDeclD `exponent (mkApp typeBuilder (mkNatLit 2)) fun exponent =>
    discard <| isolatedSuccess feasible #[mkApp sourceBuilder exponent]

/-! Hidden incomplete row bounds are rejected before they can supply evidence. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let feasibleBuilder ← elaborate (← `(fun c : ℝ => fun x : ℝ => c ≤ x))
  let source ← elaborate (← `(fun x : ℝ => Real.log x))
  let missing ← mkFreshExprMVar real
  withLetDecl `bound real missing fun bound =>
    discard <| isolatedFailure (mkApp feasibleBuilder bound) #[source] .unsupportedRow
  if ← missing.mvarId!.isAssigned then
    throwError "row admission assigned a missing bound"
  let placeholder ← mkSorry real true
  withLetDecl `bound real placeholder fun bound =>
    discard <| isolatedFailure (mkApp feasibleBuilder bound) #[source] .unsupportedRow

/-! Applied parameter/proof binders and imported problem objectives retain
their expressions and their printed presentation after certification. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let feasibleBuilder ← elaborate (← `(fun a : ℝ => fun x : ℝ => a ≤ x))
  let sourceBuilder ← elaborate (← `(fun a : ℝ => fun ha : 0 < a => fun x : ℝ =>
    let _h : 0 < a := ha
    Real.log x + Real.log a))
  let real := Lean.mkConst ``Real
  withLocalDeclD `a real fun a => do
    let positive ← mkAppM ``LT.lt #[← mkNumeral real 0, a]
    withLocalDeclD `ha positive fun ha => do
      let feasible := mkApp feasibleBuilder a
      let source := mkAppN sourceBuilder #[a, ha]
      let printed ← ppExpr source
      let printedFeasible ← ppExpr feasible
      discard <| isolatedSuccess feasible #[source]
      unless (← ppExpr source).pretty == printed.pretty &&
          (← ppExpr feasible).pretty == printedFeasible.pretty do
        throwError "certification changed the applied source presentation"
  let feasible ← elaborate (← `(fun x : ℝ => 1 ≤ x))
  let imported ← elaborate (← `(MorewTest.NLP.logProblem.objective))
  let printed ← ppExpr imported
  let declaration ← getConstInfo ``MorewTest.NLP.logProblem
  discard <| isolatedSuccess feasible #[imported]
  unless (← ppExpr imported).pretty == printed.pretty do
    throwError "certification changed the imported objective presentation"
  unless (← getConstInfo ``MorewTest.NLP.logProblem).value? == declaration.value? do
    throwError "certification changed an imported model declaration"

/-! Imported/applied feasibility fields expose exactly their admitted row facts.
The result still proves inclusion for the original model-field expression. -/

private noncomputable def groupedLogProblem : Morew.Problem ℝ ℝ where
  objective := Real.log
  feasible x := True ∧ (1 ≤ x ∧ x ≤ 3)

private def wrappedLowerBound (x : ℝ) : Prop := 1 ≤ x

private noncomputable def wrappedLogProblem : Morew.Problem ℝ ℝ where
  objective := Real.log
  feasible := wrappedLowerBound

run_cmd Lean.Elab.Command.liftTermElabM do
  let feasible ← elaborate (← `(closedLogProblem.feasible))
  let objective ← elaborate (← `(closedLogProblem.objective))
  let originalFeasible ← ppExpr feasible
  let originalObjective ← ppExpr objective
  discard <| isolatedSuccess feasible #[objective]
  unless (← ppExpr feasible).pretty == originalFeasible.pretty &&
      (← ppExpr objective).pretty == originalObjective.pretty do
    throwError "certification changed imported model fields"
  withInput (← `(fun lower : ℝ => fun _h : 0 < lower =>
    ((lowerBoundLogProblem lower).feasible, #[(lowerBoundLogProblem lower).objective]))) 2
      fun feasible sources => do
    discard <| isolatedSuccess feasible sources
  withInput (← `(fun c : ℝ => fun _hc : 0 < Real.exp c =>
    ((lowerBoundLogProblem (Real.exp c)).feasible,
      #[(lowerBoundLogProblem (Real.exp c)).objective]))) 2 fun feasible sources => do
    discard <| isolatedSuccess feasible sources
  withInput (← `((groupedLogProblem.feasible,
    #[groupedLogProblem.objective, fun x : ℝ => Real.sqrt (4 - x)]))) 0
      fun feasible sources => do
    discard <| isolatedSuccess feasible sources
  withInput (← `(((lowerBoundLogProblem 0).feasible,
    #[(lowerBoundLogProblem 0).objective]))) 0 fun feasible sources => do
    discard <| isolatedFailure feasible sources .feasibleInclusion
  withInput (← `((wrappedLogProblem.feasible, #[wrappedLogProblem.objective]))) 0
      fun feasible sources => do
    discard <| isolatedFailure feasible sources .unsupportedRow

-- An approved strict margin can simplify to True and still be needed for an
-- ordered-ring deduction. Retaining it must not expose unsupplied row proofs.
open Lean.Elab Lean.Elab.Tactic in
example (x c : ℝ) (h : 0 < Real.exp c) (hx : Real.exp c ≤ x) : 0 < x := by
  run_tac
    let point := mkFVar (← getFVarId (mkIdent `x))
    let margin := mkFVar (← getFVarId (mkIdent `h))
    let row := mkFVar (← getFVarId (mkIdent `hx))
    let goal ← getMainGoal
    let target ← goal.getType
    if (← Domain.Evidence.prove? point target #[margin]).isSome then
      throwError "domain proof search used an unsupplied decision-dependent row"
    let some proof ← Domain.Evidence.prove? point target #[margin, row]
      | throwError "domain proof search discarded an approved strict margin"
    checkWithKernel proof
    goal.assign proof

/-! Unused ambient analytic instances do not enter the returned domain proofs. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let feasible ← elaborate (← `(fun x : ℝ × ℝ => 1 ≤ x.1 ∧ 1 ≤ x.2))
  let source ← elaborate (← `(fun x : ℝ × ℝ => Real.log x.1 + Real.sqrt x.2))
  let baseline ← isolatedSuccess feasible #[source]
  let decision ← elaborate (← `(ℝ × ℝ))
  let groupType ← mkAppM ``NormedAddCommGroup #[decision]
  withLocalDecl `ambientGroup .instImplicit groupType fun group => do
    let spaceType ← mkAppM ``NormedSpace #[Lean.mkConst ``Real, decision]
    withLocalDecl `ambientSpace .instImplicit spaceType fun space => do
      let result ← isolatedSuccess feasible #[source]
      for proof in result.smooth ++ #[result.domainIsOpen, result.feasibleMemDomain] do
        if proof.containsFVar group.fvarId! || proof.containsFVar space.fvarId! then
          throwError "domain certification captured unrelated analytic instances"
      unless ← isDefEq result.domain baseline.domain do
        throwError "ambient instances changed the inferred domain"
  let canonical ← elaborate (← `(fun [LE ℝ] => fun x : ℝ =>
    @LE.le ℝ Real.instLE 1 x))
  lambdaBoundedTelescope canonical 1 fun _ feasible => do
    let source ← elaborate (← `(fun x : ℝ => Real.log x))
    discard <| isolatedSuccess feasible #[source]
  let altered ← elaborate (← `(fun x : ℝ => @LE.le ℝ ⟨fun _ _ => True⟩ 1 x))
  let source ← elaborate (← `(fun x : ℝ => Real.log x))
  discard <| isolatedFailure altered #[source] .unsupportedRow

/-! Domain inference validates native instances even for constants, while the
global certifier retains its original constant-function behavior. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let feasible ← elaborate (← `(fun _x : ℝ => True))
  for source in #[
      (← `(fun _x : ℝ => @HAdd.hAdd ℝ ℝ ℝ ⟨fun _ b => b + b⟩ 1 1)),
      (← `(fun _x : ℝ => @HDiv.hDiv ℝ ℝ ℝ ⟨fun _ b => b / b⟩ 1 1)),
      (← `(fun _x : ℝ => @HPow.hPow ℝ ℝ ℝ ⟨fun _ b => (1 : ℝ) ^ b⟩ 1 1))] do
    let source ← elaborate source
    discard <| isolatedFailure feasible #[source] .invalidInstance
    discard <| MorewTest.NLP.Smooth.checkSuccess source
  MorewTest.NLP.Smooth.assertRejected (← `(fun x : ℝ => x ^ x)) .dependency
  MorewTest.NLP.Smooth.assertRejected
    (← `(fun r : ℝ => fun x : ℝ => Real.rpow (Real.log x) r))
    .restrictedDomain 1 (some ``Real.log)

/-! A vacuous obligation inside an empty support cannot become evidence for a
later source whose logarithm is evaluated outside that support. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let feasible ← elaborate (← `(fun _x : ℝ => True))
  let emptySum ← elaborate (← `(fun x : ℝ => ∑ _i ∈ (∅ : Finset Nat), Real.log x))
  discard <| isolatedSuccess feasible #[emptySum]
  let logarithm ← elaborate (← `(fun x : ℝ => Real.log x))
  let error ← isolatedFailure feasible #[emptySum, logarithm] .feasibleInclusion
  unless error.sourceIndex? == some 1 && error.source == logarithm do
    throwError "finite-support facts escaped into an unrelated source"

end MorewTest.NLP.Domain
