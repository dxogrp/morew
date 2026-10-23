import MorewTest.Affine.Support

/-!
# Local declarations in affine recognition

Proof lets remain available during recognition. Assigned metavariables hidden
in local values and types are accepted; unresolved ones are rejected without
assigning caller state. Successful certificates are checked after scope restoration.
-/

namespace MorewTest.Affine.LocalContext

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Affine MorewTest.Affine

/-! A proof let remains available while recognizing its body. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun c : ℝ => fun (hc : 0 < c) =>
    let _h : c ≠ 0 := ne_of_gt hc
    fun x : ℝ => x / c)) 2
  assertAffine (← `(fun c : ℝ => fun (hc : 0 < c) => fun x : ℝ =>
    let _h : c ≠ 0 := ne_of_gt hc
    x / c)) 2
  assertAffine (← `(fun c : ℝ => fun (hc : 0 < c) => fun x : ℝ =>
    have _h : c ≠ 0 := ne_of_gt hc
    x / c)) 2
  assertAffine (← `(fun c : ℝ => fun (hc : 0 < c) => fun x : ℝ =>
    (fun y : ℝ => let _h : c ≠ 0 := ne_of_gt hc; y / c) (x + 1))) 2
  assertAffine (← `(fun c : ℝ => fun (hc : 0 < c) => fun p : ℝ × ℝ =>
    match p with
    | (x, y) =>
      let _h : c ≠ 0 := ne_of_gt hc
      (x + 2 * y) / c)) 2

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate (← `(fun c : ℝ => fun (hc : 0 < c) => fun x : ℝ =>
    let _h : c ≠ 0 := if x ≤ 0 then ne_of_gt hc else ne_of_gt hc
    x / c))
  lambdaBoundedTelescope expression 2 fun _ source => do
    match ← reifyAffine source with
    | .ok _ => throwError "accepted a nonzero witness depending on the decision point"
    | .error error =>
      if (← error.reason.toString).isEmpty then
        throwError "dependent nonzero evidence was rejected without a diagnostic"


/-! Constraint normalization preserves proof lets before splitting the row. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRow (← `(fun c : ℝ => fun (hc : 0 < c) => fun x : ℝ =>
    let _h : c ≠ 0 := ne_of_gt hc
    x / c ≤ 1)) 2
  assertRow (← `(fun c : ℝ => fun (hc : 0 < c) =>
    let _h : c ≠ 0 := ne_of_gt hc
    fun x : ℝ => x / c ≤ 1)) 2
  assertRow (← `(fun x : ℝ => let y := x + 1; y ≤ 3)) 0
  assertRow (← `(fun c : ℝ => fun (hc : 0 < c) => fun x : ℝ =>
    let y := x + 1
    let _h : c ≠ 0 := ne_of_gt hc
    y / c ≤ 1)) 2


/-! Assigned metavariables hidden in values and types are already resolved. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let assignedCoefficient ← mkFreshExprMVar real
  let two ← mkNumeral real 2
  assignedCoefficient.mvarId!.assign two
  withLetDecl `coefficient real assignedCoefficient fun coefficient => do
    let source ← withLocalDeclD `x real fun x => do
      mkLambdaFVars #[x] (← mkAppM ``HMul.hMul #[coefficient, x])
    if source.hasMVar then
      throwError "assigned-value regression no longer hides its metavariable"
    match ← reifyAffine source with
    | .ok result => checkResult source result
    | .error error => throwError "assigned coefficient rejected: {error.reason}"
    unless (← instantiateMVars assignedCoefficient) == two do
      throwError "recognition changed the caller's coefficient assignment"
  let assignedType ← mkFreshExprMVar (mkSort (.succ .zero))
  assignedType.mvarId!.assign real
  withLocalDeclD `coefficient assignedType fun coefficient => do
    let source ← withLocalDeclD `x real fun x => do
      mkLambdaFVars #[x] (← mkAppM ``HMul.hMul #[coefficient, x])
    if source.hasMVar then
      throwError "assigned-type regression no longer hides its metavariable"
    match ← reifyAffine source with
    | .ok result => checkResult source result
    | .error error => throwError "assigned coefficient type rejected: {error.reason}"
    unless (← instantiateMVars assignedType) == real do
      throwError "recognition changed the caller's type assignment"

/-! Genuinely unresolved coefficient values still fail without assignment. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let unresolved ← mkFreshExprMVar real
  withLetDecl `coefficient real unresolved fun coefficient => do
    let source ← withLocalDeclD `x real fun x => do
      mkLambdaFVars #[x] (← mkAppM ``HMul.hMul #[coefficient, x])
    if source.hasMVar then
      throwError "unresolved-value regression no longer hides its metavariable"
    if (← reifyAffine source).isOk then
      throwError "accepted an unresolved coefficient hidden behind a local let"
    if ← unresolved.mvarId!.isAssigned then
      throwError "recognition assigned the caller's coefficient metavariable"
  let unresolvedType ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `coefficient unresolvedType fun coefficient => do
    let source ← withLocalDeclD `x real fun x => mkLambdaFVars #[x] coefficient
    if source.hasMVar then
      throwError "unresolved-type regression no longer hides its metavariable"
    if (← reifyAffine source).isOk then
      throwError "accepted an unresolved type hidden in a local declaration"
    if ← unresolvedType.mvarId!.isAssigned then
      throwError "recognition assigned the caller's type metavariable"


/-! An unresolved operation instance cannot be assigned to force recognition. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let instanceType ← elaborate (← `(HMul ℝ ℝ ℝ))
  let unresolvedInstance ← mkFreshExprMVar instanceType
  withLocalDeclD `x real fun x => do
    let body := mkAppN (mkConst ``HMul.hMul [.zero, .zero, .zero])
      #[real, real, real, unresolvedInstance, ← mkNumeral real 2, x]
    let source ← mkLambdaFVars #[x] body
    if (← reifyAffine source).isOk then
      throwError "recognized an unresolved multiplication instance"
    if ← unresolvedInstance.mvarId!.isAssigned then
      throwError "reification assigned an instance metavariable"
    withLetDecl `hidden instanceType unresolvedInstance fun hidden => do
      let body := mkAppN (mkConst ``HMul.hMul [.zero, .zero, .zero])
        #[real, real, real, hidden, ← mkNumeral real 2, x]
      let source ← mkLambdaFVars #[x] body
      if source.hasMVar then
        throwError "hidden-instance regression no longer hides its metavariable"
      if (← reifyAffine source).isOk then
        throwError "recognized an unresolved instance hidden behind a local let"
      if ← unresolvedInstance.mvarId!.isAssigned then
        throwError "reification assigned a hidden instance metavariable"

/-! A locally available nonzero proof must itself be fully elaborated. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  withLocalDeclD `c real fun c => do
    let obligation ← mkAppM ``Ne #[c, ← mkNumeral real 0]
    let unresolvedProof ← mkFreshExprMVar obligation
    withLetDecl `hiddenNonzero obligation unresolvedProof fun _ =>
      withLocalDeclD `x real fun x => do
        let body ← mkAppM ``HDiv.hDiv #[x, c]
        let source ← mkLambdaFVars #[x] body
        if source.hasMVar then
          throwError "hidden-evidence regression no longer hides its metavariable"
        if (← reifyAffine source).isOk then
          throwError "accepted unresolved nonzero evidence hidden behind a local let"
        if ← unresolvedProof.mvarId!.isAssigned then
          throwError "reification assigned the hidden nonzero evidence metavariable"


/-! Metavariables hidden inside local relation instances must not be solved
temporarily while manufacturing a certificate for an incomplete predicate. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let orderType ← mkAppM ``LE #[real]
  let unresolvedOrder ← mkFreshExprMVar orderType
  withLetDecl `localOrder orderType unresolvedOrder fun order => do
    let predicate ← withLocalDeclD `x real fun x => do
      let relation := mkAppN (Lean.mkConst ``LE.le [Level.zero]) #[real, order, x, x]
      mkLambdaFVars #[x] relation
    unless !predicate.hasMVar do
      throwError "test did not hide the metavariable in the local context"
    let .error error ← Morew.Elab.Conic.normalizeRow predicate
      | throwError "a predicate with a hidden metavariable was accepted"
    unless (← error.reason.toString).contains "unresolved metavariables" do
      throwError "missing hidden-metavariable diagnostic"
  if ← unresolvedOrder.mvarId!.isAssigned then
    throwError "row normalization assigned a caller metavariable"

end MorewTest.Affine.LocalContext
