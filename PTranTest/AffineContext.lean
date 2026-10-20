import PTranTest.Affine
import PTran.Elab.Conic

/-!
# Affine certificates across elaborator contexts

These regressions exercise local proof and finite-index instances, unrelated
ambient algebra instances, and assigned metavariables hidden by declarations.
Every successful result is checked after the recognizer has restored its state.
-/

namespace PTranTest.AffineContext

open Lean Lean.Meta Lean.Elab.Term
open PTran.Elab.Affine PTranTest.Affine Matrix

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

private def assertRow (term : TSyntax `term) (parameterCount : Nat := 2) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let result ← match ← PTran.Elab.Conic.normalizeRow source with
      | .ok result => pure result
      | .error error =>
        throwError "expected affine row {source}\n{error.reason}"
    for expression in #[result.constraint, result.pointwiseIff] do
      if expression.hasMVar || expression.hasSorry then
        throwError "row normalization returned an incomplete certificate"
      checkWithKernel expression
    let .forallE _ domain _ _ ← whnf (← inferType source)
      | throwError "row test source is not a function"
    let expected ← withLocalDeclD `x domain fun x => do
      let holds ← mkAppM ``PTran.Conic.Constraint.Holds #[result.constraint, x]
      mkForallFVars #[x] (← mkAppM ``Iff #[holds, source.beta #[x]])
    unless ← isDefEq (← inferType result.pointwiseIff) expected do
      throwError "row certificate proves the wrong statement"

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRow (← `(fun c : ℝ => fun (hc : 0 < c) => fun x : ℝ =>
    let _h : c ≠ 0 := ne_of_gt hc
    x / c ≤ 1))
  assertRow (← `(fun c : ℝ => fun (hc : 0 < c) =>
    let _h : c ≠ 0 := ne_of_gt hc
    fun x : ℝ => x / c ≤ 1))
  assertRow (← `(fun x : ℝ => let y := x + 1; y ≤ 3)) 0
  assertRow (← `(fun c : ℝ => fun (hc : 0 < c) => fun x : ℝ =>
    let y := x + 1
    let _h : c ≠ 0 := ne_of_gt hc
    y / c ≤ 1))

/-! Explicit finite-index evidence scopes the vector operands too. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ℝ =>
    @dotProduct ι ℝ (Fintype.ofFinite ι) _ _ a (fun _ => x))) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ℝ =>
    @dotProduct ι ℝ (Fintype.ofFinite ι) _ _ (fun _ => x) a)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ℝ =>
    letI := Fintype.ofFinite ι
    a ⬝ᵥ (fun _ => x))) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) =>
    letI := Fintype.ofFinite ι
    fun x : ℝ => (fun _ => x) ⬝ᵥ a)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (A : Matrix (Fin 2) ι ℝ) =>
    fun x : ℝ => @Matrix.mulVec (Fin 2) ι ℝ _ (Fintype.ofFinite ι)
      A (fun _ => x + 1))) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (A : Matrix ι (Fin 2) ℝ) =>
    fun x : ℝ => @Matrix.vecMul ι (Fin 2) ℝ _ (Fintype.ofFinite ι)
      (fun _ => x - 1) A)) 3

/-! Unused ambient instances do not change the arithmetic in the source. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun [AddCommGroup ℝ] => fun x : ℝ => x)) 1
  assertAffine (← `(fun [AddCommGroup ℝ] => fun _ : ℝ => (2 : ℝ))) 1
  assertAffine (← `(fun [AddCommGroup ℝ] => fun x : ℝ => x + x)) 1
  assertAffine (← `(fun [Module ℝ ℝ] => fun x : ℝ => x)) 1
  assertAffine (← `(fun [Module ℝ ℝ] => fun _ : ℝ => (2 : ℝ))) 1
  assertAffine (← `(fun [Module ℝ (Fin 2 → ℝ)] =>
    fun x : Fin 2 → ℝ => (2 : ℝ) • x)) 1
  assertAffine (← `(fun [AddCommGroup ℝ] [Module ℝ ℝ] => fun x : ℝ => x)) 2
  assertAffine (← `(fun [Zero ℝ] => fun x : ℝ => x / 2)) 1
  assertAffine (← `(fun [OfNat ℝ 0] => fun x : ℝ => x / 2)) 1
  assertAffine (← `(fun c : ℝ => fun (_ : c ≠ 0) =>
    fun [Zero ℝ] => fun x : ℝ => x / c)) 3
  assertAffine (← `(fun c : ℝ => fun (_ : c ≠ 0) =>
    fun [OfNat ℝ 0] => fun x : ℝ => x / c)) 3

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

end PTranTest.AffineContext
