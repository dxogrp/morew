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

/-! Placeholders hidden in local values and types receive the same rejection
as direct placeholders, including through chains of local definitions. -/

private def rejectHiddenPlaceholder (source : Expr) : MetaM Unit := do
  if source.hasSorry || source.hasMVar then
    throwError "hidden-placeholder regression no longer hides its placeholder"
  rejectUnresolved source

run_cmd Lean.Elab.Command.liftTermElabM do
  let nat := Lean.mkConst ``Nat
  let type := mkSort (.succ .zero)
  let builder ← elaborate (← `(fun n : ℕ => fun x : ℝ => x ^ n))
  let typeBuilder ← elaborate (← `(fun _ : ℕ => ℕ))
  let unrelated ← mkFreshExprMVar nat
  let assigned ← mkFreshExprMVar nat
  assigned.mvarId!.assign (mkNatLit 7)
  for synthetic in [false, true] do
    let placeholder ← mkSorry nat synthetic
    rejectUnresolved (mkApp builder placeholder)
    withLetDecl `exponent nat placeholder fun exponent => do
      rejectHiddenPlaceholder (mkApp builder exponent)
      withLetDecl `exponentAlias nat exponent fun binding =>
        rejectHiddenPlaceholder (mkApp builder binding)
    -- This type reduces to Nat, so only inspecting its normal form would
    -- erase the placeholder before the local declaration is checked.
    let hiddenType := mkApp typeBuilder placeholder
    withLocalDeclD `exponent hiddenType fun exponent =>
      rejectHiddenPlaceholder (mkApp builder exponent)
    withLetDecl `exponentType type hiddenType fun exponentType =>
      withLetDecl `typeAlias type exponentType fun typeAlias =>
        withLocalDeclD `exponent typeAlias fun exponent =>
          rejectHiddenPlaceholder (mkApp builder exponent)
  if ← unrelated.mvarId!.isAssigned then
    throwError "placeholder rejection assigned an unrelated caller hole"
  unless (← instantiateMVars assigned) == mkNatLit 7 do
    throwError "placeholder rejection lost a caller assignment"

/-! Complete values and types remain valid through the same local-let chains. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let nat := Lean.mkConst ``Nat
  let type := mkSort (.succ .zero)
  let builder ← elaborate (← `(fun n : ℕ => fun x : ℝ => x ^ n))
  let typeBuilder ← elaborate (← `(fun _ : ℕ => ℕ))
  let accept := fun source => do
    let before ← getMCtx
    let .ok proof ← certifyGlobal source
      | throwError "a complete exponent hidden in local declarations was rejected"
    checkUnchanged before
    checkCertificate source proof
  accept (mkApp builder (mkNatLit 7))
  withLetDecl `exponent nat (mkNatLit 7) fun exponent =>
    withLetDecl `exponentAlias nat exponent fun binding =>
      accept (mkApp builder binding)
  withLetDecl `exponentType type (mkApp typeBuilder (mkNatLit 7)) fun exponentType =>
    withLetDecl `typeAlias type exponentType fun typeAlias =>
      withLocalDeclD `exponent typeAlias fun exponent =>
        accept (mkApp builder exponent)

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

/-! Local structural reductions can expose fixed exponents, coordinates, and
finite sets. These certificates must still prove smoothness of the original
source and leave caller metavariables untouched. -/

private def checkStructuralSource (source : Expr) : MetaM Unit := do
  let before ← getMCtx
  let result ← certifyGlobal source
  checkUnchanged before
  match result with
  | .ok proof => checkCertificate source proof
  | .error error => throwError "expected structural smoothness of {source}\n{error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  for term in [
    ← `(fun x : ℝ => x ^ ((fun _ : ℝ => (2 : ℕ)) x)),
    ← `(fun x : ℝ => x ^ (let _y := x; (2 : ℕ))),
    ← `(fun x : ℝ => x ^ ((2 : ℕ), x).1),
    ← `(fun x : ℝ => x ^ (((fun _ : ℝ => (2 : ℕ)) ∘ (fun y => y * y)) x)),
    ← `(fun x : ℝ => x ^ Nat.succ ((fun _ : ℝ => (1 : ℕ)) x)),
    ← `(fun x : ℝ => x ^ (1 + (let _y := x; (1 : ℕ)))),
    ← `(fun x : Fin 2 → ℝ => x ((fun _ : ℝ => (0 : Fin 2)) (x 1))),
    ← `(fun x : Fin 2 → ℝ => x (let _y := x 1; (0 : Fin 2))),
    ← `(fun x : Fin 2 → ℝ => x ((0 : Fin 2), x 1).1),
    ← `(fun x : Fin 2 → ℝ =>
      x (((fun _ : ℝ => (0 : Fin 2)) ∘ (fun y => y * y)) (x 1))),
    ← `(fun x : Fin 2 → ℝ =>
      x ⟨((fun _ : ℝ => (0 : ℕ)) (x 1)), by change (0 : ℕ) < 2; decide⟩),
    ← `(fun x : ℝ => ∑ _i ∈ ((fun _ : ℝ => ({0, 1} : Finset ℕ)) x), x),
    ← `(fun x : ℝ => ∑ _i ∈ (let _y := x; ({0, 1} : Finset ℕ)), x),
    ← `(fun x : ℝ => ∑ _i ∈ (({0, 1} : Finset ℕ), x).1, x),
    ← `(fun x : ℝ =>
      ∑ _i ∈ (((fun _ : ℝ => ({0, 1} : Finset ℕ)) ∘ (fun y => y * y)) x), x),
    ← `(fun x : ℝ => ∑ _i ∈ ({Nat.succ ((fun _ : ℝ => (0 : ℕ)) x)} : Finset ℕ), x)
  ] do
    checkStructuralSource (← elaborate term)

/-! Decision-independent real values stay constant after local structural
reductions, including underneath operations outside the smooth fragment. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for term in [
    ← `(fun x : ℝ => Real.log ((fun _ : ℝ => (1 : ℝ)) x)),
    ← `(fun x : ℝ => Real.log (let _y := x; (1 : ℝ))),
    ← `(fun x : ℝ => Real.log ((1 : ℝ), x).1),
    ← `(fun x : ℝ => Real.log (((fun _ : ℝ => (1 : ℝ)) ∘ (fun y => y * y)) x)),
    ← `(fun x : ℝ => |(fun _ : ℝ => (1 : ℝ)) x|),
    ← `(fun x : ℝ => |(let _y := x; (1 : ℝ))|),
    ← `(fun x : ℝ => |((1 : ℝ), x).1|),
    ← `(fun x : ℝ => |((fun _ : ℝ => (1 : ℝ)) ∘ (fun y => y * y)) x|)
  ] do
    checkStructuralSource (← elaborate term)
  for term in [
    ← `(fun f : ℝ → ℝ => fun x : ℝ => f ((fun _ : ℝ => (1 : ℝ)) x)),
    ← `(fun f : ℝ → ℝ => fun x : ℝ => f (let _y := x; (1 : ℝ))),
    ← `(fun f : ℝ → ℝ => fun x : ℝ => f ((1 : ℝ), x).1),
    ← `(fun f : ℝ → ℝ => fun x : ℝ =>
      f (((fun _ : ℝ => (1 : ℝ)) ∘ (fun y => y * y)) x))
  ] do
    let expression ← elaborate term
    lambdaBoundedTelescope expression 1 fun _ source => checkStructuralSource source

/-! The same local reductions can occur in value types, vector dimensions, and
finite-sum binder types. The original source remains the certificate's target. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for term in [
    ← `(fun x : ℝ =>
      (((fun _ : Fin ((fun _ : ℝ => 2) x) => x) + (fun _ => x) :
        Fin ((fun _ : ℝ => 2) x) → ℝ)) 0),
    ← `(fun x : ℝ => (show ((fun _ : ℝ => ℝ) x) from x * x)),
    ← `(fun x : ℝ => ∑ i : Fin ((fun _ : ℝ => (2 : ℕ)) x), x ^ i.val),
    ← `(fun x : ℝ => ∑ _i : Fin ((fun _ : ℝ => (2 : ℕ)) x), (1 : ℝ))
  ] do
    checkStructuralSource (← elaborate term)
  for term in [
    ← `(fun n : ℕ => fun x : ℝ => ∑ i : Fin ((fun _ : ℝ => n) x), x ^ i.val),
    ← `(fun n : ℕ => fun x : ℝ => ∑ _i : Fin ((fun _ : ℝ => n) x), (1 : ℝ))
  ] do
    let expression ← elaborate term
    lambdaBoundedTelescope expression 1 fun _ source => checkStructuralSource source
  let expression ← elaborate (← `(fun n : ℕ => fun i : Fin n => fun x : ℝ =>
    (((fun _ : Fin ((fun _ : ℝ => n) x) => x) + (fun _ => x) :
      Fin ((fun _ : ℝ => n) x) → ℝ)) i))
  lambdaBoundedTelescope expression 2 fun _ source => checkStructuralSource source

/-! Local function declarations and aliases may expose the same reductions. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for (builderTerm, valueTerm) in [
    (← `(fun n : ℝ → ℕ => fun x : ℝ => x ^ n x),
      ← `(fun y : ℝ => (let _z := y; (2 : ℕ)))),
    (← `(fun i : ℝ → Fin 2 => fun x : Fin 2 → ℝ => x (i (x 1))),
      ← `(fun y : ℝ => ((0 : Fin 2), y).1)),
    (← `(fun s : ℝ → Finset ℕ => fun x : ℝ => ∑ _i ∈ s x, x),
      ← `(fun y : ℝ => (fun _ : ℝ => ({0, 1} : Finset ℕ)) y))
  ] do
    let builder ← elaborate builderTerm
    let value ← elaborate valueTerm
    let type ← inferType value
    withLetDecl `fixedArgument type value fun binding =>
      withLetDecl `fixedArgumentAlias type binding fun aliasBinding =>
        checkStructuralSource (mkApp builder aliasBinding)

/-! Expansion does not bypass native-operation or dependency checks. Turning it
off also restores the rejection of a scalar abbreviation that ignores its argument. -/

private abbrev hiddenExponent (_ : ℝ) : ℕ := 2
private abbrev hiddenIndex (_ : ℝ) : Fin 2 := 0
private def hiddenIndices (_ : ℝ) : Finset ℕ := {0, 1}
private abbrev hiddenValue (_ : ℝ) : ℝ := 1

set_option morew.smooth.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => hiddenValue x)) .unknownHead 0 (some ``hiddenValue)

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => hiddenValue x))
  assertRejected (← `(fun x : ℝ => Real.log ((fun y : ℝ => y) x)))
    .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => |(fun y : ℝ => y) x|))
    .nonsmooth 0 (some ``abs)
  assertRejected (← `(fun f : ℝ → ℝ => fun x : ℝ => f ((fun y : ℝ => y) x)))
    .unknownHead 1
  assertRejected (← `(fun x : ℝ => Real.log (hiddenValue x)))
    .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => |hiddenValue x|)) .nonsmooth 0 (some ``abs)
  assertRejected (← `(fun x : ℝ =>
    x ^ ((fun y : ℝ => (if y ≤ 0 then 1 else 2 : ℕ)) x))) .dependency
  assertRejected (← `(fun x : ℝ =>
    x ^ Nat.succ ((fun y : ℝ => (if y ≤ 0 then 1 else 2 : ℕ)) x))) .dependency
  assertRejected (← `(fun x : Fin 2 → ℝ =>
    x ((fun y : ℝ => if y ≤ 0 then (0 : Fin 2) else 1) (x 1)))) .dependency
  assertRejected (← `(fun x : ℝ =>
    ∑ _i ∈ ((fun y : ℝ => ({0, 1} : Finset ℕ).filter (fun _ => y ≤ 0)) x), x))
    .dependency
  assertRejected (← `(fun x : ℝ => x ^ hiddenExponent x)) .dependency
  assertRejected (← `(fun x : Fin 2 → ℝ => x (hiddenIndex (x 1)))) .dependency
  assertRejected (← `(fun x : ℝ => ∑ _i ∈ hiddenIndices x, x)) .dependency
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => x ^ hiddenExponent c)) 1
  assertSmooth (← `(fun c : ℝ => fun x : Fin 2 → ℝ => x (hiddenIndex c))) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => ∑ _i ∈ hiddenIndices c, x)) 1

/-! Ambient analytic instances do not change the fixed native certificate. -/

private def checkAmbient (term : TSyntax `term) (parameterCount : Nat := 0)
    (instanceType? : Option Expr := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let baseline ← checkSuccess source
    let baselineType ← inferType baseline
    let .forallE _ decision _ _ ← whnf (← inferType source)
      | throwError "ambient-instance control is not a function"
    let instanceType := instanceType?.getD decision
    let groupType ← mkAppM ``NormedAddCommGroup #[instanceType]
    withLocalDecl `ambientGroup .instImplicit groupType fun ambientGroup => do
      let spaceType ← mkAppM ``NormedSpace #[Lean.mkConst ``Real, instanceType]
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

/-! Intermediate vectors need the same canonical enumeration even when their
index type does not occur in the scalar decision or result space. -/

private def checkIntermediateEnumeration (source indexType : Expr) : MetaM Unit := do
  let baseline ← checkSuccess source
  let baselineType ← inferType baseline
  let finiteType ← mkAppM ``Fintype #[indexType]
  withLocalDecl `ambientFintype .instImplicit finiteType fun ambient => do
    let before ← getMCtx
    let .ok proof ← certifyGlobal source
      | throwError "an ambient enumeration prevented intermediate-vector certification"
    checkUnchanged before
    checkCertificate source proof
    let proofType ← inferType proof
    if proof.containsFVar ambient.fvarId! || proofType.containsFVar ambient.fvarId! then
      throwError "intermediate-vector smoothness captured an ambient enumeration"
    unless ← isDefEq proofType baselineType do
      throwError "ambient enumeration changed the intermediate-vector certificate"

run_cmd Lean.Elab.Command.liftTermElabM do
  let indexType ← elaborate (← `(Fin 2))
  for term in [
    ← `(fun x : ℝ =>
      (((fun _ : Fin 2 => x) + (fun _ => x)) : Fin 2 → ℝ) 0),
    ← `(fun x : ℝ =>
      (((fun (_ : Fin 2) (_ : Fin 2) => x) + (fun _ _ => x)) :
        Fin 2 → Fin 2 → ℝ) 0 1),
    ← `(fun x : ℝ =>
      (((x, fun _ : Fin 2 => x) + (x, fun _ => x)) : ℝ × (Fin 2 → ℝ)).1)
  ] do
    checkIntermediateEnumeration (← elaborate term) indexType
  let expression ← elaborate (← `(fun n : ℕ => fun i : Fin n => fun x : ℝ =>
    (((fun _ : Fin n => x) + (fun _ => x)) : Fin n → ℝ) i))
  lambdaBoundedTelescope expression 2 fun parameters source => do
    checkIntermediateEnumeration source (← inferType parameters[1]!)
  let componentType ← elaborate (← `(Fin 2 → ℝ))
  checkAmbient (← `(fun x : ℝ =>
    (((x, fun _ : Fin 2 => x) + (x, fun _ => x)) : ℝ × (Fin 2 → ℝ)).1))
    0 (some componentType)
  checkAmbient (← `(fun x : ℝ =>
    (((fun _ : Fin 2 => x, x) + (fun _ => x, x)) : (Fin 2 → ℝ) × ℝ).2))
    0 (some componentType)

end MorewTest.NLP.Smooth
