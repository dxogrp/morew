/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.QuadConic.Objective
import Morew.Elab.Affine
import Morew.Elab.Evidence
import Morew.Elab.QuadConic.Expansion
import Morew.Elab.Reformulation.Presentation
import Lean.Meta.Check

/-! Construct a quadratic part and an affine part whose sum equals the source objective.
Prove the required global curvature using evidence independent of decision variables.
Transparent helpers unfold within a shared budget. -/

namespace Morew.Elab.QuadConic

open Lean Lean.Meta Qq

/-- A quadratic decomposition and curvature proof for the presentation's sense. -/
structure ObjectiveResult where
  /-- The homogeneous quadratic part. -/
  quadratic : Expr
  /-- The affine part, including the constant term. -/
  affine : Expr
  /-- Exact agreement with the original objective at every decision point. -/
  pointwiseEquality : Expr
  /-- Proof that the quadratic part is nonnegative for minimization or nonpositive for
  maximization at every decision point. -/
  curvature : Expr

private structure CertifiedResult where
  certificate : Expr
  nonnegative? : Option Expr := none
  nonpositive? : Option Expr := none
  missing? : Option Expr := none

private abbrev ReifyM := ExceptT Expr.Error MetaM

private def reject (expression : Expr) (reason : MessageData) : ReifyM α := do
  throwThe Expr.Error {
    expression
    reason := ← addMessageContext
      m!"quadratic objective: {reason}\nexpression: {expression}" }

private noncomputable def canonicalNorm (n : Nat) (x : EuclideanSpace ℝ (Fin n)) : ℝ := ‖x‖

private theorem nonnegativeOfNegatedNonpositive {c : ℝ} (h : c ≤ 0) : 0 ≤ -c :=
  neg_nonneg.mpr h

private theorem nonpositiveOfNegatedNonnegative {c : ℝ} (h : 0 ≤ c) : -c ≤ 0 :=
  neg_nonpos.mpr h

private theorem nonnegativeInverse {c : ℝ} (h : 0 ≤ c) : 0 ≤ c⁻¹ := inv_nonneg.mpr h

private theorem nonpositiveInverse {c : ℝ} (h : c ≤ 0) : c⁻¹ ≤ 0 := inv_nonpos.mpr h

section Curvature

variable {X : Type*} [AddCommGroup X] [Module ℝ X]
variable {Q : QuadraticForm ℝ X}

-- Membership evidence stays bound in the attached index of every summand.
private def sumOnSupport {ι : Type*} (s : Finset ι) (f : ι → X → ℝ)
    (a : ∀ i : {i // i ∈ s}, Morew.QuadConic.Certified (f i)) :
    Morew.QuadConic.Certified (fun x => ∑ i ∈ s, f i x) :=
  (Morew.QuadConic.Certified.sum s.attach a).transport fun x =>
    Finset.sum_attach s (fun i => f i x)

private theorem nonnegativeSMulZero (c : ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hQ' : ∀ x, Q x ≤ 0) : ∀ x, 0 ≤ (c • Q) x := by
  intro x
  change 0 ≤ c * Q x
  rw [le_antisymm (hQ' x) (hQ x), mul_zero]

private theorem nonpositiveSMulZero (c : ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hQ' : ∀ x, Q x ≤ 0) : ∀ x, (c • Q) x ≤ 0 := by
  intro x
  change c * Q x ≤ 0
  rw [le_antisymm (hQ' x) (hQ x), mul_zero]

private theorem nonnegativeZeroSMul (Q : QuadraticForm ℝ X) :
    ∀ x, 0 ≤ ((0 : ℝ) • Q) x := by simp

private theorem nonpositiveZeroSMul (Q : QuadraticForm ℝ X) :
    ∀ x, ((0 : ℝ) • Q) x ≤ 0 := by simp

private theorem nonnegativeEmptySum {ι : Type*} (s : Finset ι)
    (Q : ι → QuadraticForm ℝ X) (h : s = ∅) : ∀ x, 0 ≤ (∑ i ∈ s, Q i) x := by
  simp [h]

private theorem nonpositiveEmptySum {ι : Type*} (s : Finset ι)
    (Q : ι → QuadraticForm ℝ X) (h : s = ∅) : ∀ x, (∑ i ∈ s, Q i) x ≤ 0 := by
  simp [h]

end Curvature

-- Specialize universal parameter assumptions at the current finite-sum indices.
private partial def parameterProjection? (proof goal : Expr) (indices : List Expr)
    (reuseIndices : Bool) : StateT Nat MetaM (Option Expr) := do
  if reuseIndices then
    let remaining ← get
    if remaining == 0 then return none
    set (remaining - 1)
  let type ← Expr.reduceStructure (← inferType proof)
  if ← isDefEq type goal then return some proof
  if type.isAppOfArity ``And 2 then
    if let some found ← parameterProjection? (← mkAppM ``And.left #[proof]) goal indices
        reuseIndices then
      return some found
    return ← parameterProjection? (← mkAppM ``And.right #[proof]) goal indices reuseIndices
  if let .forallE _ domain _ _ := type then
    for index in indices do
      if ← isDefEq domain (← inferType index) then
        let remaining := if reuseIndices then indices else indices.filter (· != index)
        if let some found ← parameterProjection? (mkApp proof index) goal remaining reuseIndices then
          return some found
  return none

private def parameterProof? (point goal : Expr) (indices : Array Expr) :
    MetaM (Option Expr) := do
  if (← Expr.depends point goal) || (← Expr.hasUnresolved goal) ||
      (← Evidence.hasPlaceholders goal) then return none
  if let some proof ← Evidence.proveIndependent? point goal then return some proof
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail || !(← isProp declaration.type) then continue
    let proof := declaration.toExpr
    if (← Expr.depends point proof) || (← Expr.hasUnresolved proof) ||
        (← Evidence.hasPlaceholders proof) then continue
    -- Preserve the search that consumes indices, then bound the fallback that reuses them.
    let found? ← match ← (parameterProjection? proof goal indices.toList false).run' 0 with
      | some found => pure (some found)
      | none => (parameterProjection? proof goal indices.toList true).run' 1024
    if let some found := found? then
      checkWithKernel found
      return some found
  return none

private partial def coefficientSign? (point value : Expr) (nonnegative : Bool)
    (indices : Array Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let value : Q(ℝ) := value
  let goal : Q(Prop) := if nonnegative then q(0 ≤ $value) else q($value ≤ 0)
  if let some proof ← parameterProof? point goal indices then return some proof
  let strict : Q(Prop) := if nonnegative then q(0 < $value) else q($value < 0)
  if let some proof ← parameterProof? point strict indices then
    return some (← mkAppM ``le_of_lt #[proof])
  let reduced ← Expr.reduceStructure value
  if reduced.isAppOfArity ``Neg.neg 3 then
    let operand : Q(ℝ) := reduced.getAppArgs[2]!
    unless ← isDefEq reduced q(-$operand) do return none
    if let some proof ← coefficientSign? point operand (!nonnegative) indices (fuel - 1) then
      return some (← mkAppM
        (if nonnegative then ``nonnegativeOfNegatedNonpositive
          else ``nonpositiveOfNegatedNonnegative) #[proof])
  return none

private def nonzeroProof? (point value : Expr) (indices : Array Expr) :
    MetaM (Option Expr) := do
  let value : Q(ℝ) := value
  if let some proof ← parameterProof? point q($value ≠ 0) indices then return some proof
  if let some proof ← parameterProof? point q(0 < $value) indices then
    return some (← mkAppM ``ne_of_gt #[proof])
  if let some proof ← parameterProof? point q($value < 0) indices then
    return some (← mkAppM ``ne_of_lt #[proof])
  return none

private def affineProvider (point : Expr) (indices : Array Expr)
    (provider : Affine.EvidenceProvider) : Affine.EvidenceProvider := {
  nonzeroEvidence? := some fun goal => do
    if goal.isAppOfArity ``Ne 3 then
      if let some proof ← nonzeroProof? point goal.getAppArgs[1]! indices then return some proof
    if let some supply := provider.nonzeroEvidence? then supply goal else pure none
}

private def affine? (point expression : Expr) (provider : Affine.EvidenceProvider)
    (indices : Array Expr) : MetaM (Except Expr.Error Expr) := do
  let source ← mkLambdaFVars #[point] expression
  -- The quadratic recognizer owns the shared helper-expansion budget.
  let result ← withOptions (fun options => options.set `morew.affine.maxExpansionDepth (0 : Nat)) <|
    Affine.reifyAffine source (affineProvider point indices provider)
  match result with
  | .error error => return .error error
  | .ok result =>
    return .ok (← Affine.Space.withCanonicalSpaces #[← inferType point, ← inferType expression] do
      mkAppM ``Morew.Affine.Certified.mk #[result.map, result.pointwiseEquality])

private def affineRequired (point expression : Expr) (provider : Affine.EvidenceProvider)
    (indices : Array Expr) : ReifyM Expr :=
  affine? point expression provider indices

private def checkPrefix (source expected : Expr) (operandCount : Nat) : ReifyM Unit := do
  let source := source.consumeMData
  let expected ← Expr.reduceStructure expected
  let args := source.getAppArgs
  let expectedArgs := expected.getAppArgs
  unless source.getAppFn == expected.getAppFn && args.size == expectedArgs.size &&
      operandCount ≤ args.size do
    reject source "unsupported operation or arithmetic instance"
  for i in [:args.size - operandCount] do
    unless ← isDefEq args[i]! expectedArgs[i]! do
      reject source "expected the canonical real operation"

private def finish (point source certificate : Expr) (count? : Option Nat := none) :
    ReifyM Expr := do
  let type ← instantiateMVars (← inferType certificate)
  unless type.isAppOf ``Morew.QuadConic.Certified do
    throwError "quadratic constructor returned an unexpected certificate type"
  let function := type.getAppArgs.back!
  if let some count := count? then checkPrefix source (function.beta #[point]) count
  unless ← isDefEq function (← mkLambdaFVars #[point] source) do
    reject source "quadratic construction does not match the typed expression"
  return certificate

private def construct (point source : Expr) (name : Name) (args : Array Expr)
    (count? : Option Nat := none) : ReifyM Expr := do
  let certificate ← Affine.Space.withCanonicalSpaces #[← inferType point, mkConst ``Real] do
    mkAppM name args
  finish point source certificate count?

private def proofApp (point : Expr) (name : Name) (args : Array Expr) : MetaM Expr := do
  Affine.Space.withCanonicalSpaces #[← inferType point, mkConst ``Real] do
    mkAppM name args

private def combineProof? (point : Expr) (name : Name) (args : Array Expr)
    (left right : Option Expr) : MetaM (Option Expr) := do
  match left, right with
  | some left, some right => return some (← proofApp point name (args ++ #[left, right]))
  | _, _ => return none

private def scaled (point coefficient certificate : Expr) (value : CertifiedResult)
    (indices : Array Expr) : MetaM CertifiedResult := do
  let quadratic ← mkProjection value.certificate `quadratic
  if ← isDefEq coefficient q((0 : ℝ)) then
    return {
      certificate
      nonnegative? := some (← proofApp point ``nonnegativeZeroSMul #[quadratic])
      nonpositive? := some (← proofApp point ``nonpositiveZeroSMul #[quadratic]) }
  if let some positive := value.nonnegative? then
    if let some negative := value.nonpositive? then
      return {
        certificate
        nonnegative? := some (← proofApp point ``nonnegativeSMulZero #[coefficient, positive, negative])
        nonpositive? := some (← proofApp point ``nonpositiveSMulZero #[coefficient, positive, negative]) }
  let positive ← coefficientSign? point coefficient true indices
  let negative ← coefficientSign? point coefficient false indices
  let args := #[coefficient, value.certificate]
  let nonnegative? ← match ← combineProof? point
      ``Morew.QuadConic.Certified.smul_nonnegative_of_nonneg args positive value.nonnegative? with
    | some proof => pure (some proof)
    | none =>
      combineProof? point
        ``Morew.QuadConic.Certified.smul_nonnegative_of_nonpos args negative value.nonpositive?
  let nonpositive? ← match ← combineProof? point
      ``Morew.QuadConic.Certified.smul_nonpositive_of_nonneg args positive value.nonpositive? with
    | some proof => pure (some proof)
    | none =>
      combineProof? point
        ``Morew.QuadConic.Certified.smul_nonpositive_of_nonpos args negative value.nonnegative?
  return {
    certificate
    nonnegative?
    nonpositive?
    missing? := value.missing?.orElse (fun _ => some coefficient) }

private partial def reifyBody (point expression : Expr) (provider : Affine.EvidenceProvider)
    (indices : Array Expr := #[]) : ReifyM CertifiedResult := do
  let expression ← Expr.reduceStructure expression (preserveLets := true)
  if let .letE name type value body nondep := expression then
    if (← Expr.depends point type) || (← Expr.depends point value) then
      return ← reifyBody point (body.instantiate1 value) provider indices
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← reifyBody point (body.instantiate1 binding) provider indices
      return { result with
        certificate := ← result.certificate.replaceFVarsM #[binding] #[value]
        nonnegative? := ← result.nonnegative?.mapM (·.replaceFVarsM #[binding] #[value])
        nonpositive? := ← result.nonpositive?.mapM (·.replaceFVarsM #[binding] #[value])
        missing? := ← result.missing?.mapM (·.replaceFVarsM #[binding] #[value]) }
  unless ← isDefEq (← inferType expression) q(ℝ) do
    reject expression "expected a real-valued objective"
  if let .ok affine ← ExceptT.lift (affine? point expression provider indices) then
    let certificate ← construct point expression ``Morew.QuadConic.Certified.ofAffine #[affine]
    return {
      certificate
      nonnegative? := some (← proofApp point ``Morew.QuadConic.Certified.ofAffine_nonnegative #[affine])
      nonpositive? := some (← proofApp point ``Morew.QuadConic.Certified.ofAffine_nonpositive #[affine]) }
  let head := expression.getAppFn.constName?
  let args := expression.getAppArgs
  if head == some ``HPow.hPow && args.size == 6 then
    let exponent ← Expr.reduceStructure args[5]!
    unless (← isDefEq (← inferType exponent) q(ℕ)) && (← getNatValue? exponent) == some 2 do
      reject expression "expected a square with natural exponent 2"
    let base ← Expr.reduceStructure args[4]!
    let (affine, constructor, proofName, emptyNorm) ← if base.isAppOfArity ``Morew.Fn.norm2 2 then do
        let affine ← affineRequired point base.getAppArgs[1]! provider indices
        pure (affine, ``Morew.QuadConic.Certified.fnNorm2Sq,
          ``Morew.QuadConic.Certified.fnNorm2Sq_nonnegative,
          ← isDefEq base.getAppArgs[0]! (mkNatLit 0))
      else if base.isAppOfArity ``Norm.norm 3 then do
        let normArgs := base.getAppArgs
        let some n ← Expr.euclideanDimension? normArgs[0]!
          | reject base "squared norms require a canonical Euclidean space or Fn.norm2"
        let expected := (mkAppN (← getConstInfo ``canonicalNorm).value! #[n, normArgs[2]!]).headBeta
        checkPrefix base expected 1
        let affine ← affineRequired point normArgs[2]! provider indices
        let coordinates ← Affine.Space.withCanonicalSpaces #[← inferType point, normArgs[0]!] do
          mkAppM ``Morew.Affine.Certified.ofEuclidean #[affine]
        pure (coordinates, ``Morew.QuadConic.Certified.fnNorm2Sq,
          ``Morew.QuadConic.Certified.fnNorm2Sq_nonnegative, ← isDefEq n (mkNatLit 0))
      else do
        let affine ← affineRequired point base provider indices
        pure (affine, ``Morew.QuadConic.Certified.square,
          ``Morew.QuadConic.Certified.square_nonnegative, false)
    let certificate ← construct point expression constructor #[affine] (some 2)
    let nonpositive? ← if emptyNorm then do
        pure (some (← proofApp point ``Morew.QuadConic.Certified.fnNorm2Sq_empty_nonpositive #[affine]))
      else pure none
    return {
      certificate
      nonnegative? := some (← proofApp point proofName #[affine])
      nonpositive? }
  if (head == some ``HAdd.hAdd || head == some ``HSub.hSub) && args.size == 6 then
    let left ← reifyBody point args[4]! provider indices
    let right ← reifyBody point args[5]! provider indices
    let add := head == some ``HAdd.hAdd
    let certificate ← construct point expression
      (if add then ``Morew.QuadConic.Certified.add else ``Morew.QuadConic.Certified.sub)
      #[left.certificate, right.certificate] (some 2)
    let nonnegative? ← combineProof? point
      (if add then ``Morew.QuadConic.Certified.add_nonnegative
        else ``Morew.QuadConic.Certified.sub_nonnegative)
      #[left.certificate, right.certificate]
      left.nonnegative? (if add then right.nonnegative? else right.nonpositive?)
    let nonpositive? ← combineProof? point
      (if add then ``Morew.QuadConic.Certified.add_nonpositive
        else ``Morew.QuadConic.Certified.sub_nonpositive)
      #[left.certificate, right.certificate]
      left.nonpositive? (if add then right.nonpositive? else right.nonnegative?)
    return {
      certificate
      nonnegative?
      nonpositive?
      missing? := left.missing?.orElse (fun _ => right.missing?) }
  if head == some ``Neg.neg && args.size == 3 then
    let value ← reifyBody point args[2]! provider indices
    let certificate ← construct point expression ``Morew.QuadConic.Certified.neg
      #[value.certificate] (some 1)
    return {
      certificate
      nonnegative? := ← value.nonpositive?.mapM (fun proof =>
        proofApp point ``Morew.QuadConic.Certified.neg_nonnegative #[value.certificate, proof])
      nonpositive? := ← value.nonnegative?.mapM (fun proof =>
        proofApp point ``Morew.QuadConic.Certified.neg_nonpositive #[value.certificate, proof])
      missing? := value.missing? }
  if (head == some ``HMul.hMul || head == some ``HSMul.hSMul) && args.size == 6 then
    let left := args[4]!
    let right := args[5]!
    let (coefficient, source, constructor, leftCoefficient) ←
      if !(← Expr.depends point left) then
        pure (left, right, if head == some ``HSMul.hSMul then ``Morew.QuadConic.Certified.smul
          else ``Morew.QuadConic.Certified.mulConstLeft, true)
      else if head == some ``HMul.hMul && !(← Expr.depends point right) then
        pure (right, left, ``Morew.QuadConic.Certified.mulConstRight, false)
      else reject expression "quadratic scaling requires a decision-independent coefficient"
    unless ← isDefEq (← inferType coefficient) q(ℝ) do
      reject coefficient "quadratic scaling requires a real coefficient"
    let value ← reifyBody point source provider indices
    let certificate ← construct point expression constructor
      (if leftCoefficient then #[coefficient, value.certificate] else #[value.certificate, coefficient])
      (some 2)
    scaled point coefficient certificate value indices
  else if head == some ``HDiv.hDiv && args.size == 6 then
    let divisor : Q(ℝ) := args[5]!
    if ← Expr.depends point divisor then
      reject divisor "the divisor depends on an optimization variable"
    let value ← reifyBody point args[4]! provider indices
    let some proof ← (affineProvider point indices provider).nonzeroEvidence?.get! q($divisor ≠ 0)
      | reject divisor m!"missing nonzero evidence; required {divisor} ≠ 0"
    unless (← isDefEq (← inferType proof) q($divisor ≠ 0)) &&
        !(← Expr.depends point proof) && !(← Expr.hasUnresolved proof) &&
        !(← Evidence.hasPlaceholders proof) do
      reject divisor "invalid independent nonzero evidence"
    let certificate ← construct point expression ``Morew.QuadConic.Certified.divConst
      #[value.certificate, divisor, proof] (some 2)
    let inverse : Q(ℝ) := q($divisor⁻¹)
    let positive ← coefficientSign? point divisor true indices
    let negative ← coefficientSign? point divisor false indices
    let positive ← positive.mapM (fun proof => mkAppM ``nonnegativeInverse #[proof])
    let negative ← negative.mapM (fun proof => mkAppM ``nonpositiveInverse #[proof])
    let result ← scaled point inverse certificate value indices
    let proofArgs := #[inverse, value.certificate]
    let nonnegative? ← match result.nonnegative? with
      | some proof => pure (some proof)
      | none =>
        match ← combineProof? point ``Morew.QuadConic.Certified.smul_nonnegative_of_nonneg
            proofArgs positive value.nonnegative? with
        | some proof => pure (some proof)
        | none =>
          combineProof? point ``Morew.QuadConic.Certified.smul_nonnegative_of_nonpos
            proofArgs negative value.nonpositive?
    let nonpositive? ← match result.nonpositive? with
      | some proof => pure (some proof)
      | none =>
        match ← combineProof? point ``Morew.QuadConic.Certified.smul_nonpositive_of_nonneg
            proofArgs positive value.nonpositive? with
        | some proof => pure (some proof)
        | none =>
          combineProof? point ``Morew.QuadConic.Certified.smul_nonpositive_of_nonpos
            proofArgs negative value.nonnegative?
    return { result with nonnegative?, nonpositive? }
  else if head == some ``Finset.sum && args.size == 5 then
    let set := args[3]!
    if ← Expr.depends point set then reject set "the finite sum's index set depends on a decision"
    let sourceFamily ← withLocalDeclD `i args[0]! fun i =>
      mkLambdaFVars #[i, point] (mkApp args[4]! i)
    let supportPredicate ← withLocalDeclD `i args[0]! fun i => do
      mkLambdaFVars #[i] (← mkAppM ``Membership.mem #[set, i])
    let supportType ← mkAppM ``Subtype #[supportPredicate]
    let support ← mkAppM ``Finset.attach #[set]
    let family ← withLocalDeclD `member supportType fun member => do
      let i ← mkProjection member `val
      let membership ← mkProjection member `property
      let value ← reifyBody point (mkApp args[4]! i) provider
        (indices.push i |>.push membership)
      return { value with
        certificate := ← mkLambdaFVars #[member] value.certificate
        nonnegative? := ← value.nonnegative?.mapM (fun proof => do return ← mkLambdaFVars #[member] proof)
        nonpositive? := ← value.nonpositive?.mapM (fun proof => do return ← mkLambdaFVars #[member] proof)
        missing? := none }
    let certificate ← construct point expression ``sumOnSupport
      #[set, sourceFamily, family.certificate] (some 2)
    let forms ← withLocalDeclD `i supportType fun i => do
      mkLambdaFVars #[i] (← mkProjection (mkApp family.certificate i) `quadratic)
    let empty ← mkAppOptM ``Finset.empty #[some supportType]
    if ← isDefEq support empty then
      let equality ← mkEqRefl support
      return {
        certificate
        nonnegative? := some (← proofApp point ``nonnegativeEmptySum #[support, forms, equality])
        nonpositive? := some (← proofApp point ``nonpositiveEmptySum #[support, forms, equality]) }
    let sumCurvature? (name : Name) (evidence? : Option Expr) : MetaM (Option Expr) :=
      evidence?.mapM fun proof => do
        let bounded ← withLocalDeclD `i supportType fun i => do
          let membership ← mkAppM ``Membership.mem #[support, i]
          withLocalDeclD `hi membership fun hi =>
            mkLambdaFVars #[i, hi] (mkApp proof i)
        proofApp point name #[support, family.certificate, bounded]
    return {
      certificate
      nonnegative? := ← sumCurvature? ``Morew.QuadConic.Certified.sum_nonnegative family.nonnegative?
      nonpositive? := ← sumCurvature? ``Morew.QuadConic.Certified.sum_nonpositive family.nonpositive? }
  else reject expression "expected affine terms, squared affine expressions, or signed sums of squares"

private def withFiniteInstances (instances : List Expr) (action : ReifyM ObjectiveResult) :
    ReifyM ObjectiveResult := do
  match instances with
  | [] => action
  | inst :: rest =>
    withLetDecl `_quadConicFinite (← inferType inst) inst fun binding => do
      let result ← withFiniteInstances rest action
      return {
        quadratic := ← result.quadratic.replaceFVarsM #[binding] #[inst]
        affine := ← result.affine.replaceFVarsM #[binding] #[inst]
        pointwiseEquality := ← result.pointwiseEquality.replaceFVarsM #[binding] #[inst]
        curvature := ← result.curvature.replaceFVarsM #[binding] #[inst] }

private def reifyCore (source original : Expr) (sense : Morew.ObjectiveSense)
    (provider : Affine.EvidenceProvider) : ReifyM ObjectiveResult := do
  if (← Expr.hasUnresolved original) || (← Evidence.hasPlaceholders original) then
    reject original "unresolved metavariables or proof placeholders in the objective"
  let .forallE _ domain codomain _ ← whnf (← inferType source)
    | reject source "expected a function on the decision space"
  if codomain.hasLooseBVars || !(← isDefEq codomain q(ℝ)) then
    reject source "expected a real-valued objective"
  let instances ← Expr.sourceFiniteInstances source
  withFiniteInstances instances.toList do
    unless ← Expr.isSupportedSpace domain do reject source "unsupported decision space"
    let result ← withLocalDeclD `point domain fun point =>
      reifyBody point (mkApp source point) provider
    let curvature? := match sense with
      | .minimize => result.nonnegative?
      | .maximize => result.nonpositive?
    let some curvature := curvature? | do
      let sign := match sense with
        | .minimize => "nonnegative"
        | .maximize => "nonpositive"
      reject (result.missing?.getD original)
        m!"quadratic expression recognized, but {sign} quadratic curvature was not established; provide independent coefficient-sign evidence"
    let quadratic ← instantiateMVars (← mkProjection result.certificate `quadratic)
    let affine ← instantiateMVars (← mkProjection result.certificate `affine)
    let pointwiseEquality ← instantiateMVars (← mkProjection result.certificate `correct)
    let curvature ← instantiateMVars curvature
    let expected ← withLocalDeclD `point domain fun point => do
      let qx ← mkAppM ``DFunLike.coe #[quadratic, point]
      let ax ← mkAppM ``DFunLike.coe #[affine, point]
      mkForallFVars #[point] (← mkEq (← mkAppM ``HAdd.hAdd #[qx, ax]) (mkApp original point))
    unless ← isDefEq (← inferType pointwiseEquality) expected do
      reject original "certificate does not establish equality with the original objective"
    let senseExpr := mkConst <| match sense with
      | .minimize => ``Morew.ObjectiveSense.minimize
      | .maximize => ``Morew.ObjectiveSense.maximize
    let expectedCurvature ← Affine.Space.withCanonicalSpaces #[domain] do
      mkAppM ``Morew.QuadConic.Curvature #[senseExpr, quadratic]
    unless ← isDefEq (← inferType curvature) expectedCurvature do
      reject original "curvature certificate does not match the quadratic part and objective sense"
    for expression in #[quadratic, affine, pointwiseEquality, curvature] do
      if (← Expr.hasUnresolved expression) || (← Evidence.hasPlaceholders expression) then
        reject original "quadratic construction left unresolved metavariables or placeholders"
      checkWithKernel expression
    return { quadratic, affine, pointwiseEquality, curvature }

/-- Prove an exact quadratic decomposition and the global sign required by the declared sense.
Try direct recognition before bounded unfolding of transparent helpers. -/
def reifyQuadratic (source : Expr) (sense : Morew.ObjectiveSense)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error ObjectiveResult) :=
  State.withIsolatedMVars do
    try
      let direct ← State.withIsolatedMVars <| (reifyCore source source sense provider).run
      if let .ok result := direct then return .ok result
      unless ← Expansion.enabled do return direct
      if (← Expr.hasUnresolved source) || (← Evidence.hasPlaceholders source) then return direct
      let expanded ← Expansion.prepare source
      if expanded.expansions == 0 then return direct
      (reifyCore expanded.expression source sense provider).run
    catch error =>
      return .error {
        expression := source
        reason := ← addMessageContext m!"quadratic objective: {error.toMessageData}" }

/-- Certify the typed presentation's objective using its declared optimization sense. -/
def reifyObjective (presentation : Reformulation.PresentationState)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error ObjectiveResult) :=
  State.withIsolatedMVars do
    if (← Expr.hasUnresolved presentation.valueType) ||
        (← Expr.hasUnresolved presentation.domainType) ||
        (← Expr.hasUnresolved presentation.objective) then
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext "quadratic objective: unresolved presentation" }
    unless (← whnf presentation.valueType).isConstOf ``Real do
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext "quadratic objective: expected a real-valued objective" }
    let expected ← mkArrow presentation.domainType presentation.valueType
    unless ← isDefEq (← inferType presentation.objective) expected do
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext "quadratic objective does not match the presentation types" }
    reifyQuadratic presentation.objective presentation.sense provider

end Morew.Elab.QuadConic
