/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/
module

public import Morew.QuadConic.Objective
public import Morew.Elab.Affine
public import Morew.Elab.Evidence
public import Morew.Elab.QuadConic.Expansion
public import Morew.Elab.Objective
public import Lean.Meta.Check

/-! Construct or validate a quadratic part and an affine part whose sum equals the source objective.
Automatic recognition proves global curvature using evidence independent of decision variables.
Completed and supplied certificates share validation. Transparent helpers unfold within a shared budget. -/

public section

namespace Morew.Elab.QuadConic

open Lean Lean.Meta Qq

/-- A quadratic decomposition and curvature proof for the presentation's sense. -/
meta structure ObjectiveResult where
  /-- The homogeneous quadratic part. -/
  quadratic : Expr
  /-- The affine part, including the constant term. -/
  affine : Expr
  /-- Exact agreement with the original objective at every decision point. -/
  pointwiseEquality : Expr
  /-- Proof that the quadratic part is nonnegative for minimization or nonpositive for
  maximization at every decision point. -/
  curvature : Expr

private meta structure CertifiedResult where
  certificate : Expr
  nonneg? : Option Expr := none
  nonpos? : Option Expr := none
  missing? : Option Expr := none

private meta abbrev ReifyM := ExceptT Expr.Error MetaM

private meta def reject (expression : Expr) (reason : MessageData) : ReifyM α := do
  throwThe Expr.Error {
    expression
    reason := ← addMessageContext
      m!"quadratic objective: {reason}\nexpression: {expression}" }

-- Printing a synthetic sorry in a diagnostic suppresses that error in Lean.
private meta def rejectIncomplete (expression : Expr) : ReifyM α := do
  throwThe Expr.Error {
    expression
    reason := ← addMessageContext
      "quadratic objective: unresolved metavariables or proof placeholders" }

private meta def canonicalNorm : Expr :=
  q(fun (n : Nat) (x : EuclideanSpace ℝ (Fin n)) => ‖x‖)

private meta def zeroMatrix : Expr := q(fun (n : Nat) => (0 : Matrix (Fin n) (Fin n) ℝ))

private meta def positiveSemidefinite : Expr :=
  q(fun (n : Nat) (Q : Matrix (Fin n) (Fin n) ℝ) => Q.PosSemidef)

-- Native expressions retain both source enumerations and use the canonical real operations.
private meta def indexedQuadForm : Expr :=
  q(fun (n : Nat) (outer inner : Fintype (Fin n))
      (v : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) =>
    @dotProduct (Fin n) ℝ outer _ _ v (@Matrix.mulVec (Fin n) (Fin n) ℝ _ inner Q v))

theorem indexedQuadForm_eq (n : Nat) (outer inner : Fintype (Fin n))
    (v : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    Morew.Fn.quadForm v Q =
      @dotProduct (Fin n) ℝ outer _ _ v
        (@Matrix.mulVec (Fin n) (Fin n) ℝ _ inner Q v) := by
  have ho : outer = Fin.fintype n := Subsingleton.elim _ _
  have hi : inner = Fin.fintype n := Subsingleton.elim _ _
  subst outer inner
  rfl

theorem nonnegOfNegatedNonpos {c : ℝ} (h : c ≤ 0) : 0 ≤ -c :=
  neg_nonneg.mpr h

theorem nonposOfNegatedNonneg {c : ℝ} (h : 0 ≤ c) : -c ≤ 0 :=
  neg_nonpos.mpr h

theorem nonnegInverse {c : ℝ} (h : 0 ≤ c) : 0 ≤ c⁻¹ := inv_nonneg.mpr h

theorem nonposInverse {c : ℝ} (h : c ≤ 0) : c⁻¹ ≤ 0 := inv_nonpos.mpr h

section Curvature

variable {X : Type*} [AddCommGroup X] [Module ℝ X]
variable {Q : QuadraticForm ℝ X}

/-- Certify a finite sum using certificates indexed by membership in its support. -/
@[expose] def sumOnSupport {ι : Type*} (s : Finset ι) (f : ι → X → ℝ)
    (a : ∀ i : {i // i ∈ s}, Morew.QuadConic.CertifiedExpr (f i)) :
    Morew.QuadConic.CertifiedExpr (fun x => ∑ i ∈ s, f i x) :=
  (Morew.QuadConic.CertifiedExpr.sum s.attach a).transport fun x =>
    Finset.sum_attach s (fun i => f i x)

theorem nonnegSMulZero (c : ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hQ' : ∀ x, Q x ≤ 0) : ∀ x, 0 ≤ (c • Q) x := by
  intro x
  change 0 ≤ c * Q x
  rw [le_antisymm (hQ' x) (hQ x), mul_zero]

theorem nonposSMulZero (c : ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hQ' : ∀ x, Q x ≤ 0) : ∀ x, (c • Q) x ≤ 0 := by
  intro x
  change c * Q x ≤ 0
  rw [le_antisymm (hQ' x) (hQ x), mul_zero]

theorem nonnegZeroSMul (Q : QuadraticForm ℝ X) :
    ∀ x, 0 ≤ ((0 : ℝ) • Q) x := by simp

theorem nonposZeroSMul (Q : QuadraticForm ℝ X) :
    ∀ x, ((0 : ℝ) • Q) x ≤ 0 := by simp

theorem nonnegEmptySum {ι : Type*} (s : Finset ι)
    (Q : ι → QuadraticForm ℝ X) (h : s = ∅) : ∀ x, 0 ≤ (∑ i ∈ s, Q i) x := by
  simp [h]

theorem nonposEmptySum {ι : Type*} (s : Finset ι)
    (Q : ι → QuadraticForm ℝ X) (h : s = ∅) : ∀ x, (∑ i ∈ s, Q i) x ≤ 0 := by
  simp [h]

end Curvature

-- Specialize universal parameter assumptions at the current finite-sum indices.
private meta partial def parameterProjection? (proof goal : Expr) (indices : List Expr)
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

private meta def parameterProof? (point goal : Expr) (indices : Array Expr) :
    MetaM (Option Expr) := do
  if (← Expr.depends point goal) || !(← Evidence.complete goal) then return none
  if let some proof ← Evidence.proveIndependent? point goal then return some proof
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail || !(← isProp declaration.type) then continue
    let proof := declaration.toExpr
    if (← Expr.depends point proof) || !(← Evidence.complete proof) then continue
    -- Preserve the search that consumes indices, then bound the fallback that reuses them.
    let found? ← match ← (parameterProjection? proof goal indices.toList false).run' 0 with
      | some found => pure (some found)
      | none => (parameterProjection? proof goal indices.toList true).run' 1024
    if let some found := found? then
      checkWithKernel found
      return some found
  return none

private meta partial def coefficientSign? (point value : Expr) (nonneg : Bool)
    (indices : Array Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let value : Q(ℝ) := value
  let goal : Q(Prop) := if nonneg then q(0 ≤ $value) else q($value ≤ 0)
  if let some proof ← parameterProof? point goal indices then return some proof
  let strict : Q(Prop) := if nonneg then q(0 < $value) else q($value < 0)
  if let some proof ← parameterProof? point strict indices then
    return some (← mkAppM ``le_of_lt #[proof])
  let reduced ← Expr.reduceStructure value
  if reduced.isAppOfArity ``Neg.neg 3 then
    let operand : Q(ℝ) := reduced.getAppArgs[2]!
    unless ← isDefEq reduced q(-$operand) do return none
    if let some proof ← coefficientSign? point operand (!nonneg) indices (fuel - 1) then
      return some (← mkAppM
        (if nonneg then ``nonnegOfNegatedNonpos
          else ``nonposOfNegatedNonneg) #[proof])
  return none

private meta def nonzeroProof? (point value : Expr) (indices : Array Expr) :
    MetaM (Option Expr) := do
  let value : Q(ℝ) := value
  if let some proof ← parameterProof? point q($value ≠ 0) indices then return some proof
  if let some proof ← parameterProof? point q(0 < $value) indices then
    return some (← mkAppM ``ne_of_gt #[proof])
  if let some proof ← parameterProof? point q($value < 0) indices then
    return some (← mkAppM ``ne_of_lt #[proof])
  return none

private meta def affineProvider (point : Expr) (indices : Array Expr)
    (provider : Affine.EvidenceProvider) : Affine.EvidenceProvider := {
  nonzeroEvidence? := some fun goal => do
    if goal.isAppOfArity ``Ne 3 then
      if let some proof ← nonzeroProof? point goal.getAppArgs[1]! indices then return some proof
    if let some supply := provider.nonzeroEvidence? then supply goal else pure none
}

private meta def affine? (point expression : Expr) (provider : Affine.EvidenceProvider)
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

private meta def checkPrefix (source expected : Expr) (operandCount : Nat) : ReifyM Unit := do
  let source := source.consumeMData
  let expected ← Expr.reduceStructure expected
  match ← Expr.operationPrefixMismatch? source expected operandCount with
  | none => pure ()
  | some .shape => reject source "unsupported operation or arithmetic instance"
  | some .argument => reject source "expected the canonical real operation"

private meta def finish (point source certificate : Expr) (count? : Option Nat := none) :
    ReifyM Expr := do
  let type ← instantiateMVars (← inferType certificate)
  unless type.isAppOf ``Morew.QuadConic.CertifiedExpr do
    throwError "quadratic constructor returned an unexpected certificate type"
  let function := type.getAppArgs.back!
  if let some count := count? then checkPrefix source (function.beta #[point]) count
  unless ← isDefEq function (← mkLambdaFVars #[point] source) do
    reject source "quadratic construction does not match the typed expression"
  return certificate

private meta def construct (point source : Expr) (name : Name) (args : Array Expr)
    (count? : Option Nat := none) : ReifyM Expr := do
  let certificate ← Affine.Space.withCanonicalSpaces #[← inferType point, mkConst ``Real] do
    mkAppM name args
  finish point source certificate count?

private meta def proofApp (point : Expr) (name : Name) (args : Array Expr) : MetaM Expr := do
  Affine.Space.withCanonicalSpaces #[← inferType point, mkConst ``Real] do
    mkAppM name args

private meta def combineProof? (point : Expr) (name : Name) (args : Array Expr)
    (left right : Option Expr) : MetaM (Option Expr) := do
  match left, right with
  | some left, some right => return some (← proofApp point name (args ++ #[left, right]))
  | _, _ => return none

private meta def scaled (point coefficient certificate : Expr) (value : CertifiedResult)
    (indices : Array Expr) : MetaM CertifiedResult := do
  let quadratic ← mkProjection value.certificate `quadratic
  if ← isDefEq coefficient q((0 : ℝ)) then
    return {
      certificate
      nonneg? := some (← proofApp point ``nonnegZeroSMul #[quadratic])
      nonpos? := some (← proofApp point ``nonposZeroSMul #[quadratic]) }
  if let some positive := value.nonneg? then
    if let some negative := value.nonpos? then
      return {
        certificate
        nonneg? := some (← proofApp point ``nonnegSMulZero #[coefficient, positive, negative])
        nonpos? := some (← proofApp point ``nonposSMulZero #[coefficient, positive, negative]) }
  let positive ← coefficientSign? point coefficient true indices
  let negative ← coefficientSign? point coefficient false indices
  let args := #[coefficient, value.certificate]
  let nonneg? ← match ← combineProof? point
      ``Morew.QuadConic.CertifiedExpr.smul_nonneg_of_nonneg args positive value.nonneg? with
    | some proof => pure (some proof)
    | none =>
      combineProof? point
        ``Morew.QuadConic.CertifiedExpr.smul_nonneg_of_nonpos args negative value.nonpos?
  let nonpos? ← match ← combineProof? point
      ``Morew.QuadConic.CertifiedExpr.smul_nonpos_of_nonneg args positive value.nonpos? with
    | some proof => pure (some proof)
    | none =>
      combineProof? point
        ``Morew.QuadConic.CertifiedExpr.smul_nonpos_of_nonpos args negative value.nonneg?
  return {
    certificate
    nonneg?
    nonpos?
    missing? := value.missing?.orElse (fun _ => some coefficient) }

private meta partial def reifyBody (point expression : Expr) (provider : Affine.EvidenceProvider)
    (indices : Array Expr := #[]) : ReifyM CertifiedResult := do
  let expression ← Expr.reduceStructure expression (preserveLets := true)
  if let .letE name type value body nondep := expression then
    if (← Expr.depends point type) || (← Expr.depends point value) then
      return ← reifyBody point (body.instantiate1 value) provider indices
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← reifyBody point (body.instantiate1 binding) provider indices
      return { result with
        certificate := ← result.certificate.replaceFVarsM #[binding] #[value]
        nonneg? := ← result.nonneg?.mapM (·.replaceFVarsM #[binding] #[value])
        nonpos? := ← result.nonpos?.mapM (·.replaceFVarsM #[binding] #[value])
        missing? := ← result.missing?.mapM (·.replaceFVarsM #[binding] #[value]) }
  unless ← isDefEq (← inferType expression) q(ℝ) do
    reject expression "expected a real-valued objective"
  if let .ok affine ← ExceptT.lift (affine? point expression provider indices) then
    let certificate ← construct point expression ``Morew.QuadConic.CertifiedExpr.ofAffine #[affine]
    return {
      certificate
      nonneg? := some (← proofApp point ``Morew.QuadConic.CertifiedExpr.ofAffine_nonneg #[affine])
      nonpos? := some (← proofApp point ``Morew.QuadConic.CertifiedExpr.ofAffine_nonpos #[affine]) }
  let head := expression.getAppFn.constName?
  let args := expression.getAppArgs
  if (head == some ``Morew.Fn.quadForm && args.size == 3) ||
      (head == some ``dotProduct && args.size == 7) then
    let (n, vector, matrix, native?) ← if head == some ``Morew.Fn.quadForm then
        pure (args[0]!, args[1]!, args[2]!, (none : Option (Expr × Expr)))
      else do
        let index ← whnf args[0]!
        unless index.isAppOfArity ``Fin 1 do
          reject expression "matrix quadratic forms require real coordinate vectors indexed by Fin n"
        let product ← Expr.reduceStructure args[6]!
        unless product.isAppOfArity ``Matrix.mulVec 7 do
          reject expression "expected a vector dotted with a fixed matrix times the same vector"
        let productArgs := product.getAppArgs
        let n := index.getAppArgs[0]!
        let vector := args[5]!
        let matrix := productArgs[5]!
        for instanceExpr in #[args[2]!, productArgs[4]!] do
          if ← Expr.depends point instanceExpr then
            reject instanceExpr "the finite indexing instance depends on an optimization variable"
        let expected := (mkAppN indexedQuadForm
          #[n, args[2]!, productArgs[4]!, vector, matrix]).headBeta
        checkPrefix expression expected 2
        checkPrefix product expected.getAppArgs[6]! 2
        unless ← isDefEq vector productArgs[6]! do
          reject expression "matrix quadratic forms require the same vector on both sides"
        pure (n, vector, matrix, some (args[2]!, productArgs[4]!))
    if ← Expr.depends point matrix then
      reject matrix "the quadratic coefficient matrix depends on an optimization variable"
    let affine ← ExceptT.mk (affine? point vector provider indices)
    let named ← mkAppM ``Morew.Fn.quadForm #[vector, matrix]
    let certificate ← construct point named ``Morew.QuadConic.CertifiedExpr.quadForm
      #[affine, matrix]
    let certificate ← match native? with
      | none => finish point expression certificate
      | some (outer, inner) => do
        let equality ← mkAppM ``indexedQuadForm_eq #[n, outer, inner, vector, matrix]
        let equality ← mkLambdaFVars #[point] equality
        let transported ← proofApp point ``Morew.QuadConic.CertifiedExpr.transport
          #[certificate, equality]
        finish point expression transported
    if ← isDefEq n (mkNatLit 0) then
      return {
        certificate
        nonneg? := some (← proofApp point
          ``Morew.QuadConic.CertifiedExpr.quadForm_empty_nonneg #[affine, matrix])
        nonpos? := some (← proofApp point
          ``Morew.QuadConic.CertifiedExpr.quadForm_empty_nonpos #[affine, matrix]) }
    if ← isDefEq matrix ((mkApp zeroMatrix n).headBeta) then
      return {
        certificate
        nonneg? := some (← proofApp point
          ``Morew.QuadConic.CertifiedExpr.quadForm_zero_nonneg #[affine])
        nonpos? := some (← proofApp point
          ``Morew.QuadConic.CertifiedExpr.quadForm_zero_nonpos #[affine]) }
    let positive ← parameterProof? point ((mkAppN positiveSemidefinite #[n, matrix]).headBeta) indices
    return {
      certificate
      nonneg? := ← positive.mapM (fun proof =>
        proofApp point ``Morew.QuadConic.CertifiedExpr.quadForm_nonneg #[affine, matrix, proof])
      missing? := some matrix }
  if head == some ``HPow.hPow && args.size == 6 then
    let exponent ← Expr.reduceStructure args[5]!
    unless (← isDefEq (← inferType exponent) q(ℕ)) && (← getNatValue? exponent) == some 2 do
      reject expression "expected a square with natural exponent 2"
    let base ← Expr.reduceStructure args[4]!
    let (affine, constructor, proofName, emptyNorm) ← if base.isAppOfArity ``Morew.Fn.norm2 2 then do
        let affine ← ExceptT.mk (affine? point base.getAppArgs[1]! provider indices)
        pure (affine, ``Morew.QuadConic.CertifiedExpr.fnNorm2Sq,
          ``Morew.QuadConic.CertifiedExpr.fnNorm2Sq_nonneg,
          ← isDefEq base.getAppArgs[0]! (mkNatLit 0))
      else if base.isAppOfArity ``Norm.norm 3 then do
        let normArgs := base.getAppArgs
        let some n ← Expr.euclideanDimension? normArgs[0]!
          | reject base "squared norms require a canonical Euclidean space or Fn.norm2"
        let expected := (mkAppN canonicalNorm #[n, normArgs[2]!]).headBeta
        checkPrefix base expected 1
        let affine ← ExceptT.mk (affine? point normArgs[2]! provider indices)
        let coordinates ← Affine.Space.withCanonicalSpaces #[← inferType point, normArgs[0]!] do
          mkAppM ``Morew.Affine.Certified.ofEuclidean #[affine]
        pure (coordinates, ``Morew.QuadConic.CertifiedExpr.fnNorm2Sq,
          ``Morew.QuadConic.CertifiedExpr.fnNorm2Sq_nonneg, ← isDefEq n (mkNatLit 0))
      else do
        let affine ← ExceptT.mk (affine? point base provider indices)
        pure (affine, ``Morew.QuadConic.CertifiedExpr.square,
          ``Morew.QuadConic.CertifiedExpr.square_nonneg, false)
    let certificate ← construct point expression constructor #[affine] (some 2)
    let nonpos? ← if emptyNorm then do
        pure (some (← proofApp point ``Morew.QuadConic.CertifiedExpr.fnNorm2Sq_empty_nonpos #[affine]))
      else pure none
    return {
      certificate
      nonneg? := some (← proofApp point proofName #[affine])
      nonpos? }
  if (head == some ``HAdd.hAdd || head == some ``HSub.hSub) && args.size == 6 then
    let left ← reifyBody point args[4]! provider indices
    let right ← reifyBody point args[5]! provider indices
    let add := head == some ``HAdd.hAdd
    let certificate ← construct point expression
      (if add then ``Morew.QuadConic.CertifiedExpr.add else ``Morew.QuadConic.CertifiedExpr.sub)
      #[left.certificate, right.certificate] (some 2)
    let nonneg? ← combineProof? point
      (if add then ``Morew.QuadConic.CertifiedExpr.add_nonneg
        else ``Morew.QuadConic.CertifiedExpr.sub_nonneg)
      #[left.certificate, right.certificate]
      left.nonneg? (if add then right.nonneg? else right.nonpos?)
    let nonpos? ← combineProof? point
      (if add then ``Morew.QuadConic.CertifiedExpr.add_nonpos
        else ``Morew.QuadConic.CertifiedExpr.sub_nonpos)
      #[left.certificate, right.certificate]
      left.nonpos? (if add then right.nonpos? else right.nonneg?)
    return {
      certificate
      nonneg?
      nonpos?
      missing? := left.missing?.orElse (fun _ => right.missing?) }
  if head == some ``Neg.neg && args.size == 3 then
    let value ← reifyBody point args[2]! provider indices
    let certificate ← construct point expression ``Morew.QuadConic.CertifiedExpr.neg
      #[value.certificate] (some 1)
    return {
      certificate
      nonneg? := ← value.nonpos?.mapM (fun proof =>
        proofApp point ``Morew.QuadConic.CertifiedExpr.neg_nonneg #[value.certificate, proof])
      nonpos? := ← value.nonneg?.mapM (fun proof =>
        proofApp point ``Morew.QuadConic.CertifiedExpr.neg_nonpos #[value.certificate, proof])
      missing? := value.missing? }
  if (head == some ``HMul.hMul || head == some ``HSMul.hSMul) && args.size == 6 then
    let left := args[4]!
    let right := args[5]!
    let (coefficient, source, constructor, leftCoefficient) ←
      if !(← Expr.depends point left) then
        pure (left, right, if head == some ``HSMul.hSMul then ``Morew.QuadConic.CertifiedExpr.smul
          else ``Morew.QuadConic.CertifiedExpr.mulConstLeft, true)
      else if head == some ``HMul.hMul && !(← Expr.depends point right) then
        pure (right, left, ``Morew.QuadConic.CertifiedExpr.mulConstRight, false)
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
        !(← Expr.depends point proof) && (← Evidence.complete proof) do
      reject divisor "invalid independent nonzero evidence"
    let certificate ← construct point expression ``Morew.QuadConic.CertifiedExpr.divConst
      #[value.certificate, divisor, proof] (some 2)
    let inverse : Q(ℝ) := q($divisor⁻¹)
    let positive ← coefficientSign? point divisor true indices
    let negative ← coefficientSign? point divisor false indices
    let positive ← positive.mapM (fun proof => mkAppM ``nonnegInverse #[proof])
    let negative ← negative.mapM (fun proof => mkAppM ``nonposInverse #[proof])
    let result ← scaled point inverse certificate value indices
    let proofArgs := #[inverse, value.certificate]
    let nonneg? ← match result.nonneg? with
      | some proof => pure (some proof)
      | none =>
        match ← combineProof? point ``Morew.QuadConic.CertifiedExpr.smul_nonneg_of_nonneg
            proofArgs positive value.nonneg? with
        | some proof => pure (some proof)
        | none =>
          combineProof? point ``Morew.QuadConic.CertifiedExpr.smul_nonneg_of_nonpos
            proofArgs negative value.nonpos?
    let nonpos? ← match result.nonpos? with
      | some proof => pure (some proof)
      | none =>
        match ← combineProof? point ``Morew.QuadConic.CertifiedExpr.smul_nonpos_of_nonneg
            proofArgs positive value.nonpos? with
        | some proof => pure (some proof)
        | none =>
          combineProof? point ``Morew.QuadConic.CertifiedExpr.smul_nonpos_of_nonpos
            proofArgs negative value.nonneg?
    return { result with nonneg?, nonpos? }
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
        nonneg? := ← value.nonneg?.mapM (fun proof => do return ← mkLambdaFVars #[member] proof)
        nonpos? := ← value.nonpos?.mapM (fun proof => do return ← mkLambdaFVars #[member] proof)
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
        nonneg? := some (← proofApp point ``nonnegEmptySum #[support, forms, equality])
        nonpos? := some (← proofApp point ``nonposEmptySum #[support, forms, equality]) }
    let sumCurvature? (name : Name) (evidence? : Option Expr) : MetaM (Option Expr) :=
      evidence?.mapM fun proof => do
        let bounded ← withLocalDeclD `i supportType fun i => do
          let membership ← mkAppM ``Membership.mem #[support, i]
          withLocalDeclD `hi membership fun hi =>
            mkLambdaFVars #[i, hi] (mkApp proof i)
        proofApp point name #[support, family.certificate, bounded]
    return {
      certificate
      nonneg? := ← sumCurvature? ``Morew.QuadConic.CertifiedExpr.sum_nonneg family.nonneg?
      nonpos? := ← sumCurvature? ``Morew.QuadConic.CertifiedExpr.sum_nonpos family.nonpos? }
  else
    reject expression
      "expected affine terms, squared affine expressions, matrix quadratic forms, or their signed sums"

private meta def withFiniteInstances (instances : List Expr) (action : ReifyM ObjectiveResult) :
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

private meta def validateCertificateCore (source : Expr) (sense : Morew.ObjectiveSense)
    (certificate : Expr) : ReifyM ObjectiveResult := do
  for expression in #[source, certificate] do
    unless ← Evidence.complete expression do
      rejectIncomplete expression
  let .forallE _ domain codomain _ ← whnf (← inferType source)
    | reject source "expected a function on the decision space"
  if codomain.hasLooseBVars || !(← isDefEq codomain q(ℝ)) then
    reject source "expected a real-valued objective"
  let certificateName := match sense with
    | .minimize => ``Morew.QuadConic.CertifiedMin
    | .maximize => ``Morew.QuadConic.CertifiedMax
  let expected ← Affine.Space.withCanonicalSpaces #[domain] do
    mkAppM certificateName #[source]
  unless ← isDefEq (← inferType certificate) expected do
    reject certificate
      "certificate does not match the current objective, declared direction, and canonical vector spaces"
  checkWithKernel certificate
  let decomposition ← mkProjection certificate `toCertifiedExpr
  let quadratic ← instantiateMVars (← mkProjection decomposition `quadratic)
  let affine ← instantiateMVars (← mkProjection decomposition `affine)
  let pointwiseEquality ← instantiateMVars (← mkProjection decomposition `correct)
  let curvature ← instantiateMVars (← mkProjection certificate `curvature)
  let senseExpr := mkConst <| match sense with
    | .minimize => ``Morew.ObjectiveSense.minimize
    | .maximize => ``Morew.ObjectiveSense.maximize
  let expectedCurvature ← Affine.Space.withCanonicalSpaces #[domain] do
    mkAppM ``Morew.QuadConic.Curvature #[senseExpr, quadratic]
  unless ← isDefEq (← inferType curvature) expectedCurvature do
    reject certificate "curvature certificate does not match the quadratic part and objective sense"
  for expression in #[quadratic, affine, pointwiseEquality, curvature] do
    unless ← Evidence.complete expression do
      rejectIncomplete expression
    checkWithKernel expression
  return { quadratic, affine, pointwiseEquality, curvature }

private meta def completeCertificate (decomposition curvature : Expr)
    (sense : Morew.ObjectiveSense) : MetaM Expr :=
  mkAppM (match sense with
    | .minimize => ``Morew.QuadConic.CertifiedMin.mk
    | .maximize => ``Morew.QuadConic.CertifiedMax.mk) #[decomposition, curvature]

/-- Check the completed certificate for the current objective and declared optimization sense. -/
meta def validateObjectiveCertificate (presentation : Reformulation.PresentationState)
    (certificate : Expr) : MetaM (Except Expr.Error ObjectiveResult) :=
  State.withIsolatedMVars do
    try
      checkRealObjective presentation
      (validateCertificateCore presentation.objective presentation.sense certificate).run
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext m!"quadratic objective: {error.toMessageData}" }

/-- Validate assembled objective fields before using them in a quadratic conic form. -/
meta def validateObjectiveResult (presentation : Reformulation.PresentationState)
    (objective : ObjectiveResult) : MetaM (Except Expr.Error ObjectiveResult) :=
  State.withIsolatedMVars do
    try
      let certificate ← Affine.Space.withCanonicalSpaces #[presentation.domainType] do
        let decomposition ← mkAppM ``Morew.QuadConic.CertifiedExpr.mk
          #[objective.quadratic, objective.affine, objective.pointwiseEquality]
        completeCertificate decomposition objective.curvature presentation.sense
      validateObjectiveCertificate presentation certificate
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext m!"quadratic objective: {error.toMessageData}" }

private meta def reifyCore (source original : Expr) (sense : Morew.ObjectiveSense)
    (provider : Affine.EvidenceProvider) : ReifyM ObjectiveResult := do
  unless ← Evidence.complete original do
    rejectIncomplete original
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
      | .minimize => result.nonneg?
      | .maximize => result.nonpos?
    let some curvature := curvature? | do
      let sign := match sense with
        | .minimize => "nonnegative"
        | .maximize => "nonpositive"
      reject (result.missing?.getD original)
        m!"quadratic expression recognized, but {sign} quadratic curvature was not established; provide independent coefficient-sign or matrix positive-semidefiniteness evidence"
    let certificate ← Affine.Space.withCanonicalSpaces #[domain] do
      completeCertificate result.certificate curvature sense
    validateCertificateCore original sense certificate

/-- Prove an exact quadratic decomposition and the global sign required by the declared sense.
Try direct recognition before bounded unfolding of transparent helpers. -/
meta def reifyQuadratic (source : Expr) (sense : Morew.ObjectiveSense)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error ObjectiveResult) :=
  State.withIsolatedMVars do
    try
      let direct ← State.withIsolatedMVars <| (reifyCore source source sense provider).run
      if let .ok result := direct then return .ok result
      unless ← Expansion.enabled do return direct
      unless ← Evidence.complete source do return direct
      let expanded ← Expansion.prepare source
      if expanded.expansions == 0 then return direct
      (reifyCore expanded.expression source sense provider).run
    catch error =>
      return .error {
        expression := source
        reason := ← addMessageContext m!"quadratic objective: {error.toMessageData}" }

/-- Certify the typed presentation's objective using its declared optimization sense. -/
meta def reifyObjective (presentation : Reformulation.PresentationState)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error ObjectiveResult) :=
  State.withIsolatedMVars do
    try
      checkRealObjective presentation
      reifyQuadratic presentation.objective presentation.sense provider
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext m!"quadratic objective: {error.toMessageData}" }

end Morew.Elab.QuadConic
