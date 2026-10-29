/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic
import Morew.Elab.Rewrite.Plan
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Shared exact conic replacement planning

Adapt explicit representations, split ordered target rows, and certify each row.
Registered-rule selection and explicit certificates share these finishing checks.
-/

namespace Morew.Elab.Conic.Plan

open Lean Lean.Meta Qq
open Morew.Elab.Rewrite Morew.Elab.Rewrite.Plan

/-- A complete exact replacement, before presentation names are allocated. -/
structure Result extends Morew.Elab.Rewrite.Plan.Result where
  /-- Checked affine cone rows corresponding to `rowPredicates`. -/
  certifiedRows : Array RowResult

/-- Rebase all expressions of a checked replacement. -/
def Result.replaceFVars (result : Result) (oldVars newVars : Array Expr) : Result :=
  let replace := fun expression : Expr => expression.replaceFVars oldVars newVars
  { toResult := result.toResult.replaceFVars oldVars newVars
    certifiedRows := result.certifiedRows.map fun row => {
      constraint := replace row.constraint
      pointwiseIff := replace row.pointwiseIff } }

/-- Retry a failed certificate with safe finite evidence exposed by helpers.
Direct recognition keeps its original fast path; speculative declarations and
metavariables are discarded before retrying the unchanged source predicates. -/
def withHelperFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (sources : Array Expr)
    (action : MetaM (Except Expr.Error α)) :
    MetaM (Except Expr.Error α) := State.withIsolatedMVars do
  let failure (error : Exception) : MetaM (Except Expr.Error α) := do
    return Except.error ({
      expression := sources[0]?.getD (mkConst ``True)
      reason := ← addMessageContext error.toMessageData } : Expr.Error)
  try
    let replaceResult := fun result oldVars newVars =>
      result.map (fun value => replace value oldVars newVars)
    let direct ← State.withIsolatedMVars do
      try action catch error => failure error
    if let .ok result := direct then return .ok result
    let mut additional := #[]
    for source in sources do
      for inst in ← Affine.helperFiniteInstances source do
        unless additional.contains inst do
          additional := additional.push inst
    if additional.isEmpty then return direct
    withScopedFiniteInstances replaceResult additional.toList action
  catch error => failure error

/-- Retain finite-index evidence from the entire presentation while constructing
certificates. A row can carry the only explicit indexing instance needed by the
objective or another row. Duplicate proofs are scoped once, and all temporary
bindings are substituted through the completed result before leaving scope. -/
def withPresentationFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (presentation : Reformulation.PresentationState)
    (action : MetaM (Except Expr.Error α)) :
    MetaM (Except Expr.Error α) := do
  let mut instances := #[]
  let sources := #[presentation.objective] ++ presentation.constraints.map (·.predicate)
  for source in sources do
    for inst in ← Expr.sourceFiniteInstances source do
      unless instances.contains inst do
        instances := instances.push inst
  withHelperFiniteInstances replace sources do
    withScopedFiniteInstances
      (fun result oldVars newVars => result.map (fun value => replace value oldVars newVars))
      instances.toList action

/-- Retain source indexing evidence while constructing an exact lift. -/
def withFiniteInstances (instances : List Expr) (action : MetaM Result) :
    MetaM Result :=
  withScopedFiniteInstances Result.replaceFVars instances action

/-- Retain independent source lets while constructing an exact lift. -/
def withPredicateEvidence (point body : Expr)
    (action : MetaM Result) : MetaM Result :=
  withScopedEvidence Result.replaceFVars point body action

-- Adapters can leave another representation's target projection at the head.
-- Expose only these record fields, stopping before arbitrary predicate helpers
-- or arithmetic operands are unfolded.
/-- Reduce checked representation target fields without unfolding predicate helpers. -/
partial def exposeTarget (body : Expr) : MetaM Expr := do
  let body ← Expr.reduceStructure body (preserveLets := true)
  let head := body.getAppFn
  let prefixSize? := match head.constName? with
    | some ``Morew.ExactConstraintLift.target => some 3
    | some ``Morew.GraphRepresentation.target => some 4
    | some ``Morew.EpigraphRepresentation.target => some 5
    | some ``Morew.HypographRepresentation.target => some 5
    | _ => none
  if let some prefixSize := prefixSize? then
    let args := body.getAppArgs
    if args.size >= prefixSize then
      let partialTarget := mkAppN head (args.extract 0 prefixSize)
      let reduced ← whnf partialTarget
      unless reduced == partialTarget do
        return ← exposeTarget (mkAppN reduced (args.extract prefixSize args.size))
  return body

/-- Expose representation fields and split a checked replacement target. -/
def splitTarget (body : Expr) : MetaM (List Expr × Expr) :=
  Decomposition.split body fun body => do
    let body ← exposeTarget body
    -- Keep exact-lift diagnostics stable while sharing conjunction proof assembly.
    unless body.isLet || body.isConstOf ``True || body.isAppOfArity ``And 2 ||
        body.isForall || body.isAppOfArity ``Eq 3 || body.isAppOfArity ``LE.le 4 ||
        body.isAppOfArity ``GE.ge 4 || body.isAppOfArity ``Membership.mem 5 do
      throwError "unsupported exact target predicate {body}; expected True, conjunctions, affine equalities and non-strict inequalities, supported cone memberships, or a finite exponential or power membership family"
    return body

/-- Certify each replacement row without changing its presentation predicate. -/
def certifyRows (predicates : Array Expr) (provider : Affine.EvidenceProvider := {}) :
    MetaM (Array RowResult) := do
  predicates.mapM fun predicate => do
    match ← normalizeRow predicate provider with
    | .ok row => pure row
    | .error error => throwError "generated row: {error.reason}"

private def powerMembership (α : ℝ) (hα : 0 < α ∧ α < 1)
    (value : ℝ × ℝ × ℝ) : Prop :=
  value ∈ (Morew.Conic.Cone.power α hα).carrier

private theorem powerRangeOfEq {α β : ℝ} (h : α = β)
    (hα : 0 < α ∧ α < 1) : 0 < β ∧ β < 1 := h ▸ hα

private theorem powerMembershipCongr (α β : ℝ)
    (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (value : ℝ × ℝ × ℝ) (h : α = β) :
    powerMembership α hα value ↔ powerMembership β hβ value := by
  subst β
  rfl

-- Check operation instances separately from their operands: an altered
-- operation can agree with canonical arithmetic at a particular numeral.
private def sameOperationPrefix (source canonical : Expr) (operandCount : Nat) :
    MetaM Bool := do
  let sourceArgs := source.getAppArgs
  let canonicalArgs := canonical.getAppArgs
  unless source.getAppFn == canonical.getAppFn &&
      sourceArgs.size == canonicalArgs.size && operandCount ≤ sourceArgs.size do
    return false
  for index in [:sourceArgs.size - operandCount] do
    unless ← isDefEq sourceArgs[index]! canonicalArgs[index]! do return false
  return true

-- Only native extended-real numeral, inverse and quotient syntax can be
-- reduced inside `toReal`. Symbolic parameters and named operands stay intact.
private partial def literalENNReal (expression : Expr) : MetaM Bool := do
  let expression := expression.consumeMData
  let args := expression.getAppArgs
  if expression.isAppOfArity ``OfNat.ofNat 3 then
    unless args[1]!.isRawNatLit do return false
    let numeral : Q(ℕ) := args[1]!
    let ⟨canonical, _⟩ ← Mathlib.Meta.NormNum.mkOfNat (u := .zero)
      q(ENNReal) q(inferInstance) numeral
    return ← sameOperationPrefix expression canonical 0
  if expression.isAppOfArity ``Inv.inv 3 then
    let operand : Q(ENNReal) := args[2]!
    return (← sameOperationPrefix expression q($operand⁻¹) 1) &&
      (← literalENNReal operand)
  unless expression.isAppOfArity ``HDiv.hDiv 6 do return false
  let left : Q(ENNReal) := args[4]!
  let right : Q(ENNReal) := args[5]!
  return (← sameOperationPrefix expression q($left / $right) 2) &&
    (← literalENNReal left) && (← literalENNReal right)

-- Deliberately inspect syntax before invoking numerical evaluation. Named
-- constants, model-local definitions, and symbolic parameters retain their
-- identities even when their values happen to be rational.
private partial def literalRational (expression : Expr) : MetaM Bool := do
  let expression := expression.consumeMData
  let args := expression.getAppArgs
  if expression.isAppOfArity ``ENNReal.toReal 1 then
    return ← literalENNReal args[0]!
  if expression.isAppOfArity ``OfNat.ofNat 3 then
    unless args[1]!.isRawNatLit do return false
    let numeral : Q(ℕ) := args[1]!
    let ⟨canonical, _⟩ ← Mathlib.Meta.NormNum.mkOfNat (u := .zero)
      q(ℝ) q(inferInstance) numeral
    return ← sameOperationPrefix expression canonical 0
  if expression.isAppOfArity ``Neg.neg 3 || expression.isAppOfArity ``Inv.inv 3 then
    let operand : Q(ℝ) := args[2]!
    let canonical := if expression.isAppOfArity ``Neg.neg 3 then q(-$operand)
      else q($operand⁻¹)
    return (← sameOperationPrefix expression canonical 1) && (← literalRational operand)
  unless expression.isAppOfArity ``HAdd.hAdd 6 ||
      expression.isAppOfArity ``HSub.hSub 6 ||
      expression.isAppOfArity ``HMul.hMul 6 ||
      expression.isAppOfArity ``HDiv.hDiv 6 do return false
  let left : Q(ℝ) := args[4]!
  let right : Q(ℝ) := args[5]!
  let canonical := if expression.isAppOfArity ``HAdd.hAdd 6 then q($left + $right)
    else if expression.isAppOfArity ``HSub.hSub 6 then q($left - $right)
    else if expression.isAppOfArity ``HMul.hMul 6 then q($left * $right)
    else q($left / $right)
  return (← sameOperationPrefix expression canonical 2) &&
    (← literalRational left) && (← literalRational right)

private def normalizePowerMembership? (body : Expr) : MetaM (Option (Expr × Expr)) := do
  let expression := body.consumeMData
  unless expression.isAppOfArity ``Membership.mem 5 do return none
  let args := expression.getAppArgs
  let carrier := args[3]!.consumeMData
  unless carrier.isAppOfArity ``Morew.Conic.Cone.carrier 1 do return none
  let cone := carrier.getAppArgs[0]!.consumeMData
  unless cone.isAppOfArity ``Morew.Conic.Cone.power 2 do return none
  let result ← State.withIsolatedMVars (ε := Unit) do
    try
      let context ← readThe Core.Context
      let localLimit := (← IO.getNumHeartbeats) - context.initHeartbeats + 2_000_000
      let limit := if context.maxHeartbeats == 0 then localLimit
        else min context.maxHeartbeats localLimit
      withTheReader Core.Context (fun context => { context with maxHeartbeats := limit }) do
        let exponent : Q(ℝ) := cone.getAppArgs[0]!
        unless ← literalRational exponent do return .error ()
        let evidence := cone.getAppArgs[1]!
        let canonical := (mkAppN (← getConstInfo ``powerMembership).value!
          #[exponent, evidence, args[4]!]).headBeta
        unless (← isDefEq args[2]! canonical.getAppArgs[2]!) &&
            (← isDefEq body canonical) do return .error ()
        let normalized ← Evidence.normalizeToReal exponent
        let normalizedExponent : Q(ℝ) := normalized.expr
        let evaluated ← Mathlib.Meta.NormNum.Result.toSimpResult (u := .zero)
          (← Mathlib.Meta.NormNum.derive (u := .zero) normalizedExponent)
        if ← isDefEq exponent evaluated.expr then return .error ()
        let equality ← mkEqTrans (← normalized.getProof) (← evaluated.getProof)
        unless ← isDefEq (← inferType equality) (← mkEq exponent evaluated.expr) do
          return .error ()
        checkWithKernel equality
        let range ← mkAppM ``powerRangeOfEq #[equality, evidence]
        let normalized := (mkAppN (← getConstInfo ``powerMembership).value!
          #[evaluated.expr, range, args[4]!]).headBeta
        let proof ← mkAppM ``powerMembershipCongr
          #[exponent, evaluated.expr, evidence, range, args[4]!, equality]
        unless ← isDefEq (← inferType proof) (mkApp2 (mkConst ``Iff) body normalized) do
          return .error ()
        checkWithKernel proof
        return .ok (normalized, proof)
    catch _ => return .error ()
  return result.toOption

private partial def normalizeGeneratedPower? (body : Expr) :
    MetaM (Option (Expr × Expr)) := do
  if let .letE name type value rest nondep := body.consumeMData then
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let some (normalized, proof) ← normalizeGeneratedPower? (rest.instantiate1 binding)
        | return none
      return some (← mkLetFVars #[binding] normalized
        (usedLetOnly := false) (generalizeNondepLet := false),
        ← mkLetFVars #[binding] proof
        (usedLetOnly := false) (generalizeNondepLet := false))
  if let .forallE name type rest info := body.consumeMData then
    unless (← whnf type).isAppOfArity ``Fin 1 do return none
    return ← withLocalDecl name info type fun index => do
      let some (normalized, proof) ← normalizeGeneratedPower? (rest.instantiate1 index)
        | return none
      let normalized ← mkForallFVars #[index] normalized
      let proof ← mkAppM ``forall_congr' #[← mkLambdaFVars #[index] proof]
      unless ← isDefEq (← inferType proof) (mkApp2 (mkConst ``Iff) body normalized) do
        throwError "quantified power normalization changed its predicate"
      checkWithKernel proof
      return some (normalized, proof)
  normalizePowerMembership? body

private partial def conjunctionCongr (proofs : List Expr) : MetaM Expr := do
  match proofs with
  | [] => return mkApp (mkConst ``Iff.rfl) (mkConst ``True)
  | [proof] => return proof
  | proof :: rest => mkAppM ``and_congr #[proof, ← conjunctionCongr rest]

private def finishCore (source domain : Expr) (certificate : Certificate)
    (retained : Array Expr) (provider : Affine.EvidenceProvider) : MetaM Result := do
  certificate.check source retained
  let auxiliary ← whnf (← certificate.auxiliaryType)
  let noAuxiliary ← isDefEq auxiliary (mkConst ``Unit)
  let auxiliary? := if noAuxiliary then none else some auxiliary
  let nextDomain ← if noAuxiliary then pure domain else mkAppM ``Prod #[domain, auxiliary]
  unless ← Expr.isSupportedSpace nextDomain do
    throwError "unsupported exact-lift decision space {nextDomain}; expected real scalars, products, or finite function spaces"
  let targetFunction ← whnf (← certificate.targetFunction)
  let (rowPredicates, targetIff) ← withLocalDeclD `point nextDomain fun point => do
    let target := if noAuxiliary then mkApp2 targetFunction point (mkConst ``Unit.unit)
      else mkApp2 targetFunction (.proj ``Prod 0 point) (.proj ``Prod 1 point)
    let (originalBodies, splitProof) ← splitTarget target
    let mut bodies := []
    let mut proofs := []
    let mut changed := false
    for body in originalBodies do
      if let some (normalized, proof) ← normalizeGeneratedPower? body then
        bodies := normalized :: bodies
        proofs := proof :: proofs
        changed := true
      else
        bodies := body :: bodies
        proofs := mkApp (mkConst ``Iff.rfl) body :: proofs
    bodies := bodies.reverse
    let proof ← if changed then
        mkAppM ``Iff.trans #[splitProof, ← conjunctionCongr proofs.reverse]
      else pure splitProof
    let rows ← bodies.toArray.mapM fun body => mkLambdaFVars #[point] body
    return (rows, ← mkLambdaFVars #[point] proof)
  let prepared : Morew.Elab.Rewrite.Plan.Result := {
    certificate, auxiliary?, nextDomain, rowPredicates, targetIff }
  prepared.check source retained
  let certifiedRows ← certifyRows rowPredicates provider
  return { toResult := prepared, certifiedRows }

/-- Split and certify every row of an exact lift. -/
def finish (source domain : Expr) (certificate : Certificate)
    (retained : Array Expr) (provider : Affine.EvidenceProvider) : MetaM Result := do
  let target ← whnf (← certificate.targetFunction)
  let result ← withHelperFiniteInstances Result.replaceFVars #[target] do
    let result ← withFiniteInstances (← Expr.sourceFiniteInstances target).toList do
      finishCore source domain certificate retained provider
    return .ok result
  match result with
  | .ok result => return result
  | .error error => throwError error.reason

/-- Adapt an explicit record for the entire selected predicate and certify its rows.
Caller metavariables and the environment are restored on failure. -/
private def planDirect (sourcePredicate rule : Expr)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Result) :=
  State.withIsolatedMVars do
    try
      let source ← instantiateMVars sourcePredicate
      if ← unresolved source then throwError "unresolved metavariables in the selected predicate"
      let domain ← predicateDomain source
      let result ← withFiniteInstances (← Expr.sourceFiniteInstances source).toList do
        withLocalDeclD `point domain fun point =>
          withPredicateEvidence point (mkApp source point) do
            let lift ← customLift source domain rule
            finish source domain (.exact lift) #[] provider
      return .ok result
    catch error =>
      return .error {
        expression := sourcePredicate
        reason := ← addMessageContext error.toMessageData
      }

/-- Certify an explicit record, exposing finite evidence from helpers only if
the direct attempt fails. Adaptation always uses the original predicate. -/
def plan (sourcePredicate rule : Expr) (provider : Affine.EvidenceProvider := {}) :
    MetaM (Except Expr.Error Result) :=
  State.withIsolatedMVars do
    withHelperFiniteInstances Result.replaceFVars #[sourcePredicate]
      (planDirect sourcePredicate rule provider)

end Morew.Elab.Conic.Plan
