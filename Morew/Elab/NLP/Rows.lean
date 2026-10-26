/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Rows
import Morew.Elab.NLP.Domain

/-!
# Certification of generated smooth constraint rows

The caller supplies the exact proposed feasibility after checking its independent
exact-lift certificate. Only generated predicates are required to have smooth
residuals. Domain inclusion may use checked projections of any admitted retained
or generated row. Unsupported retained leaves stay opaque and supply no facts.
Symbolic finite rows remain grouped; their domains are finite intersections.
-/

namespace Morew.Elab.NLP.Rows

open Lean Lean.Meta Qq

/-- Checked common-domain evidence for exactly the generated predicates. -/
structure Result where
  /-- Common open evaluation domain. -/
  domain : Expr
  /-- Openness of the common domain. -/
  domainIsOpen : Expr
  /-- Inclusion of the exact proposed feasibility in the common domain. -/
  feasibleMemDomain : Expr
  /-- `Morew.NLP.Rows.Certified domain rows[i]`, in presentation order. -/
  rowCertificates : Array Expr

/-- Rebase every expression before the reformulation runner materializes a step. -/
def Result.replaceFVars (result : Result) (oldVars newVars : Array Expr) : Result := {
  domain := result.domain.replaceFVars oldVars newVars
  domainIsOpen := result.domainIsOpen.replaceFVars oldVars newVars
  feasibleMemDomain := result.feasibleMemDomain.replaceFVars oldVars newVars
  rowCertificates := result.rowCertificates.map (·.replaceFVars oldVars newVars)
}

private inductive Relation where
  | le | ge | eq

private def vectorRule : Relation → Name
  | .le => ``Morew.NLP.Rows.vector_le_iff
  | .ge => ``Morew.NLP.Rows.vector_ge_iff
  | .eq => ``Morew.NLP.Rows.vector_eq_iff

private def relation? (body : Expr) : Option (Relation × Expr × Expr × Expr) := do
  let args := body.getAppArgs
  if body.isAppOfArity ``Eq 3 then
    return (.eq, args[0]!, args[1]!, args[2]!)
  if body.isAppOfArity ``LE.le 4 then
    return (.le, args[0]!, args[2]!, args[3]!)
  if body.isAppOfArity ``GE.ge 4 then
    return (.ge, args[0]!, args[2]!, args[3]!)
  none

private def vectorSize? (type : Expr) : MetaM (Option Expr) := do
  let .forallE name index target info ← whnf type | return none
  let shape ← whnf index
  unless shape.isAppOfArity ``Fin 1 do return none
  withLocalDecl name info index fun i => do
    let target ← Core.betaReduce (← whnf (target.instantiate1 i))
    if target.containsFVar i.fvarId! then return none
    unless ← isDefEq target q(ℝ) do return none
    return some shape.getAppArgs[0]!

-- Check the relation instance before reducing a vector order into a quantifier.
private def canonicalRelation (body : Expr) (relation : Relation)
    (type lhs rhs : Expr) : MetaM Bool := do
  if let .eq := relation then return true
  let expected ← if ← isDefEq type q(ℝ) then do
      let lhs : Q(ℝ) := lhs
      let rhs : Q(ℝ) := rhs
      pure (match relation with | .ge => q($lhs ≥ $rhs) | _ => q($lhs ≤ $rhs) : Expr)
    else if (← vectorSize? type).isSome then do
      let proof ← mkAppM (vectorRule relation) #[lhs, rhs]
      pure (← inferType proof).getAppArgs[0]!
    else return false
  isDefEq body.getAppArgs[1]! expected.getAppArgs[1]!

private def structural (point body : Expr) : MetaM Expr :=
  Affine.reduceStructure body (opaqueProblemDependencies? := some point)

private def addUnique (values : Array Expr) (value : Expr) : Array Expr :=
  if values.contains value then values else values.push value

-- Inspect the typed membership head before reduction erases it. Both its
-- finite carrier and its native membership instance must match.
private def finiteMembership? (point proposition : Expr) : MetaM (Option Expr) := do
  let proposition ← structural point proposition
  unless proposition.isAppOfArity ``Membership.mem 5 do return none
  let args := proposition.getAppArgs
  unless (← whnf args[1]!).isAppOfArity ``Finset 1 do return none
  if (← Affine.depends point args[3]!) || (← Affine.depends point args[4]!) then return none
  let native ← mkAppOptM ``Finset.mem_def #[some args[0]!, some args[4]!, some args[3]!]
  let expected := (← inferType native).getAppArgs[0]!
  unless ← isDefEq args[2]! expected.getAppArgs[2]! do return none
  return some args[4]!

-- Indices come from the actual obligation or the active finite scopes. A finite
-- subtype also supplies its checked membership proof after reindexing a Finset.
private partial def collectIndices (point expression : Expr)
    (values facts : Array Expr) : MetaM (Array Expr × Array Expr) := do
  if values.size ≥ 64 then return (values, facts)
  let mut values := values
  let mut facts := facts
  unless expression.hasLooseBVars || expression.isSort || expression.isMVar do
    if !(← Affine.depends point expression) && (← Domain.Evidence.complete expression) then
      let type ← whnf (← inferType expression)
      if type.isAppOfArity ``Fin 1 then values := addUnique values expression
      if type.isAppOfArity ``Subtype 2 then
        let property ← mkAppM ``Subtype.property #[expression]
        -- Restrict extra subtype candidates to finite-set support evidence.
        if let some value ← finiteMembership? point (← inferType property) then
          values := addUnique (addUnique values expression) value
          facts := addUnique facts property
  match expression with
  | .app f a =>
    let (nextValues, nextFacts) ← collectIndices point f values facts
    collectIndices point a nextValues nextFacts
  | .mdata _ value | .proj _ _ value => collectIndices point value values facts
  | .letE _ type value body _ =>
    let (nextValues, nextFacts) ← collectIndices point type values facts
    let (nextValues, nextFacts) ← collectIndices point value nextValues nextFacts
    collectIndices point body nextValues nextFacts
  | _ => return (values, facts)

private def indexContext (point obligation : Expr) : MetaM (Array Expr × Array Expr) := do
  let mut values := #[]
  let mut facts := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    if ← Affine.depends point declaration.toExpr then continue
    unless ← Domain.Evidence.complete declaration.toExpr do continue
    if ← isProp declaration.type then
      facts := addUnique facts declaration.toExpr
      if let some value ← finiteMembership? point declaration.type then
        values := addUnique values value
    else
      let (nextValues, nextFacts) ← collectIndices point declaration.toExpr values facts
      values := nextValues
      facts := nextFacts
  collectIndices point obligation values facts

-- Independent parameter families may be applied to finite-support coordinates,
-- including the original index hidden beneath an equivFin reindexing.
private partial def specializeParameters (proof : Expr) (indices facts : Array Expr)
    (fuel : Nat) : MetaM (Array Expr) := do
  if fuel == 0 then return #[]
  let type ← whnf (← inferType proof)
  let .forallE _ argument _ _ := type | return #[proof]
  let choices := if ← isProp argument then facts else indices
  let mut result := #[]
  for choice in choices do
    if result.size ≥ 64 then break
    if ← isDefEq (← inferType choice) argument then
      result := result ++ (← specializeParameters (mkApp proof choice) indices facts (fuel - 1))
  return result

private partial def projectedFacts (point proof : Expr) (indices support : Array Expr)
    (fuel : Nat) : MetaM (Array Expr) := do
  if fuel == 0 then return #[]
  let type ← structural point (← inferType proof)
  let proof ← mkAppOptM ``id #[some type, some proof]
  if type.isAppOfArity ``And 2 then
    return (← projectedFacts point (← mkAppM ``And.left #[proof]) indices support fuel) ++
      (← projectedFacts point (← mkAppM ``And.right #[proof]) indices support fuel)
  if let some (relation, valueType, lhs, rhs) := relation? type then
    unless ← canonicalRelation type relation valueType lhs rhs do return #[]
    if ← isDefEq valueType q(ℝ) then return #[proof]
    if let some size ← vectorSize? valueType then
      let indexType ← mkAppM ``Fin #[size]
      let mut result := #[]
      for index in indices do
        if result.size ≥ 128 then break
        if ← isDefEq (← inferType index) indexType then
          let child ← match relation with
            | .eq => mkAppM ``congrFun #[proof, index]
            | _ => pure (mkApp proof index)
          result := result ++ (← projectedFacts point child indices support (fuel - 1))
      return result
    return #[]
  if let .forallE _ index rest _ := type then
    let indexShape ← whnf index
    let isFinite := indexShape.isAppOfArity ``Fin 1
    let isSupport := (← finiteMembership? point index).isSome
    if ← Affine.depends point index then return #[]
    let mut result := #[]
    for candidate in (if isSupport then support else indices) do
      if result.size ≥ 128 then break
      if ← isDefEq (← inferType candidate) index then
        unless isFinite || isSupport do
          -- An arbitrary ambient index is admitted only with an immediately
          -- following native finite-support premise, discharged in the next step.
          let .forallE _ premise _ _ ← structural point (rest.instantiate1 candidate)
            | continue
          unless (← finiteMembership? point premise).isSome do continue
        result := result ++ (← projectedFacts point (mkApp proof candidate)
          indices support (fuel - 1))
    return result
  return #[]

private def factsProvider : Domain.Evidence.FactsProvider := fun point feasibleProof obligation => do
  let (indices, support) ← indexContext point obligation
  let mut result ← projectedFacts point feasibleProof indices support 32
  for proof in support do
    result := result ++ (← specializeParameters proof indices support 4)
  for proof in result do
    unless ← Domain.Evidence.complete proof do throwError "incomplete projected row evidence"
    checkWithKernel proof
  return result

private structure RowCertificate where
  domain : Expr
  isOpen : Expr
  included : Expr
  proof : Expr

private structure Context where
  feasible : Expr
  decision : Expr
  source : Expr
  rowIndex : Nat
  unrestricted : Domain.DomainResult

private abbrev RowsM := ReaderT Context (ExceptT Domain.DomainError MetaM)

private def reject (expression : Expr) (reason : MessageData)
    (kind : Smooth.SmoothFailureKind := .unsupportedRow) : RowsM α := do
  let context ← read
  let type ← inferType expression
  throwThe Domain.DomainError {
    source := context.source, rowIndex? := some context.rowIndex
    expression, type, kind
    reason := ← addMessageContext
      m!"generated row {context.rowIndex}: at {expression} : {type}: {reason}"
  }

private def analytic (action : MetaM Expr) : RowsM Expr := do
  Space.withCanonicalSpaces #[(← read).decision] action

private def restrict (certificate : RowCertificate) (subset : Expr) : RowsM Expr :=
  analytic <| mkAppM ``Morew.NLP.Rows.Certified.mono #[certificate.proof, subset]

private def intersect (left right : RowCertificate) : RowsM (RowCertificate × Expr × Expr) := do
  let domain ← mkAppM ``Morew.NLP.Domain.inter #[left.domain, right.domain]
  let leftSubset ← mkAppM ``Morew.NLP.Domain.inter_left #[left.domain, right.domain]
  let rightSubset ← mkAppM ``Morew.NLP.Domain.inter_right #[left.domain, right.domain]
  let isOpen ← analytic <| mkAppM ``Morew.NLP.Domain.inter_open
    #[left.domain, right.domain, left.isOpen, right.isOpen]
  let included ← mkAppM ``Morew.NLP.Domain.inter_includes
    #[(← read).feasible, left.domain, right.domain, left.included, right.included]
  return (⟨domain, isOpen, included, left.proof⟩,
    ← restrict left leftSubset, ← restrict right rightSubset)

-- Keep independent proof lets in a projected predicate available while checking
-- its residuals, including when the binding is scoped to a finite-family index.
private def hoistProjectionLets : Expr → Expr
  | .proj name index value =>
    match hoistProjectionLets value with
    | .letE binding type value body nondep =>
      .letE binding type value (.proj name index body) nondep
    | value => .proj name index value
  | expression => expression

private partial def certifyBody (point body : Expr) : RowsM RowCertificate := do
  let body := hoistProjectionLets (← Affine.reduceStructure body (preserveLets := true)
    (opaqueProblemDependencies? := some point))
  if let .letE name type value rest nondep := body then
    if (← Affine.depends point type) || (← Affine.depends point value) then
      return ← certifyBody point (rest.instantiate1 value)
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← certifyBody point (rest.instantiate1 binding)
      return {
        domain := ← result.domain.replaceFVarsM #[binding] #[value]
        isOpen := ← result.isOpen.replaceFVarsM #[binding] #[value]
        included := ← result.included.replaceFVarsM #[binding] #[value]
        proof := ← result.proof.replaceFVarsM #[binding] #[value]
      }
  let body ← structural point body
  if body.isConstOf ``True then
    let base := (← read).unrestricted
    let proof ← analytic <| mkAppOptM ``Morew.NLP.Rows.Certified.truth
      #[some (← read).decision, none, none, some base.domain]
    return ⟨base.domain, base.domainIsOpen, base.feasibleMemDomain, proof⟩
  if body.isAppOfArity ``And 2 then
    let left ← certifyBody point body.getAppArgs[0]!
    let right ← certifyBody point body.getAppArgs[1]!
    let (info, left, right) ← intersect left right
    let proof ← analytic <| mkAppM ``Morew.NLP.Rows.Certified.and #[left, right]
    return { info with proof }
  if let some (relation, type, lhs, rhs) := relation? body then
    unless ← canonicalRelation body relation type lhs rhs do
      reject body "expected a canonical real or finite-vector order instance"
    if ← isDefEq type q(ℝ) then
      let lhs : Q(ℝ) := lhs
      let rhs : Q(ℝ) := rhs
      let residual ← mkLambdaFVars #[point] q($lhs - $rhs)
      let outcome ← Domain.certifyWithEvidence (← read).feasible #[residual] factsProvider
      let .ok result := outcome | do
        let .error error := outcome | unreachable!
        throwThe Domain.DomainError { error with
          source := (← read).source, sourceIndex? := none, rowIndex? := some (← read).rowIndex }
      let constructor := match relation with
        | .le => ``Morew.NLP.Rows.Certified.le
        | .ge => ``Morew.NLP.Rows.Certified.ge
        | .eq => ``Morew.NLP.Rows.Certified.eq
      let left ← mkLambdaFVars #[point] lhs
      let right ← mkLambdaFVars #[point] rhs
      let proof ← analytic <| mkAppM constructor #[left, right, result.smooth[0]!]
      return ⟨result.domain, result.domainIsOpen, result.feasibleMemDomain, proof⟩
    if let some size ← vectorSize? type then
      if ← Affine.depends point size then reject body "the vector dimension depends on a decision"
      let equivalent ← mkAppM (vectorRule relation) #[lhs, rhs]
      let expanded := (← inferType equivalent).getAppArgs[1]!
      let result ← certifyBody point expanded
      let p ← mkLambdaFVars #[point] body
      let q ← mkLambdaFVars #[point] expanded
      let equivalent ← mkLambdaFVars #[point] equivalent
      let proof ← analytic <| mkAppM ``Morew.NLP.Rows.Certified.of_iff
        #[p, q, equivalent, result.proof]
      return { result with proof }
    reject body "expected closed scalar or Fin n vector comparisons"
  if let .forallE name index rest info := body then
    let indexShape ← whnf index
    unless indexShape.isAppOfArity ``Fin 1 do
      reject body "generated families require an index of type Fin n"
    if ← Affine.depends point index then reject body "the family index type depends on a decision"
    let context ← read
    let outcome ← withLocalDecl name info index fun i => do
      ((do
        let child ← certifyBody point (rest.instantiate1 i)
        let predicate ← mkLambdaFVars #[point] (rest.instantiate1 i)
        return (← mkLambdaFVars #[i] child.domain,
          ← mkLambdaFVars #[i] child.isOpen,
          ← mkLambdaFVars #[i] child.included,
          ← mkLambdaFVars #[i] child.proof,
          ← mkLambdaFVars #[i] predicate) : RowsM _).run context).run
    let .ok (sets, opens, includes, proofs, predicates) := outcome | do
      let .error error := outcome | unreachable!
      throwThe Domain.DomainError error
    let domain ← mkAppM ``Morew.NLP.Domain.family #[sets]
    let isOpen ← analytic <| mkAppM ``Morew.NLP.Domain.family_open #[sets, opens]
    let included ← mkAppM ``Morew.NLP.Domain.family_includes
      #[(← read).feasible, sets, includes]
    let proofs ← withLocalDecl name info index fun i => do
      let subset ← mkAppM ``Morew.NLP.Domain.family_subset #[sets, i]
      let proof ← Space.withCanonicalSpaces #[context.decision] <|
        mkAppM ``Morew.NLP.Rows.Certified.mono #[mkApp proofs i, subset]
      mkLambdaFVars #[i] proof
    let proof ← analytic <| mkAppM ``Morew.NLP.Rows.Certified.family #[predicates, proofs]
    return ⟨domain, isOpen, included, proof⟩
  reject body "expected True, conjunctions, closed real comparisons, or finite families"

private def certifyCore (feasible : Expr) (rows : Array Expr) :
    MetaM (Except Domain.DomainError Result) := do
  let outcome ← Domain.certifyWithEvidence feasible #[] factsProvider
  let .ok base := outcome | do
    let .error error := outcome | unreachable!
    return .error error
  let .forallE _ decision _ _ ← whnf (← inferType feasible)
    | throwError "expected a feasibility predicate"
  let mut result : Result := ⟨base.domain, base.domainIsOpen, base.feasibleMemDomain, #[]⟩
  for index in [:rows.size] do
    let row := rows[index]!
    unless ← Domain.Evidence.complete row do
      return .error {
        source := row, rowIndex? := some index, expression := row, type := ← inferType row
        kind := .unresolved, reason := ← addMessageContext m!"generated row {index} is incomplete"
      }
    unless ← isDefEq (← inferType row) (← mkArrow decision q(Prop)) do
      throwError "generated row {index} does not have type {decision} → Prop"
    let context : Context := ⟨feasible, decision, row, index, base⟩
    let outcome ← withLocalDeclD `point decision fun point =>
      ((certifyBody point (mkApp row point)).run context).run
    let .ok child := outcome | do
      let .error error := outcome | unreachable!
      return .error error
    let domain ← mkAppM ``Morew.NLP.Domain.inter #[result.domain, child.domain]
    let left ← mkAppM ``Morew.NLP.Domain.inter_left #[result.domain, child.domain]
    let right ← mkAppM ``Morew.NLP.Domain.inter_right #[result.domain, child.domain]
    let proofs ← result.rowCertificates.mapM fun proof =>
      Space.withCanonicalSpaces #[decision] <|
        mkAppM ``Morew.NLP.Rows.Certified.mono #[proof, left]
    let proof ← Space.withCanonicalSpaces #[decision] <|
      mkAppM ``Morew.NLP.Rows.Certified.mono #[child.proof, right]
    result := {
      domain
      domainIsOpen := ← Space.withCanonicalSpaces #[decision] <|
        mkAppM ``Morew.NLP.Domain.inter_open
          #[result.domain, child.domain, result.domainIsOpen, child.isOpen]
      feasibleMemDomain := ← mkAppM ``Morew.NLP.Domain.inter_includes
        #[feasible, result.domain, child.domain, result.feasibleMemDomain, child.included]
      rowCertificates := proofs.push proof
    }
  let expectedOpen ← Space.withCanonicalSpaces #[decision] <|
    mkAppM ``IsOpen #[result.domain]
  unless ← isDefEq (← inferType result.domainIsOpen) expectedOpen do
    throwError "generated-row domain certificate changed the open set"
  let expectedInclusion ← withLocalDeclD `point decision fun point => do
    let membership ← mkAppM ``Membership.mem #[result.domain, point]
    mkForallFVars #[point] (← mkArrow (mkApp feasible point) membership)
  unless ← isDefEq (← inferType result.feasibleMemDomain) expectedInclusion do
    throwError "generated-row domain certificate changed proposed feasibility"
  for i in [:rows.size] do
    let expected ← Space.withCanonicalSpaces #[decision] <|
      mkAppM ``Morew.NLP.Rows.Certified #[result.domain, rows[i]!]
    unless ← isDefEq (← inferType result.rowCertificates[i]!) expected do
      throwError "generated-row certificate changed row {i} or its common domain"
    let proof ← mkAppOptM ``id #[some expected, some result.rowCertificates[i]!]
    result := { result with rowCertificates := result.rowCertificates.set! i proof }
  for proof in result.rowCertificates ++ #[result.domainIsOpen, result.feasibleMemDomain] do
    unless ← Domain.Evidence.complete proof do throwError "incomplete generated-row certificate"
    checkWithKernel proof
  return .ok result

/-- Certify precisely the supplied generated rows using checked evidence from the
exact proposed feasibility. The caller first checks its unconditional exact lift.
Unsupported retained leaves contribute no facts. Public `Domain.certify` keeps
its stricter whole-predicate grammar. Caller state is restored on every outcome. -/
def certifyRows (feasible : Expr) (rows : Array Expr) :
    MetaM (Except Domain.DomainError Result) :=
  Affine.withIsolatedMVars do
    try
      certifyCore feasible rows
    catch exception =>
      return .error {
        source := feasible, expression := feasible, type := ← inferType feasible
        kind := .invalidInstance, reason := ← addMessageContext exception.toMessageData
      }

end Morew.Elab.NLP.Rows
