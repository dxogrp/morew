/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Affine
import Morew.Affine.Matrix
import Morew.Affine.SymmetricMatrix
import Morew.Elab.Expr
import Morew.Elab.Affine.Space
import Morew.Elab.State
import Morew.Elab.Affine.Expansion
import Morew.Core
import Mathlib.Tactic.NormNum
import Lean.Meta.Check
import Lean.Meta.Match.MatcherInfo

/-! Construct affine maps and prove pointwise agreement with the source expressions.

Transparent, nonrecursive `def` and `abbrev` helpers expand for certification;
source expressions and printing retain their names.

Expansion limits apply per source expression, including evidence discovery:
* `morew.affine.maxExpansionDepth`: 32 nested expansions.
* `morew.affine.maxExpansionSteps`: 1024 unfoldings across branches.
* `morew.affine.maxExpansionNodes`: 100000 expanded nodes, including duplication.

A zero limit leaves only direct recognition. Opaque, irreducible, and recursive
helpers and custom predicates remain unexpanded. Standard operations require canonical
instances and domain evidence. -/

namespace Morew.Elab.Affine

open Lean Lean.Meta Qq

/-- Optional nonzero evidence for division. -/
structure EvidenceProvider where
  /-- Supply a proof of `c ≠ 0`. The certifier checks its type, independence, and completeness.
Returning `none` allows bounded numeral/rational evaluation. -/
  nonzeroEvidence? : Option (Expr → MetaM (Option Expr)) := none

/-- A real affine map and its pointwise agreement with the supplied function. -/
structure AffineResult where
  /-- An expression of type `X →ᵃ[ℝ] Y`. -/
  map : Expr
  /-- A proof of `∀ x, map x = source x`. -/
  pointwiseEquality : Expr

private abbrev ReifyM := ExceptT Expr.Error MetaM

private def reject (expression : Expr) (reason : MessageData) : ReifyM α := do
  throwThe Expr.Error {
    expression
    reason := ← addMessageContext
      m!"cannot certify affine expression {expression}: {reason}"
  }

/-- Discover finite-index evidence in transparent helpers after direct certification fails. -/
def helperFiniteInstances (source : Expr) : MetaM (Array Expr) := do
  unless ← Expansion.enabled do return #[]
  let prepared ← Expansion.prepare source
    (fun expression preserve => Expr.reduceStructure expression preserve)
  if prepared.expansions == 0 then return #[]
  let original ← Expr.sourceFiniteInstances source
  return (← Expr.sourceFiniteInstances prepared.expression).filter (!original.contains ·)

private def withFiniteInstances (instances : List Expr) (action : ReifyM Expr) :
    ReifyM Expr := do
  match instances with
  | [] => action
  | inst :: rest =>
    mapLetDeclZeta `_sourceFinite (← inferType inst) inst fun _ =>
      withFiniteInstances rest action

private def functionOf (point body : Expr) : MetaM Expr :=
  mkLambdaFVars #[point] body

private partial def hasPlaceholders (expression : Expr) (seen : FVarIdSet := {}) :
    MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasSorry then return true
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    unless seen.contains id do
      seen := seen.insert id
      let declaration ← id.getDecl
      if ← hasPlaceholders declaration.type seen then return true
      if let some value := declaration.value? (allowNondep := true) then
        if ← hasPlaceholders value seen then return true
  return false

private def certifiedFunction (certificate : Expr) : MetaM Expr := do
  let type ← instantiateMVars (← inferType certificate)
  unless type.isAppOf ``Morew.Affine.Certified do
    throwError "internal affine constructor returned an unexpected type"
  return type.getAppArgs.back!

-- Check operation instances independently of their operands.
private def checkPrefix (source expected : Expr) (operandCount : Nat) : ReifyM Unit := do
  let source := source.consumeMData
  let expected ← Expr.reduceStructure expected
  let sourceArgs := source.getAppArgs
  let expectedArgs := expected.getAppArgs
  unless source.getAppFn == expected.getAppFn &&
      sourceArgs.size == expectedArgs.size && operandCount ≤ sourceArgs.size do
    reject source "unsupported operation or arithmetic instance"
  let prefixSize := sourceArgs.size - operandCount
  for i in [:prefixSize] do
    unless ← isDefEq sourceArgs[i]! expectedArgs[i]! do
      reject source "unsupported arithmetic instance; expected the canonical real operation"

private def finish (point source certificate : Expr)
    (operandCount? : Option Nat := none) : ReifyM Expr := do
  let function ← certifiedFunction certificate
  if let some count := operandCount? then
    checkPrefix source (function.beta #[point]) count
  unless ← isDefEq function (← functionOf point source) do
    reject source "the supported affine construction does not match this typed expression"
  return certificate

private def withIndexInstance (point inst : Expr) (action : ReifyM Expr) : ReifyM Expr := do
  if ← Expr.depends point inst then
    reject inst "the finite indexing instance depends on an optimization variable"
  mapLetDeclZeta `_affineIndex (← inferType inst) inst fun _ => action

-- Expose finite enumeration through `HMul` instance aliases, then check the canonical prefix.
private partial def matrixIndexInstance? (instanceExpr : Expr) (fuel : Nat := 32) :
    MetaM (Option Expr) := do
  if fuel == 0 then return none
  let instanceExpr ← Expr.reduceStructure instanceExpr
  if instanceExpr.isAppOfArity ``Matrix.instHMulOfFintypeOfMulOfAddCommMonoid 7 then
    return some instanceExpr.getAppArgs[4]!
  -- Square multiplication can arrive through the ordinary `Mul`-to-`HMul` bridge.
  if instanceExpr.isAppOfArity ``instHMul 2 then
    return ← matrixIndexInstance? instanceExpr.getAppArgs[1]! (fuel - 1)
  if instanceExpr.isAppOfArity ``Matrix.instMulOfFintypeOfAddCommMonoid 5 then
    return some instanceExpr.getAppArgs[2]!
  if let some expanded ← unfoldDefinition? instanceExpr then
    return ← matrixIndexInstance? expanded (fuel - 1)
  return none

private def construct (point source : Expr) (name : Name) (args : Array Expr)
    (operandCount? : Option Nat := none) : ReifyM Expr := do
  let certificate ← try
    let spaces := #[← inferType point, ← inferType source]
    Space.withCanonicalSpaces spaces do
      let mut term ← mkAppM name args
      repeat
        let type ← whnf (← inferType term)
        if let .forallE _ domain _ .instImplicit := type then
          term := mkApp term (← synthInstance domain)
        else break
      pure term
  catch exception =>
    reject source m!"unsupported types or instances: {exception.toMessageData}"
  finish point source certificate operandCount?

private def nonzeroProof (point divisor : Expr) (provider : EvidenceProvider) : ReifyM Expr := do
  if ← Expr.depends point divisor then
    reject divisor "the divisor depends on an optimization variable"
  let zero : Expr := q((0 : ℝ))
  let obligation ← mkAppM ``Ne #[divisor, zero]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if ← isDefEq declaration.type obligation then
        let (dependent, unresolved) ← Expr.inspectLocals declaration.toExpr (some point.fvarId!)
        if dependent then
          reject divisor "nonzero evidence depends on the decision point"
        if unresolved then
          reject divisor "nonzero evidence contains unresolved metavariables"
        return declaration.toExpr
  if let some provide := provider.nonzeroEvidence? then
    if let some proof ← provide obligation then
      unless ← isDefEq (← inferType proof) obligation do
        reject divisor "supplied evidence does not prove that the divisor is nonzero"
      let (dependent, unresolved) ← Expr.inspectLocals proof (some point.fvarId!)
      if dependent then
        reject divisor "nonzero evidence depends on the decision point"
      if unresolved then
        reject divisor "nonzero evidence contains unresolved metavariables"
      return proof
  try
    -- Bound numeral/rational evidence search, preserving any tighter caller limit and heartbeat origin.
    let context ← readThe Core.Context
    let localLimit := (← IO.getNumHeartbeats) - context.initHeartbeats + 2_000_000
    let limit := if context.maxHeartbeats == 0 then localLimit
      else min context.maxHeartbeats localLimit
    let result ← withTheReader Core.Context
      (fun context => { context with maxHeartbeats := limit }) <|
      Mathlib.Meta.NormNum.deriveBool obligation
    match result with
    | ⟨true, proof⟩ => return proof
    | ⟨false, _⟩ => pure ()
  catch _ => pure ()
  reject divisor m!"missing nonzero evidence; required {obligation}"

private partial def reifyBody (point expression : Expr) (provider : EvidenceProvider) : ReifyM Expr := do
  let expression ← Expr.reduceStructure expression (preserveLets := true)
  if let .letE name type value body nondep := expression then
    -- Substitute decision-dependent aliases before abstraction; retain independent proof and instance lets.
    if (← Expr.depends point type) || (← Expr.depends point value) then
      return ← reifyBody point (body.instantiate1 value) provider
    return ← mapLetDeclZeta name type value (nondep := nondep) fun binding =>
      reifyBody point (body.instantiate1 binding) provider
  let type ← inferType expression
  unless ← Expr.isSupportedSpace type do
    reject expression m!"unsupported affine value type {type}"
  let domain ← inferType point
  if !(← Expr.depends point expression) then
    return ← construct point expression ``Morew.Affine.Certified.const #[domain, expression]
  if expression == point then
    return ← construct point expression ``Morew.Affine.Certified.id #[domain]
  if let .proj ``Subtype 0 value := expression then
    if (← Expr.symmetricMatrixDimension? (← inferType value)).isSome then
      let value ← reifyBody point value provider
      return ← construct point expression ``Morew.Affine.Certified.fromSymmetricMatrix #[value]
  if let .proj ``WithLp 0 value := expression then
    if (← Expr.euclideanDimension? (← inferType value)).isSome then
      let value ← reifyBody point value provider
      return ← construct point expression ``Morew.Affine.Certified.ofEuclidean #[value]
  if let .proj ``Prod index value := expression then
    let value ← reifyBody point value provider
    let constructor := if index == 0 then
      ``Morew.Affine.Certified.fst else ``Morew.Affine.Certified.snd
    return ← construct point expression constructor #[value]
  if let .lam name index body info := expression then
    let family ← withLocalDecl name info index fun i => do
      let certificate ← reifyBody point (body.instantiate1 i) provider
      mkLambdaFVars #[i] certificate
    return ← construct point expression ``Morew.Affine.Certified.pi #[family]
  let head := expression.getAppFn
  let args := expression.getAppArgs
  let name := head.constName?
  if name == some ``Morew.Conic.SymmetricMatrix.toMatrix && args.size == 2 then
    let value ← reifyBody point args[1]! provider
    return ← construct point expression ``Morew.Affine.Certified.fromSymmetricMatrix #[value] (some 1)
  if name == some ``Subtype.val && args.size == 3 then
    if (← Expr.symmetricMatrixDimension? (← inferType args[2]!)).isSome then
      let value ← reifyBody point args[2]! provider
      return ← construct point expression ``Morew.Affine.Certified.fromSymmetricMatrix #[value]
  if name == some ``Morew.Conic.SymmetricMatrix.ofMatrix && args.size == 3 then
    let value ← reifyBody point args[1]! provider
    let proof ← mkLambdaFVars #[point] args[2]!
    if (← Expr.hasUnresolved proof) || (← hasPlaceholders proof) then
      reject args[2]! "the symmetry proof contains unresolved metavariables or placeholders"
    return ← construct point expression ``Morew.Affine.Certified.toSymmetricMatrix #[value, proof]
  if name == some ``Morew.Conic.fromBlocksFin && args.size == 6 then
    let mut blocks := #[]
    for block in args[2:] do
      blocks := blocks.push (← reifyBody point block provider)
    return ← construct point expression ``Morew.Affine.Certified.fromBlocksFin blocks (some 4)
  if name == some ``DFunLike.coe && args.size == 6 then
    let operation ← Expr.reduceStructure args[4]!
    if operation.isAppOfArity ``Matrix.of 3 then
      let value ← reifyBody point args[5]! provider
      return ← construct point expression ``Morew.Affine.Certified.matrixOf #[value] (some 1)
    if operation.isAppOfArity ``Matrix.reindex 7 then
      let opArgs := operation.getAppArgs
      for index in #[opArgs[5]!, opArgs[6]!] do
        if ← Expr.depends point index then
          reject index "the matrix reindexing depends on an optimization variable"
      let value ← reifyBody point args[5]! provider
      return ← construct point expression ``Morew.Affine.Certified.reindex
        #[opArgs[5]!, opArgs[6]!, value] (some 1)
  if name == some ``Matrix.transpose && args.size == 4 then
    let value ← reifyBody point args[3]! provider
    return ← construct point expression ``Morew.Affine.Certified.transpose #[value] (some 1)
  if name == some ``Matrix.diagonal && args.size == 5 then
    return ← withIndexInstance point args[2]! do
      let value ← reifyBody point args[4]! provider
      return ← construct point expression ``Morew.Affine.Certified.diagonal #[value] (some 1)
  if name == some ``Matrix.trace && args.size == 5 then
    return ← withIndexInstance point args[2]! do
      let value ← reifyBody point args[4]! provider
      return ← construct point expression ``Morew.Affine.Certified.trace #[value] (some 1)
  if name == some ``Morew.Conic.lowerTriangularMatrix && args.size == 2 then
    let value ← reifyBody point args[1]! provider
    return ← construct point expression ``Morew.Affine.Certified.lowerTriangularMatrix
      #[value] (some 1)
  if name == some ``Matrix.submatrix && args.size == 8 then
    for index in #[args[6]!, args[7]!] do
      if ← Expr.depends point index then
        reject index "the matrix index map depends on an optimization variable"
    let value ← reifyBody point args[5]! provider
    return ← construct point expression ``Morew.Affine.Certified.submatrix
      #[value, args[6]!, args[7]!] (some 3)
  if name == some ``Matrix.fromBlocks && args.size == 9 then
    let mut blocks := #[]
    for block in args[5:] do
      blocks := blocks.push (← reifyBody point block provider)
    return ← construct point expression ``Morew.Affine.Certified.fromBlocks blocks (some 4)
  if name == some ``WithLp.toLp && args.size == 3 then
    if (← Expr.euclideanDimension? type).isSome then
      let value ← reifyBody point args[2]! provider
      return ← construct point expression ``Morew.Affine.Certified.toEuclidean #[value]
  if name == some ``WithLp.ofLp && args.size == 3 then
    if (← Expr.euclideanDimension? (← inferType args[2]!)).isSome then
      let value ← reifyBody point args[2]! provider
      return ← construct point expression ``Morew.Affine.Certified.ofEuclidean #[value]
  if name == some ``HAdd.hAdd && args.size == 6 then
    let left ← reifyBody point args[4]! provider
    let right ← reifyBody point args[5]! provider
    return ← construct point expression ``Morew.Affine.Certified.add #[left, right] (some 2)
  if name == some ``HSub.hSub && args.size == 6 then
    let left ← reifyBody point args[4]! provider
    let right ← reifyBody point args[5]! provider
    return ← construct point expression ``Morew.Affine.Certified.sub #[left, right] (some 2)
  if name == some ``Neg.neg && args.size == 3 then
    let value ← reifyBody point args[2]! provider
    return ← construct point expression ``Morew.Affine.Certified.neg #[value] (some 1)
  if name == some ``HMul.hMul && args.size == 6 then
    let left := args[4]!
    let right := args[5]!
    if let some index ← matrixIndexInstance? args[3]! then
      return ← withIndexInstance point index do
        if !(← Expr.depends point left) then
          let rightMap ← reifyBody point right provider
          return ← construct point expression ``Morew.Affine.Certified.matrixMulConstLeft
            #[left, rightMap] (some 2)
        if !(← Expr.depends point right) then
          let leftMap ← reifyBody point left provider
          return ← construct point expression ``Morew.Affine.Certified.matrixMulConstRight
            #[leftMap, right] (some 2)
        discard <| reifyBody point left provider
        discard <| reifyBody point right provider
        reject expression "both matrix factors of multiplication depend on optimization variables"
    if !(← Expr.depends point left) then
      let rightMap ← reifyBody point right provider
      return ← construct point expression ``Morew.Affine.Certified.mulConstLeft
        #[left, rightMap] (some 2)
    if !(← Expr.depends point right) then
      let leftMap ← reifyBody point left provider
      return ← construct point expression ``Morew.Affine.Certified.mulConstRight
        #[leftMap, right] (some 2)
    discard <| reifyBody point left provider
    discard <| reifyBody point right provider
    reject expression "both factors of multiplication depend on optimization variables"
  if name == some ``HSMul.hSMul && args.size == 6 then
    let coefficient := args[4]!
    if ← Expr.depends point coefficient then
      if !(← Expr.depends point args[5]!) &&
          (← isDefEq (← inferType coefficient) (mkConst ``Real)) then
        let scalar ← reifyBody point coefficient provider
        return ← construct point expression ``Morew.Affine.Certified.smulConst
          #[scalar, args[5]!] (some 2)
      reject coefficient "the scalar coefficient depends on an optimization variable"
    let value ← reifyBody point args[5]! provider
    let scalarType ← inferType coefficient
    let constructor ← if ← isDefEq scalarType (mkConst ``Real) then
        pure ``Morew.Affine.Certified.realSMul
      else if ← isDefEq scalarType (mkConst ``Nat) then
        pure ``Morew.Affine.Certified.natSMul
      else reject coefficient "only real and natural scalar coefficients are supported"
    return ← construct point expression constructor #[coefficient, value] (some 2)
  if name == some ``HDiv.hDiv && args.size == 6 then
    let numerator ← reifyBody point args[4]! provider
    let proof ← nonzeroProof point args[5]! provider
    return ← construct point expression ``Morew.Affine.Certified.divConst
      #[numerator, args[5]!, proof] (some 2)
  if name == some ``Real.rpow && args.size == 2 then
    let exponent ← Expr.reduceStructure args[1]!
    unless ← Expr.depends point exponent do
      if ← isDefEq exponent q((0 : ℝ)) then
        let source ← functionOf point args[0]!
        return ← construct point expression ``Morew.Affine.Certified.rpowZeroSource
          #[source] (some 2)
      if ← isDefEq exponent q((1 : ℝ)) then
        let base ← reifyBody point args[0]! provider
        return ← construct point expression ``Morew.Affine.Certified.rpowOne #[base] (some 2)
    reject expression "a decision-dependent real power is supported only with exponent 0 or 1"
  if name == some ``HPow.hPow && args.size == 6 then
    let exponent ← Expr.reduceStructure args[5]!
    if ← isDefEq (← inferType exponent) q(ℝ) then
      unless ← Expr.depends point exponent do
        if ← isDefEq exponent q((0 : ℝ)) then
          let source ← functionOf point args[4]!
          return ← construct point expression ``Morew.Affine.Certified.rpowNotationZeroSource
            #[source] (some 2)
        if ← isDefEq exponent q((1 : ℝ)) then
          let base ← reifyBody point args[4]! provider
          return ← construct point expression ``Morew.Affine.Certified.rpowNotationOne #[base] (some 2)
      reject expression "a decision-dependent real power is supported only with exponent 0 or 1"
    if ← isDefEq (← inferType exponent) (mkConst ``Nat) then
      if (← getNatValue? exponent) == some 0 then
        let source ← functionOf point args[4]!
        return ← construct point expression ``Morew.Affine.Certified.powZeroSource
          #[source] (some 2)
      if (← getNatValue? exponent) == some 1 then
        let base ← reifyBody point args[4]! provider
        return ← construct point expression ``Morew.Affine.Certified.powOne #[base] (some 2)
    reject expression "a decision-dependent power is supported only with natural exponent 0 or 1"
  if name == some ``Prod.mk && args.size == 4 then
    let left ← reifyBody point args[2]! provider
    let right ← reifyBody point args[3]! provider
    return ← construct point expression ``Morew.Affine.Certified.pair #[left, right]
  if name == some ``Matrix.vecCons && args.size == 4 then
    let first ← reifyBody point args[2]! provider
    let rest ← reifyBody point args[3]! provider
    return ← construct point expression ``Morew.Affine.Certified.vecCons #[first, rest]
  if name == some ``Finset.sum && args.size == 5 then
    let set := args[3]!
    if ← Expr.depends point set then
      reject set "the finite sum's index set depends on an optimization variable"
    let family ← withLocalDeclD `i args[0]! fun i => do
      let certificate ← reifyBody point (mkApp args[4]! i) provider
      mkLambdaFVars #[i] certificate
    return ← construct point expression ``Morew.Affine.Certified.sum #[set, family] (some 2)
  if name == some ``dotProduct && args.size == 7 then
    return ← withIndexInstance point args[2]! do
      let left := args[5]!
      let right := args[6]!
      if !(← Expr.depends point left) then
        let rightMap ← reifyBody point right provider
        return ← construct point expression ``Morew.Affine.Certified.dotConstLeft
          #[left, rightMap] (some 2)
      if !(← Expr.depends point right) then
        let leftMap ← reifyBody point left provider
        return ← construct point expression ``Morew.Affine.Certified.dotConstRight
          #[leftMap, right] (some 2)
      discard <| reifyBody point left provider
      discard <| reifyBody point right provider
      reject expression "both dot-product factors depend on optimization variables"
  if (name == some ``Matrix.mulVec || name == some ``Matrix.vecMul) && args.size == 7 then
    return ← withIndexInstance point args[4]! do
      let matrix := if name == some ``Matrix.mulVec then args[5]! else args[6]!
      let vector := if name == some ``Matrix.mulVec then args[6]! else args[5]!
      if ← Expr.depends point matrix then
        -- Diagnose an unsupported entry first, then the coefficient's dependence.
        discard <| reifyBody point matrix provider
        reject matrix "the coefficient matrix depends on an optimization variable"
      let vectorMap ← reifyBody point vector provider
      if name == some ``Matrix.mulVec then
        return ← construct point expression ``Morew.Affine.Certified.mulVec
          #[matrix, vectorMap] (some 2)
      return ← construct point expression ``Morew.Affine.Certified.vecMul
        #[vectorMap, matrix] (some 2)
  -- Recognize fixed vector indices after operation heads.
  if let .app vector index := expression then
    let vectorType ← whnf (← inferType vector)
    if vectorType.isForall && (← Expr.isSupportedSpace vectorType) then
      if ← Expr.depends point index then
        reject index "the vector index depends on an optimization variable"
      let vectorMap ← reifyBody point vector provider
      return ← construct point expression ``Morew.Affine.Certified.eval #[vectorMap, index]
  -- Prefer a failing inner operand to its enclosing unsupported application.
  for argument in args do
    if (← Expr.depends point argument) && (← Expr.isSupportedSpace (← inferType argument)) then
      discard <| reifyBody point argument provider
  reject expression "unsupported function, coercion, or nonlinear operation"

private def reifyCore (source : Expr) (provider : EvidenceProvider)
    (original? : Option Expr := none) : ReifyM AffineResult := do
  let source ← instantiateMVars source
  if (← Expr.inspectLocals source none).2 then
    reject source "unresolved metavariables are not supported"
  if ← hasPlaceholders source then
    reject source "proof placeholders are not supported"
  let type ← whnf (← inferType source)
  let .forallE _ domain codomain _ := type
    | reject source "expected a function from a decision space"
  if codomain.hasLooseBVars then
    reject source "dependent result types are not supported"
  let original := original?.getD source
  let instances ← Expr.sourceFiniteInstances source
  let originalInstances ← if original?.isSome then Expr.sourceFiniteInstances original else pure #[]
  let certificate ← withFiniteInstances (instances ++ originalInstances).toList do
    unless ← Expr.isSupportedSpace domain do
      reject source m!"unsupported decision space {domain}"
    withLocalDeclD `point domain fun point => do
      reifyBody point (mkApp source point) provider
  let map ← mkProjection certificate `map
  let equality ← mkProjection certificate `correct
  let map ← instantiateMVars map
  let equality ← instantiateMVars equality
  if map.hasMVar || equality.hasMVar then
    reject source "affine construction left unresolved metavariables"
  let expected ← withLocalDeclD `point domain fun point => do
    let value := mkApp (← mkProjection map `toFun) point
    mkForallFVars #[point] (← mkEq value (mkApp original point))
  unless ← isDefEq (← inferType equality) expected do
    reject source "affine certificate does not establish equality to the original function"
  checkWithKernel map
  checkWithKernel equality
  return { map, pointwiseEquality := equality }

/-- Construct an affine map for a typed function in an isolated metavariable context.
Try direct recognition before bounded helper expansion. Nonzero evidence uses local
hypotheses, then the optional provider, then bounded numeral/rational evaluation. -/
def reifyAffine (source : Expr) (provider : EvidenceProvider := {}) :
    MetaM (Except Expr.Error AffineResult) := State.withIsolatedMVars do
  try
    let direct ← State.withIsolatedMVars <| (reifyCore source provider).run
    if let .ok result := direct then return .ok result
    unless ← Expansion.enabled do return direct
    -- Reject unresolved inputs before expansion can discard their arguments.
    if (← Expr.inspectLocals source none).2 || (← hasPlaceholders source) then return direct
    let prepared ← Expansion.prepare source
      (fun expression preserve => Expr.reduceStructure expression preserve)
    if prepared.expansions == 0 then return direct
    match ← (reifyCore prepared.expression provider (some source)).run with
    | .ok result => return .ok result
    | .error error => return .error { error with
        reason := ← addMessageContext
          m!"while expanding affine helpers in {source}: {error.reason}" }
  catch exception =>
    return .error {
      expression := source
      reason := ← addMessageContext exception.toMessageData
    }

end Morew.Elab.Affine
