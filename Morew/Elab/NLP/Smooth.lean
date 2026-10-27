/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Domain
import Morew.Elab.NLP.Domain.Evidence
import Morew.Elab.NLP.Space
import Morew.Elab.Affine
import Morew.Elab.Atom
import Lean.Meta.Check

/-!
# Proof-producing recognition of globally smooth expressions

`certifyGlobal` is an internal metaprogramming interface. It proves C² smoothness
on `Set.univ` for a native fragment, including nonconvex products and polynomials.
It does not change model expressions or install a modeling command. Failure means
that the fragment did not certify the function, not that the function is not smooth.

Real scalars, finite Euclidean spaces, products, and finite real vectors are
supported decision spaces. Native Euclidean coordinates and `WithLp.toLp 2`
construction use the canonical continuous linear equivalence.
Constants, projections, arithmetic, natural powers, finite sums, and the native
exponential, trigonometric, and hyperbolic functions compose structurally. Local
lets and beta applications reduce only for proof construction; named helpers do
not unfold. A decision-independent expression is a constant even if its internal
operations would require domain evidence when applied to decisions.

The returned proof mentions the original function and is checked by the kernel.
The companion `Morew.Elab.NLP.Domain` API shares this traversal and infers open
domains for restricted operations. Its stricter constant policy leaves the
global API unchanged. Nonsmooth rewrites remain separate, and affine
helper-expansion options do not affect either smoothness certifier.

Metaprograms pass a fully elaborated `Expr` representing a function `X → ℝ` to
`Morew.Elab.NLP.Smooth.certifyGlobal`. On `.ok proof`, the ordinary Lean proof
can fill an objective or residual smoothness field whose domain is `Set.univ`.
On `.error error`, use `error.kind` for classification and `error.reason` for
rendering: the latter captures the local context of `error.expression` and
`error.type`, including any temporary decision or finite-sum binders.

For example, `fun x : ℝ => x ^ 4 - 3 * x ^ 2 + Real.sin x` is supported.
Both factors in `x * x` may depend on decisions. Natural exponents and finite
indices must be fixed with respect to decisions. Real logarithms, division,
inverse and square roots need the domain-aware API; absolute values and
min/max need separate treatment. No convexity conclusion follows from C²
smoothness, and no derivative expressions are generated.
-/

namespace Morew.Elab.NLP.Smooth

open Lean Lean.Meta Qq

/-- Failure categories for consumers of this internal certifier's diagnostics. -/
inductive SmoothFailureKind where
  /-- The input or an intermediate value has an unsupported analytic space. -/
  | unsupportedSpace
  /-- This operation needs domain evidence not supplied by global recognition. -/
  | restrictedDomain
  /-- This native operation is not globally smooth in general. -/
  | nonsmooth
  /-- No rule handles this function, coercion, or other operation. -/
  | unknownHead
  /-- The typed operation or analytic structure does not match the checked rule. -/
  | invalidInstance
  /-- The input or generated evidence contains unresolved metavariables. -/
  | unresolved
  /-- A type, exponent, or index depends on the decision point. -/
  | dependency
  /-- An inferred evaluation domain could not be proved open. -/
  | openDomain
  /-- Existing feasibility does not establish a required domain condition. -/
  | feasibleInclusion
  /-- The feasibility predicate has a row outside the admitted grammar. -/
  | unsupportedRow
  deriving BEq, Repr, Inhabited

/-- A failure retaining the original function and the local typed obstruction. -/
structure SmoothError where
  /-- The complete function supplied by the caller. -/
  source : Expr
  /-- The subexpression where recognition failed. -/
  expression : Expr
  /-- Its elaborated type, in the diagnostic's local context. -/
  type : Expr
  /-- The class of unsupported operation or evidence. -/
  kind : SmoothFailureKind
  /-- A message with the original local pretty-printing context attached. -/
  reason : MessageData
  /-- The exact missing proposition, when inclusion fails. -/
  obligation? : Option Expr := none

instance : ToMessageData SmoothError := ⟨(·.reason)⟩

/-- Checked information for an expression's evaluation domain. -/
structure DomainInfo where
  /-- The evaluation set. -/
  domain : Expr
  /-- Evidence that the evaluation set is open. -/
  isOpen : Expr
  /-- Evidence that the supplied feasibility predicate implies membership. -/
  included : Expr
  deriving Inhabited

/-- Internal traversal output, shared by global and inferred-domain recognition. -/
structure Certificate extends DomainInfo where
  /-- C² evidence for the original function on this domain. -/
  smooth : Expr
  deriving Inhabited

private structure Context where
  source : Expr
  feasible : Expr
  inferDomains : Bool := false
  prior : Array Expr := #[]
  facts? : Option Domain.Evidence.FactsProvider := none

private abbrev CertifyM := ReaderT Context (ExceptT SmoothError MetaM)

private def reject (expression : Expr) (kind : SmoothFailureKind)
    (reason : MessageData) (obligation? : Option Expr := none) : CertifyM α := do
  throwThe SmoothError {
    source := (← read).source
    expression
    type := ← inferType expression
    kind
    obligation?
    reason := ← addMessageContext
      m!"cannot certify smoothness of {(← read).source}: at {expression}: {reason}"
  }

private partial def supportedSpaceShape (euclidean : Bool) (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if type.isConstOf ``Real then return true
  if euclidean then
    if (← Affine.Space.euclideanDimension? type).isSome then return true
  if type.isAppOfArity ``Prod 2 then
    return (← supportedSpaceShape euclidean type.getAppArgs[0]!) &&
      (← supportedSpaceShape euclidean type.getAppArgs[1]!)
  if let .forallE name index body info := type then
    unless (← whnf index).isAppOfArity ``Fin 1 do return false
    return ← withLocalDecl name info index fun i => do
      let body ← Core.betaReduce (← whnf (body.instantiate1 i))
      if body.containsFVar i.fvarId! then return false
      supportedSpaceShape euclidean body
  return false

private def supportedSpace (type : Expr) : MetaM Bool :=
  supportedSpaceShape true type

-- Extending analytic spaces must not expose formerly opaque helper arguments.
private def helperArgumentSpace (type : Expr) : MetaM Bool :=
  supportedSpaceShape false type

private def functionOf (point body : Expr) : MetaM Expr :=
  mkLambdaFVars #[point] body

private def certificateFunction (proof : Expr) : MetaM Expr := do
  let type ← instantiateMVars (← inferType proof)
  unless type.isAppOf ``ContDiffOn do
    throwError "internal smooth constructor returned an unexpected proposition"
  return type.getAppArgs[type.getAppNumArgs - 2]!

-- Check the operation independently of its operands: an altered instance may
-- accidentally agree with standard arithmetic on a particular input.
private def checkPrefix (source expected : Expr) (operands : Nat) : CertifyM Unit := do
  let source := source.consumeMData
  let expected ← Affine.reduceStructure expected
  let actualArgs := source.getAppArgs
  let expectedArgs := expected.getAppArgs
  unless source.getAppFn == expected.getAppFn && actualArgs.size == expectedArgs.size &&
      operands ≤ actualArgs.size do
    reject source .invalidInstance "expected a canonical native operation"
  for i in [:actualArgs.size - operands] do
    unless ← isDefEq actualArgs[i]! expectedArgs[i]! do
      reject source .invalidInstance "expected canonical real arithmetic instances"

-- Fixed product/vector coefficients need no multiplication calculus rule, but
-- their operation instances and visible operand domains must still be checked.
-- Fix these instances at declaration time, independently of ambient instances.
private structure PointwiseArithmetic (X : Type*) where
  mul : Mul X
  pow : Pow X ℕ

private noncomputable abbrev PointwiseArithmetic.real : PointwiseArithmetic ℝ :=
  ⟨inferInstance, inferInstance⟩

private abbrev PointwiseArithmetic.prod {X Y : Type*}
    (left : PointwiseArithmetic X) (right : PointwiseArithmetic Y) :
    PointwiseArithmetic (X × Y) := by
  letI := left.mul
  letI := left.pow
  letI := right.mul
  letI := right.pow
  exact ⟨inferInstance, inferInstance⟩

private abbrev PointwiseArithmetic.pi (n : Nat) {Y : Type*}
    (target : PointwiseArithmetic Y) : PointwiseArithmetic (Fin n → Y) := by
  letI := target.mul
  letI := target.pow
  exact ⟨inferInstance, inferInstance⟩

private partial def pointwiseArithmetic (type : Expr) : MetaM Expr := do
  let shape ← whnf type
  if shape.isConstOf ``Real then
    return mkConst ``PointwiseArithmetic.real
  if shape.isAppOfArity ``Prod 2 then
    return ← mkAppM ``PointwiseArithmetic.prod
      #[← pointwiseArithmetic shape.getAppArgs[0]!,
        ← pointwiseArithmetic shape.getAppArgs[1]!]
  if let .forallE name index body info := shape then
    let indexShape ← whnf index
    if indexShape.isAppOfArity ``Fin 1 then
      return ← withLocalDecl name info index fun i => do
        let target ← pointwiseArithmetic (body.instantiate1 i)
        mkAppM ``PointwiseArithmetic.pi #[indexShape.getAppArgs[0]!, target]
  throwError "unsupported pointwise arithmetic space {type}"

private def checkPointwisePrefix (expression type : Expr) (power : Bool) : CertifyM Unit := do
  let data ← pointwiseArithmetic type
  let args := expression.getAppArgs
  let expected ← if power then do
      let pow ← mkAppM ``PointwiseArithmetic.pow #[data]
      let inst ← mkAppOptM ``instHPow #[some type, some (mkConst ``Nat), some pow]
      pure <| mkAppN expression.getAppFn
        #[type, mkConst ``Nat, type, inst, args[4]!, args[5]!]
    else do
      let mul ← mkAppM ``PointwiseArithmetic.mul #[data]
      let inst ← mkAppOptM ``instHMul #[some type, some mul]
      pure <| mkAppN expression.getAppFn
        #[type, type, type, inst, args[4]!, args[5]!]
  checkPrefix expression expected 2

-- Reduce local structural forms wherever they can hide decision independence.
-- Independent terms retain their spelling and named helpers remain boundaries.
-- Use the reduced expression in constructors as well as dependency checks, so
-- an erased decision reference cannot escape through a fixed argument or type.
private def reduceLocalStructure (point expression : Expr) : MetaM Expr := do
  let step (value : Expr) : MetaM TransformStep := do
    if !(← Affine.depends point value) then return .done value
    let reduced ← Affine.reduceStructure value
      (opaqueProblemDependencies? := some point)
    let reduced := if reduced.isAppOfArity ``Function.comp 6 then
        let args := reduced.getAppArgs
        mkApp args[3]! (mkApp args[4]! args[5]!)
      else reduced
    if reduced == value then return .continue
    return .visit reduced
  Meta.transform expression (pre := step) (post := step)

private def construct (point expression : Expr) (name : Name) (args : Array Expr)
    (operands? : Option Nat := none) (intermediateSpaces : Array Expr := #[]) : CertifyM Expr := do
  let proof ← try
    let valueType ← reduceLocalStructure point (← inferType expression)
    let intermediateSpaces ←
      (intermediateSpaces.mapM (reduceLocalStructure point) : MetaM (Array Expr))
    -- Projections also need the operand's structures, even when its finite
    -- index or unused product component is absent from the decision/result.
    Space.withCanonicalSpaces (#[← inferType point, valueType] ++ intermediateSpaces) <|
      mkAppM name args
  catch exception =>
    reject expression .invalidInstance
      m!"unsupported analytic types or instances: {exception.toMessageData}"
  let function ← certificateFunction proof
  if let some count := operands? then
    checkPrefix expression (function.beta #[point]) count
  unless ← isDefEq function (← functionOf point expression) do
    reject expression .invalidInstance "smoothness construction does not match this typed expression"
  return proof

private def fixedArgument (point expression : Expr) (what : String) : CertifyM Expr := do
  let reduced ← reduceLocalStructure point expression
  if ← Affine.depends point reduced then
    reject expression .dependency m!"{what} depends on a decision variable"
  return reduced

private def domainApp (point : Expr) (name : Name) (args : Array Expr) : MetaM Expr := do
  Space.withCanonicalSpaces #[← inferType point] (mkAppM name args)

private def univInfo (point : Expr) : CertifyM DomainInfo := do
  let decision ← inferType point
  return {
    domain := ← mkAppOptM ``Set.univ #[some decision]
    isOpen := ← Space.withCanonicalSpaces #[decision] <|
      mkAppOptM ``Morew.NLP.Domain.univ_open #[some decision, none]
    included := ← mkAppM ``Morew.NLP.Domain.univ_includes #[(← read).feasible]
  }

private def restrictProof (point proof domain subset : Expr) : MetaM Expr := do
  let function ← certificateFunction proof
  let args := (← inferType proof).getAppArgs
  Space.withCanonicalSpaces #[← inferType point, ← inferType (mkApp function point)] <|
    mkAppM ``Morew.NLP.Domain.restrict #[function, args.back!, domain, proof, subset]

private def combine (point : Expr) (children : Array Certificate) :
    CertifyM (DomainInfo × Array Expr) := do
  if children.isEmpty then return (← univInfo point, #[])
  let mut info := children[0]!.toDomainInfo
  let mut proofs := #[children[0]!.smooth]
  for child in children[1:] do
    if info.domain == child.domain then
      proofs := proofs.push child.smooth
    else
      let domain ← mkAppM ``Morew.NLP.Domain.inter #[info.domain, child.domain]
      let left ← mkAppM ``Morew.NLP.Domain.inter_left #[info.domain, child.domain]
      let right ← mkAppM ``Morew.NLP.Domain.inter_right #[info.domain, child.domain]
      proofs ← proofs.mapM fun proof => restrictProof point proof domain left
      proofs := proofs.push (← restrictProof point child.smooth domain right)
      info := {
        domain
        isOpen := ← domainApp point ``Morew.NLP.Domain.inter_open
          #[info.domain, child.domain, info.isOpen, child.isOpen]
        included := ← mkAppM ``Morew.NLP.Domain.inter_includes
          #[(← read).feasible, info.domain, child.domain, info.included, child.included]
      }
  return (info, proofs)

private def after (child : Certificate) (action : CertifyM α) : CertifyM α :=
  withReader (fun ctx => { ctx with prior := ctx.prior.push child.included }) action

private def constant (point expression : Expr) (info : DomainInfo) : CertifyM Certificate := do
  return { info with
    smooth := ← construct point expression ``Morew.NLP.Smooth.const #[info.domain, expression] }

-- Only the inclusion proof uses feasibility. The domain and its analytic proofs
-- are built without any assumption that the current domain condition holds.
private def restrictDomain (point expression value : Expr) (positive : Bool)
    (info : DomainInfo) (proofs : Array Expr) (valueProof : Expr) :
    CertifyM (DomainInfo × Array Expr × Expr) := do
  let function ← functionOf point value
  let base := if positive then `Morew.NLP.Domain.positive else `Morew.NLP.Domain.nonzero
  let domain ← mkAppM base #[info.domain, function]
  let isOpen ← try
    domainApp point (base.appendAfter "_open") #[info.domain, function, info.isOpen, valueProof]
  catch exception =>
    reject expression .openDomain exception.toMessageData
  let subset ← mkAppM (base.appendAfter "_subset") #[info.domain, function]
  let holds ← mkAppM (base.appendAfter "_holds") #[info.domain, function]
  let value : Q(ℝ) := value
  let required : Expr := if positive then q(0 < $value) else q($value ≠ 0)
  let feasible := (← read).feasible
  let inclusion ← withLocalDeclD `feasiblePoint (mkApp feasible point) fun hp => do
    let mut facts ← match (← read).facts? with
      | none => Domain.Evidence.rowFacts point hp
      | some provider => provider point hp required
    facts := facts.push (mkApp2 info.included point hp)
    for prior in (← read).prior do
      facts := facts.push (mkApp2 prior point hp)
    let some evidence ← Domain.Evidence.prove? point required facts
      | reject expression .feasibleInclusion
          m!"existing feasibility does not establish the domain condition {required}" (some required)
    mkLambdaFVars #[point, hp] evidence
  let included ← mkAppM (base.appendAfter "_includes")
    #[feasible, info.domain, function, info.included, inclusion]
  let proofs ← proofs.mapM fun proof => restrictProof point proof domain subset
  return ({ domain, isOpen, included }, proofs, holds)

-- Bring structural bindings in a projection operand into the traversal's
-- scope. Unlike zeta reduction, this retains independent proof lets/instances.
private def hoistProjectionLets : Expr → Expr
  | .proj name index value =>
    match hoistProjectionLets value with
    | .letE binding type value body nondep =>
      .letE binding type value (.proj name index body) nondep
    | value => .proj name index value
  | expression => expression

private partial def certifyBody (point expression : Expr) : CertifyM Certificate := do
  let expression := hoistProjectionLets (← Affine.reduceStructure expression (preserveLets := true)
    (opaqueProblemDependencies? := some point))
  if let .letE name type value body nondep := expression then
    if (← Affine.depends point type) || (← Affine.depends point value) then
      return ← certifyBody point (body.instantiate1 value)
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← certifyBody point (body.instantiate1 binding)
      return {
        domain := ← result.domain.replaceFVarsM #[binding] #[value]
        isOpen := ← result.isOpen.replaceFVarsM #[binding] #[value]
        included := ← result.included.replaceFVarsM #[binding] #[value]
        smooth := ← result.smooth.replaceFVarsM #[binding] #[value]
      }
  let expression ← reduceLocalStructure point expression
  let type ← fixedArgument point (← inferType expression) "the value type"
  unless ← supportedSpace type do
    reject expression .unsupportedSpace m!"unsupported smooth value type {type}"
  let inferDomains := (← read).inferDomains
  let independent := !(← Affine.depends point expression)
  if independent && !inferDomains then
    return ← constant point expression (← univInfo point)
  if expression == point then
    let info ← univInfo point
    return { info with
      smooth := ← construct point expression ``Morew.NLP.Smooth.id #[info.domain] }
  if let .proj ``WithLp 0 value := expression then
    if (← Affine.Space.euclideanDimension? (← inferType value)).isSome then
      let child ← certifyBody point value
      return { child with
        smooth := ← construct point expression ``Morew.NLP.Smooth.ofEuclidean
          #[← functionOf point value, child.smooth] (intermediateSpaces := #[← inferType value]) }
  if let .proj ``Prod index value := expression then
    -- A fixed scalar/vector component need not give the whole parameter an
    -- analytic structure. Unsupported value spaces remain opaque, after the
    -- structural reductions above have exposed any selected tuple component.
    if independent && !(← supportedSpace (← inferType value)) then
      return ← constant point expression (← univInfo point)
    let child ← certifyBody point value
    let name := if index == 0 then ``Morew.NLP.Smooth.fst else ``Morew.NLP.Smooth.snd
    return { child with
      smooth := ← construct point expression name
        #[← functionOf point value, child.smooth] (intermediateSpaces := #[← inferType value]) }
  if let .lam name index body binderInfo := expression then
    let index ← fixedArgument point index "the vector index type"
    let (sets, opens, includes, smooths) ← withLocalDecl name binderInfo index fun i => do
      let child ← certifyBody point (body.instantiate1 i)
      return (← mkLambdaFVars #[i] child.domain, ← mkLambdaFVars #[i] child.isOpen,
        ← mkLambdaFVars #[i] child.included, ← mkLambdaFVars #[i] child.smooth)
    let info ← if inferDomains then do
      pure {
        domain := ← mkAppM ``Morew.NLP.Domain.family #[sets]
        isOpen := ← Space.withCanonicalSpaces #[← inferType point, type] <|
          mkAppM ``Morew.NLP.Domain.family_open #[sets, opens]
        included := ← mkAppM ``Morew.NLP.Domain.family_includes #[(← read).feasible, sets, includes]
      }
      else univInfo point
    let proof ← withLocalDecl name binderInfo index fun i => do
      let proof := mkApp smooths i
      let proof ← if inferDomains then do
        let subset ← mkAppM ``Morew.NLP.Domain.family_subset #[sets, i]
        restrictProof point proof info.domain subset
        else pure proof
      mkLambdaFVars #[i] proof
    return { info with
      smooth := ← construct point expression ``Morew.NLP.Smooth.pi
        #[← functionOf point expression, proof] }
  let head := expression.getAppFn
  let args := expression.getAppArgs
  let name := head.constName?
  if name == some ``WithLp.toLp && args.size == 3 then
    if (← Affine.Space.euclideanDimension? type).isSome then
      let child ← certifyBody point args[2]!
      return { child with
        smooth := ← construct point expression ``Morew.NLP.Smooth.toEuclidean
          #[← functionOf point args[2]!, child.smooth]
          (intermediateSpaces := #[← inferType args[2]!]) }
  if name == some ``WithLp.ofLp && args.size == 3 then
    if (← Affine.Space.euclideanDimension? (← inferType args[2]!)).isSome then
      let child ← certifyBody point args[2]!
      return { child with
        smooth := ← construct point expression ``Morew.NLP.Smooth.ofEuclidean
          #[← functionOf point args[2]!, child.smooth]
          (intermediateSpaces := #[← inferType args[2]!]) }
  if name == some ``Function.comp && args.size == 6 then
    return ← certifyBody point (mkApp args[3]! (mkApp args[4]! args[5]!))
  if (name == some ``HAdd.hAdd || name == some ``HSub.hSub ||
      name == some ``HMul.hMul || name == some ``Prod.mk) &&
      (args.size == 6 || (name == some ``Prod.mk && args.size == 4)) then
    let lhs := args[args.size - 2]!
    let rhs := args.back!
    let left ← certifyBody point lhs
    let right ← after left <| certifyBody point rhs
    let (info, proofs) ← combine point #[left, right]
    if name == some ``HMul.hMul && independent && !(← whnf type).isConstOf ``Real then
      checkPointwisePrefix expression type false
      return ← constant point expression info
    let constructor := if name == some ``HAdd.hAdd then ``Morew.NLP.Smooth.add
      else if name == some ``HSub.hSub then ``Morew.NLP.Smooth.sub
      else if name == some ``HMul.hMul then ``Morew.NLP.Smooth.mul
      else ``Morew.NLP.Smooth.pair
    return { info with
      smooth := ← construct point expression constructor
        #[← functionOf point lhs, ← functionOf point rhs, proofs[0]!, proofs[1]!]
        (if name == some ``Prod.mk then none else some 2) }
  if name == some ``Neg.neg && args.size == 3 then
    let child ← certifyBody point args[2]!
    return { child with
      smooth := ← construct point expression ``Morew.NLP.Smooth.neg
        #[← functionOf point args[2]!, child.smooth] (some 1) }
  if name == some ``HPow.hPow && args.size == 6 then
    if !inferDomains then
      discard <| fixedArgument point args[5]! "the exponent"
    if ← isDefEq (← inferType args[5]!) (mkConst ``Nat) then
      let exponent ← fixedArgument point args[5]! "the exponent"
      let child ← certifyBody point args[4]!
      if independent && !(← whnf type).isConstOf ``Real then
        checkPointwisePrefix expression type true
        return ← constant point expression child.toDomainInfo
      return { child with
        smooth := ← construct point expression ``Morew.NLP.Smooth.pow
          #[← functionOf point args[4]!, exponent, child.smooth] (some 2) }
    if !inferDomains then
      reject expression .unknownHead "only natural powers are supported"
  if name == some ``Finset.sum && args.size == 5 then
    let indices ← fixedArgument point args[3]! "the finite sum's index set"
    discard <| fixedArgument point args[2]! "the finite sum's arithmetic instance"
    let indexType ← fixedArgument point args[0]! "the finite sum's index type"
    if !inferDomains then
      let (family, proof) ← withLocalDeclD `i indexType fun i => do
        let body := mkApp args[4]! i
        let child ← certifyBody point body
        return (← mkLambdaFVars #[i] (← functionOf point body), ← mkLambdaFVars #[i] child.smooth)
      let info ← univInfo point
      return { info with
        smooth := ← construct point expression ``Morew.NLP.Smooth.sum
          #[indices, family, proof] (some 2) }
    let (family, sets, opens, includes, smooths) ← withLocalDeclD `i indexType fun i => do
      let membership ← mkAppM ``Membership.mem #[indices, i]
      withLocalDeclD `inSupport membership fun hi => do
        let body := mkApp args[4]! i
        let child ← certifyBody point body
        for value in #[child.domain, child.isOpen, child.smooth] do
          if value.containsFVar hi.fvarId! then
            reject expression .invalidInstance "analytic evidence escaped the finite support scope"
        return (← mkLambdaFVars #[i] (← functionOf point body),
          ← mkLambdaFVars #[i] child.domain, ← mkLambdaFVars #[i, hi] child.isOpen,
          ← mkLambdaFVars #[i, hi] child.included, ← mkLambdaFVars #[i] child.smooth)
    let info : DomainInfo := {
      domain := ← mkAppM ``Morew.NLP.Domain.bounded #[indices, sets]
      isOpen := ← domainApp point ``Morew.NLP.Domain.bounded_open #[indices, sets, opens]
      included := ← mkAppM ``Morew.NLP.Domain.bounded_includes #[(← read).feasible, indices, sets, includes]
    }
    let proof ← withLocalDeclD `i indexType fun i => do
      let membership ← mkAppM ``Membership.mem #[indices, i]
      withLocalDeclD `inSupport membership fun hi => do
        let subset ← mkAppM ``Morew.NLP.Domain.bounded_subset #[indices, sets, i, hi]
        let proof ← restrictProof point (mkApp smooths i) info.domain subset
        mkLambdaFVars #[i, hi] proof
    return { info with
      smooth := ← construct point expression ``Morew.NLP.Domain.sum
        #[indices, family, proof] (some 2) }
  if let some atom ← Atom.recognizeAtom? expression then
    if atom.kind == .rpow && !inferDomains then
      -- Explicit Real.rpow was previously an unknown application. Retain its
      -- operand diagnostics in global mode; HPow's old boundary is above.
      for argument in args do
        if (← Affine.depends point argument) && (← supportedSpace (← inferType argument)) then
          discard <| certifyBody point argument
      reject expression .unknownHead "unsupported function, coercion, or operation"
    let restricted := atom.kind == .log || atom.kind == .sqrt || atom.kind == .inv || atom.kind == .rpow
    let nonsmooth := atom.kind == .abs || atom.kind == .pos || atom.kind == .maximum || atom.kind == .minimum
    if restricted && !inferDomains then
      reject expression .restrictedDomain
        "this operation requires domain evidence; global recognition does not infer it"
    if nonsmooth && !independent then
      reject expression .nonsmooth "this native operation is not globally smooth in general"
    let mut children : Array Certificate := #[]
    for i in [:atom.operands.size] do
      let operand ← if atom.kind == .rpow && i == 1 then
        fixedArgument point atom.operands[i]! "the real exponent"
        else pure atom.operands[i]!
      let child ← withReader (fun ctx => { ctx with
        prior := ctx.prior ++ children.map (·.included) }) <| certifyBody point operand
      children := children.push child
    let (info, proofs) ← combine point children
    if nonsmooth then return ← constant point expression info
    let value := atom.operands[0]!
    let constructor := match atom.kind with
      | .exp => ``Morew.NLP.Smooth.exp
      | .sin => ``Morew.NLP.Smooth.sin
      | .cos => ``Morew.NLP.Smooth.cos
      | .sinh => ``Morew.NLP.Smooth.sinh
      | .cosh => ``Morew.NLP.Smooth.cosh
      | .tanh => ``Morew.NLP.Smooth.tanh
      | .log => ``Morew.NLP.Domain.log
      | .sqrt => ``Morew.NLP.Domain.sqrt
      | .inv => ``Morew.NLP.Domain.inv
      | .rpow => ``Morew.NLP.Domain.rpow
      | _ => unreachable!
    if restricted then
      let (info, proofs, holds) ← restrictDomain point expression value (atom.kind != .inv)
        info proofs proofs[0]!
      let arguments ← if atom.kind == .rpow then do
          pure #[← functionOf point value,
            ← fixedArgument point atom.operands[1]! "the real exponent", proofs[0]!, holds]
        else do pure #[← functionOf point value, proofs[0]!, holds]
      return { info with
        smooth := ← construct point expression constructor arguments }
    return { info with
      smooth := ← construct point expression constructor
        #[← functionOf point value, proofs[0]!] }
  if name == some ``HDiv.hDiv && args.size == 6 then
    let left : Q(ℝ) := args[4]!
    let right : Q(ℝ) := args[5]!
    checkPrefix expression q($left / $right) 2
    if !inferDomains then reject expression .restrictedDomain "division requires domain evidence"
    let numerator ← certifyBody point left
    let denominator ← after numerator <| certifyBody point right
    let (info, proofs) ← combine point #[numerator, denominator]
    let (info, proofs, holds) ← restrictDomain point expression right false info proofs proofs[1]!
    return { info with
      smooth := ← construct point expression ``Morew.NLP.Domain.div
        #[← functionOf point left, ← functionOf point right, proofs[0]!, proofs[1]!, holds] (some 2) }
  if name == some ``Inv.inv || name == some ``abs || name == some ``PosPart.posPart ||
      name == some ``Max.max || name == some ``Min.min then
    reject expression .invalidInstance "unsupported native operation instance"
  if name == some ``HPow.hPow then
    if inferDomains && args.size == 6 then
      if ← isDefEq args[1]! (mkConst ``Real) then
        reject expression .invalidInstance "unsupported real-power instance"
    if !independent then
      reject expression .unknownHead "unsupported power type or instance"
  if let .app vector index := expression then
    let vectorType ← whnf (← inferType vector)
    if vectorType.isForall && (← supportedSpace vectorType) then
      let index ← fixedArgument point index "the vector index"
      let child ← certifyBody point vector
      return { child with
        smooth := ← construct point expression ``Morew.NLP.Smooth.apply
          #[← functionOf point vector, index, child.smooth] (intermediateSpaces := #[vectorType]) }
  -- Constant helper bodies remain opaque, but supported value arguments retain
  -- their native evaluation requirements. Function and proof arguments do not.
  let mut children : Array Certificate := #[]
  for argument in args do
    if (independent || (← Affine.depends point argument)) &&
        (← helperArgumentSpace (← inferType argument)) then
      let child ← withReader (fun ctx => { ctx with
        prior := ctx.prior ++ children.map (·.included) }) <| certifyBody point argument
      children := children.push child
  if independent then
    let (info, _) ← combine point children
    return ← constant point expression info
  reject expression .unknownHead "unsupported function, coercion, or operation"


private def certifyCore (source : Expr) : CertifyM Certificate := do
  let source ← instantiateMVars source
  unless ← Domain.Evidence.complete source do
    reject source .unresolved "unresolved metavariables or placeholders are not supported"
  let type ← whnf (← inferType source)
  let .forallE _ decision result _ := type
    | reject source .unsupportedSpace "expected a function from a decision space to ℝ"
  let result ← withLocalDeclD `point decision fun point =>
    fixedArgument point (result.instantiate1 point) "the result type"
  unless (← supportedSpace decision) && (← isDefEq result (mkConst ``Real)) do
    reject source .unsupportedSpace "expected a supported real decision space and scalar result"
  let result ← withLocalDeclD `point decision fun point =>
    certifyBody point (mkApp source point)
  let result : Certificate := {
    domain := ← instantiateMVars result.domain
    isOpen := ← instantiateMVars result.isOpen
    included := ← instantiateMVars result.included
    smooth := ← instantiateMVars result.smooth
  }
  let proof := result.smooth
  let domain := result.domain
  unless ← Domain.Evidence.complete proof do
    reject source .unresolved "smoothness construction left unresolved metavariables or placeholders"
  let function ← certificateFunction proof
  unless ← isDefEq function source do
    reject source .invalidInstance "certificate does not prove smoothness of the original function"
  -- Construct the full target independently, fixing order, domain and instances.
  let expected ← Space.withCanonicalSpaces #[decision] <|
    mkAppM ``ContDiffOn #[q(ℝ), q((2 : WithTop ℕ∞)), source, domain]
  unless ← isDefEq (← inferType proof) expected do
    reject source .invalidInstance "certificate does not establish the exact C² target"
  checkWithKernel proof
  for evidence in #[result.isOpen, result.included] do
    unless ← Domain.Evidence.complete evidence do
      reject source .unresolved "domain construction left incomplete evidence"
    checkWithKernel evidence
  return { result with
    smooth := proof }

/-- Certify a native function without modifying caller metavariables.

The proof establishes `ContDiffOn ℝ 2 source Set.univ` for the original function.
Canonical real, product, and finite-vector analytic instances are fixed and
retained in the checked proof. Local lets and
beta applications may reduce, but named helpers never unfold. Rejection restores
the environment as well as metavariables, and carries the failing typed term.
-/
def certifyGlobal (source : Expr) : MetaM (Except SmoothError Expr) :=
  Affine.withIsolatedMVars do
    try
      let type ← whnf (← inferType source)
      let decision := match type with
        | .forallE _ decision _ _ => decision
        | _ => mkConst ``Unit
      let feasible ← withLocalDeclD `point decision fun point =>
        mkLambdaFVars #[point] (mkConst ``True)
      match ← (certifyCore source { source, feasible }).run with
      | .ok result => return .ok result.smooth
      | .error error => return .error error
    catch exception =>
      return .error {
        source, expression := source, type := ← inferType source
        kind := .invalidInstance
        reason := ← addMessageContext exception.toMessageData
      }

/-- Internal shared traversal in domain-inference mode. The caller validates the
feasibility grammar and checks that its decision space agrees with the source.
Previously proved inclusion certificates may supply earlier domain facts. -/
def certifyOnFeasible (feasible source : Expr) (prior : Array Expr := #[])
    (facts? : Option Domain.Evidence.FactsProvider := none) :
    MetaM (Except SmoothError Certificate) :=
  Affine.withIsolatedMVars do
    try
      (certifyCore source { source, feasible, inferDomains := true, prior, facts? }).run
    catch exception =>
      return .error {
        source, expression := source, type := ← inferType source
        kind := .invalidInstance
        reason := ← addMessageContext exception.toMessageData
      }

end Morew.Elab.NLP.Smooth
