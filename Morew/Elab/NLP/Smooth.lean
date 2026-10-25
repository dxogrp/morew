/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Smooth
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

Real scalars, products, and finite real vectors are supported decision spaces.
Constants, projections, arithmetic, natural powers, finite sums, and the native
exponential, trigonometric, and hyperbolic functions compose structurally. Local
lets and beta applications reduce only for proof construction; named helpers do
not unfold. A decision-independent expression is a constant even if its internal
operations would require domain evidence when applied to decisions.

The returned proof mentions the original function and is checked by the kernel.
Restricted-domain operations and nonsmooth rewrites belong to later NLP passes.
Affine helper-expansion options do not affect this certifier.

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

instance : ToMessageData SmoothError := ⟨(·.reason)⟩

private abbrev CertifyM := ReaderT Expr (ExceptT SmoothError MetaM)

private def reject (expression : Expr) (kind : SmoothFailureKind)
    (reason : MessageData) : CertifyM α := do
  throwThe SmoothError {
    source := ← read
    expression
    type := ← inferType expression
    kind
    reason := ← addMessageContext
      m!"cannot certify global smoothness of {← read}: at {expression}: {reason}"
  }

private partial def supportedSpace (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if type.isConstOf ``Real then return true
  if type.isAppOfArity ``Prod 2 then
    return (← supportedSpace type.getAppArgs[0]!) &&
      (← supportedSpace type.getAppArgs[1]!)
  if let .forallE _ index body _ := type then
    if body.hasLooseBVars then return false
    unless (← whnf index).isAppOfArity ``Fin 1 do return false
    return ← supportedSpace body
  return false

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

private def construct (point expression : Expr) (name : Name) (args : Array Expr)
    (operands? : Option Nat := none) : CertifyM Expr := do
  let proof ← try
    Space.withCanonicalSpaces #[← inferType point, ← inferType expression] <|
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

private def independent (point expression : Expr) (what : String) : CertifyM Unit := do
  if ← Affine.depends point expression then
    reject expression .dependency m!"{what} depends on a decision variable"

private partial def certifyBody (point domain expression : Expr) : CertifyM Expr := do
  let expression ← Affine.reduceStructure expression (preserveLets := true)
  if let .letE name type value body nondep := expression then
    if (← Affine.depends point type) || (← Affine.depends point value) then
      return ← certifyBody point domain (body.instantiate1 value)
    return ← mapLetDeclZeta name type value (nondep := nondep) fun binding =>
      certifyBody point domain (body.instantiate1 binding)
  let type ← inferType expression
  independent point type "the value type"
  unless ← supportedSpace type do
    reject expression .unsupportedSpace m!"unsupported smooth value type {type}"
  if !(← Affine.depends point expression) then
    return ← construct point expression ``Morew.NLP.Smooth.const #[domain, expression]
  if expression == point then
    return ← construct point expression ``Morew.NLP.Smooth.id #[domain]
  if let .proj ``Prod index value := expression then
    let proof ← certifyBody point domain value
    let name := if index == 0 then ``Morew.NLP.Smooth.fst else ``Morew.NLP.Smooth.snd
    return ← construct point expression name #[← functionOf point value, proof]
  if let .lam name index body info := expression then
    let proof ← withLocalDecl name info index fun i => do
      let proof ← certifyBody point domain (body.instantiate1 i)
      mkLambdaFVars #[i] proof
    return ← construct point expression ``Morew.NLP.Smooth.pi
      #[← functionOf point expression, proof]
  let head := expression.getAppFn
  let args := expression.getAppArgs
  let name := head.constName?
  if name == some ``Function.comp && args.size == 6 then
    return ← certifyBody point domain (mkApp args[3]! (mkApp args[4]! args[5]!))
  if (name == some ``HAdd.hAdd || name == some ``HSub.hSub ||
      name == some ``HMul.hMul) && args.size == 6 then
    let left ← certifyBody point domain args[4]!
    let right ← certifyBody point domain args[5]!
    let constructor := if name == some ``HAdd.hAdd then ``Morew.NLP.Smooth.add
      else if name == some ``HSub.hSub then ``Morew.NLP.Smooth.sub
      else ``Morew.NLP.Smooth.mul
    return ← construct point expression constructor
      #[← functionOf point args[4]!, ← functionOf point args[5]!, left, right] (some 2)
  if name == some ``Neg.neg && args.size == 3 then
    let proof ← certifyBody point domain args[2]!
    return ← construct point expression ``Morew.NLP.Smooth.neg
      #[← functionOf point args[2]!, proof] (some 1)
  if name == some ``HPow.hPow && args.size == 6 then
    independent point args[5]! "the exponent"
    unless ← isDefEq (← inferType args[5]!) (mkConst ``Nat) do
      reject expression .unknownHead "only natural powers are supported"
    let proof ← certifyBody point domain args[4]!
    return ← construct point expression ``Morew.NLP.Smooth.pow
      #[← functionOf point args[4]!, args[5]!, proof] (some 2)
  if name == some ``Prod.mk && args.size == 4 then
    let left ← certifyBody point domain args[2]!
    let right ← certifyBody point domain args[3]!
    return ← construct point expression ``Morew.NLP.Smooth.pair
      #[← functionOf point args[2]!, ← functionOf point args[3]!, left, right]
  if name == some ``Finset.sum && args.size == 5 then
    independent point args[3]! "the finite sum's index set"
    independent point args[2]! "the finite sum's arithmetic instance"
    let (family, proof) ← withLocalDeclD `i args[0]! fun i => do
      let body := mkApp args[4]! i
      let proof ← certifyBody point domain body
      return (← mkLambdaFVars #[i] (← functionOf point body),
        ← mkLambdaFVars #[i] proof)
    return ← construct point expression ``Morew.NLP.Smooth.sum
      #[args[3]!, family, proof] (some 2)
  if let some atom ← Atom.recognizeAtom? expression then
    let constructor ← match atom.kind with
      | .exp => pure ``Morew.NLP.Smooth.exp
      | .sin => pure ``Morew.NLP.Smooth.sin
      | .cos => pure ``Morew.NLP.Smooth.cos
      | .sinh => pure ``Morew.NLP.Smooth.sinh
      | .cosh => pure ``Morew.NLP.Smooth.cosh
      | .tanh => pure ``Morew.NLP.Smooth.tanh
      | .log | .sqrt | .inv =>
        reject expression .restrictedDomain
          "this operation requires domain evidence; global recognition does not infer it"
      | .abs | .pos | .maximum | .minimum =>
        reject expression .nonsmooth
          "this native operation is not globally smooth in general"
    let value := atom.operands[0]!
    let proof ← certifyBody point domain value
    return ← construct point expression constructor #[← functionOf point value, proof]
  if name == some ``HDiv.hDiv && args.size == 6 then
    let left : Q(ℝ) := args[4]!
    let right : Q(ℝ) := args[5]!
    checkPrefix expression q($left / $right) 2
    reject expression .restrictedDomain "division requires domain evidence"
  -- A failed native recognizer still denotes an invalid native instance, rather
  -- than an unknown helper. Native functions with no instance prefix are handled above.
  if name == some ``Inv.inv || name == some ``abs || name == some ``PosPart.posPart ||
      name == some ``Max.max || name == some ``Min.min then
    reject expression .invalidInstance "unsupported native operation instance"
  if let .app vector index := expression then
    let vectorType ← whnf (← inferType vector)
    if vectorType.isForall && (← supportedSpace vectorType) then
      independent point index "the vector index"
      let proof ← certifyBody point domain vector
      return ← construct point expression ``Morew.NLP.Smooth.apply
        #[← functionOf point vector, index, proof]
  -- A supported scalar operand can carry a more precise obstruction than its
  -- enclosing unknown application. This inspection never unfolds that head.
  for argument in args do
    if (← Affine.depends point argument) && (← supportedSpace (← inferType argument)) then
      discard <| certifyBody point domain argument
  reject expression .unknownHead "unsupported function, coercion, or operation"

private def certifyCore (source : Expr) : CertifyM Expr := do
  let source ← instantiateMVars source
  if source.hasSorry || (← Affine.hasUnresolved source) then
    reject source .unresolved "unresolved metavariables or placeholders are not supported"
  let type ← whnf (← inferType source)
  let .forallE _ decision result _ := type
    | reject source .unsupportedSpace "expected a function from a decision space to ℝ"
  if result.hasLooseBVars then
    reject source .dependency "dependent result types are not supported"
  unless (← supportedSpace decision) && (← isDefEq result (mkConst ``Real)) do
    reject source .unsupportedSpace "expected a supported real decision space and scalar result"
  let domain ← mkAppOptM ``Set.univ #[some decision]
  let proof ← withLocalDeclD `point decision fun point =>
    certifyBody point domain (mkApp source point)
  let proof ← instantiateMVars proof
  if proof.hasSorry || (← Affine.hasUnresolved proof) then
    reject source .unresolved "smoothness construction left unresolved metavariables or placeholders"
  let function ← certificateFunction proof
  unless ← isDefEq function source do
    reject source .invalidInstance "certificate does not prove smoothness of the original function"
  -- Construct the full target independently, fixing order, domain and instances.
  let expected ← Space.withCanonicalSpaces #[decision] <|
    mkAppM ``ContDiffOn #[q(ℝ), q((2 : WithTop ℕ∞)), source, domain]
  unless ← isDefEq (← inferType proof) expected do
    reject source .invalidInstance "certificate does not establish the exact global C² target"
  checkWithKernel proof
  return proof

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
      (certifyCore source source).run
    catch exception =>
      return .error {
        source, expression := source, type := ← inferType source
        kind := .invalidInstance
        reason := ← addMessageContext exception.toMessageData
      }

end Morew.Elab.NLP.Smooth
