/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Elab.Rewrite.Comparison
import Lean

/-! Register exact representations with `morew_conic` and `morew_nlp`, following Lean
attribute scope. Records live in `Type`. Registration checks record types and requires
fixed source heads; certificates are checked on use.

Automatic discovery certifies all matching rules and requires one success, after
the built-in SOC/power norm preference for conic rules. Ambiguous names are sorted.
Explicit `using` selects a single declaration or certificate, registered or otherwise.

Graph and bound matching adapts outer real negations by equivalence while retaining
operation instances; whole-predicate records match literally. Independent or retained
evidence discharges subtype conditions and proof parameters. Exactness uses the retained
constraints; auxiliary types are decision-independent and targets are proof-independent.
`Unit` auxiliaries add no coordinate.

Conic premises use direct lower bounds; NLP uses bounded reasoning over retained real
equalities, non-strict inequalities, and compatible finite indices. Once exactness is proved,
NLP may use generated constraints for domain inclusion. Unsupported retained predicates supply no facts.

Conic and NLP `Rules` modules install built-ins; `Morew.Reformulation` imports both rule sets. -/

namespace Morew.Elab.Rewrite.Registry

open Lean Lean.Meta

/-- The two target forms supported by exact representation declarations. -/
inductive Target where
  | conic | nlp
  deriving BEq, Inhabited

/-- The source orientation recorded by a representation. -/
inductive Family where
  | exact | graph | epigraph | hypograph
  deriving BEq, Inhabited, Repr

/-- Lookup metadata; check types and certificates on every use. -/
structure Entry where
  /-- The fully qualified declaration to instantiate and check. -/
  declaration : Name
  /-- The certificate family and source orientation. -/
  family : Family
  /-- The fixed operation or complete-predicate head. -/
  head : Name
  /-- A fixed output-type head, or a wildcard for generic output types. -/
  outputHead? : Option Name := none
  /-- Fixed type-valued arguments by application position; generic types remain wildcards. -/
  typeArgumentHeads : Array (Nat × Name) := #[]
  deriving BEq, Inhabited

/-- Reduce binding syntax without unfolding named mathematical functions. -/
partial def structural (expression : Expr) (preserveLets : Bool := false) : MetaM Expr := do
  let expression := (← instantiateMVars expression).consumeMData
  match expression with
  | .letE _ _ value body _ =>
    if preserveLets then pure expression else structural (body.instantiate1 value)
  | .fvar id =>
    if let some value := (← id.getDecl).value? (allowNondep := true) then
      structural value preserveLets
    else pure expression
  | .app .. =>
    let arguments := expression.getAppArgs
    let fn ← structural expression.getAppFn preserveLets
    if let .letE name type value body nondep := fn then
      return ← structural (.letE name type value
        (mkAppN body (arguments.map (·.liftLooseBVars 0 1))) nondep) preserveLets
    if fn.isLambda then return ← structural (fn.beta arguments) preserveLets
    if (fn.isConstOf ``Prod.casesOn || fn.isConstOf ``Prod.rec) && arguments.size >= 5 then
      let value := arguments[if fn.isConstOf ``Prod.casesOn then 3 else 4]!
      let branch := arguments[if fn.isConstOf ``Prod.casesOn then 4 else 3]!
      let fields := #[Expr.proj ``Prod 0 value, Expr.proj ``Prod 1 value]
      return ← structural (mkAppN (branch.beta fields)
        (arguments.extract 5 arguments.size)) preserveLets
    if let some name := fn.constName? then
      if let some matcher ← getMatcherInfo? name then
        if matcher.numAlts == 1 && arguments.size >= matcher.arity then
          let mut productsOnly := decide (matcher.numDiscrs > 0)
          for index in [matcher.getFirstDiscrPos:matcher.getFirstAltPos] do
            let type ← whnf (← inferType arguments[index]!)
            productsOnly := productsOnly && type.isAppOfArity ``Prod 2
          if productsOnly then
            let declaration ← getConstInfo name
            if let some value := declaration.value? then
              let value := value.instantiateLevelParams declaration.levelParams fn.constLevels!
              return ← structural (value.beta arguments) preserveLets
    if (fn.isConstOf ``Prod.fst || fn.isConstOf ``Prod.snd) && arguments.size >= 3 then
      let args := arguments
      let projected ← structural (.proj ``Prod (if fn.isConstOf ``Prod.fst then 0 else 1)
        args[2]!) preserveLets
      return ← structural (mkAppN projected (args.extract 3 args.size)) preserveLets
    if fn.isConstOf ``Subtype.val && arguments.size >= 3 then
      let args := arguments
      let projected ← structural (.proj ``Subtype 0 args[2]!) preserveLets
      return ← structural (mkAppN projected (args.extract 3 args.size)) preserveLets
    pure (mkAppN fn arguments)
  | .proj name index value =>
    let value ← structural value preserveLets
    if value.isAppOf ``Prod.mk then structural value.getAppArgs[index + 2]! preserveLets
    else if name == ``Subtype && value.isAppOf ``Subtype.mk then
      structural value.getAppArgs[index + 2]! preserveLets
    else pure (.proj name index value)
  | _ => pure expression

/-- Read the accepted family and represented predicate/function from a type. -/
def representation (type : Expr) : MetaM (Family × Expr × Expr) := do
  let type ← whnf type
  let args := type.getAppArgs
  if type.isAppOfArity ``Morew.ExactConstraintLift 2 then
    return (.exact, args[0]!, args[1]!)
  if type.isAppOfArity ``Morew.GraphRepresentation 3 then
    return (.graph, args[0]!, args[2]!)
  if type.isAppOfArity ``Morew.EpigraphRepresentation 4 then
    return (.epigraph, args[0]!, args[3]!)
  if type.isAppOfArity ``Morew.HypographRepresentation 4 then
    return (.hypograph, args[0]!, args[3]!)
  throwError "expected ExactConstraintLift, GraphRepresentation, EpigraphRepresentation, or HypographRepresentation; reduced type is {type}"

private def fixedTypeHead? (type : Expr) : MetaM (Option Name) := do
  let type ← whnf type
  -- Keep parameter-dependent type heads as lookup wildcards.
  if type.hasFVar || type.hasMVar then return none
  return type.getAppFn.constName?

private def typeArgumentHeads (expression : Expr) : MetaM (Array (Nat × Name)) := do
  let mut heads := #[]
  for argument in expression.getAppArgs, index in [:expression.getAppNumArgs] do
    if (← whnf (← inferType argument)).isSort then
      if let some head ← fixedTypeHead? argument then
        heads := heads.push (index, head)
  return heads

private def entry (declaration : Name) : MetaM Entry := do
  let type := (← getConstInfo declaration).type
  forallTelescopeReducing type fun _ body => do
    let body ← whnf body
    let (family, input, represented) ← representation body
    let outputHead? ← if family == .exact then pure none else fixedTypeHead? body.getAppArgs[1]!
    withLocalDeclD `input input fun input => do
      let body ← structural (mkApp represented input)
      let .const head _ := body.getAppFn
        | throwError "cannot register {declaration}: the represented source has no fixed operation head: {body}; reduced type is {← whnf (← inferType (← mkConstWithFreshMVarLevels declaration))}"
      let head := if family == .exact && head == ``GE.ge then ``LE.le else head
      let typeArgumentHeads ← if family == .exact then pure #[] else typeArgumentHeads body
      return { declaration, family, head, outputHead?, typeArgumentHeads }

private def makeExtension (name : Name) : IO (SimpleScopedEnvExtension Entry (Array Entry)) :=
  registerSimpleScopedEnvExtension {
    name, initial := #[]
    addEntry := fun entries value =>
      if entries.any (·.declaration == value.declaration) then entries else entries.push value }

/-- Scoped persistent registrations for conic rewriting. -/
initialize conicExtension : SimpleScopedEnvExtension Entry (Array Entry) ←
  makeExtension `morewConicRegistry

/-- Scoped persistent registrations for smooth-NLP rewriting. -/
initialize nlpExtension : SimpleScopedEnvExtension Entry (Array Entry) ←
  makeExtension `morewNLPRegistry

private def register (name : Name)
    (extension : SimpleScopedEnvExtension Entry (Array Entry)) : IO Unit :=
  registerBuiltinAttribute {
    name, descr := "checked exact constraint representation"
    applicationTime := .afterCompilation
    add := fun declaration stx kind => MetaM.run' do
      Attribute.Builtin.ensureNoArgs stx
      let metadata ← entry declaration
      extension.add metadata kind
    erase := fun declaration => do
      modifyEnv fun env => extension.modifyState env fun entries =>
        entries.filter (·.declaration != declaration) }

initialize register `morew_conic conicExtension
initialize register `morew_nlp nlpExtension

/-- Current registrations, sorted independently of declaration/import order. -/
def entries (target : Target) : CoreM (Array Entry) := do
  let extension := if target == .conic then conicExtension else nlpExtension
  return (extension.getState (← getEnv)).qsort fun a b =>
    a.declaration.toString < b.declaration.toString

private def operation? (expression : Expr) :
    MetaM (Option (Name × Array (Nat × Name))) := do
  let expression ← structural expression
  let .const name _ := expression.getAppFn | return none
  return some (name, ← typeArgumentHeads expression)

private def compatibleOperation (entry : Entry)
    (operation : Option (Name × Array (Nat × Name))) : Bool :=
  match operation with
  | none => false
  | some (head, actualTypes) =>
    head == entry.head && entry.typeArgumentHeads.all fun (index, expected) =>
      match actualTypes.find? (·.1 == index) with
      | some (_, actual) => expected == actual
      | none => true

/-- Discover declarations with compatible source heads, orientations, and fixed types.
Generic types remain candidates for matching and certification. -/
def candidates (target : Target) (source : Expr) : MetaM (Array Name) := do
  let type ← whnf (← inferType source)
  let .forallE _ domain _ _ := type | throwError "expected a constraint predicate"
  withLocalDeclD `point domain fun point => do
    let body ← structural (mkApp source point)
    let sourceHead := body.getAppFn.constName?
    let sourceHead := if sourceHead == some ``GE.ge then some ``LE.le else sourceHead
    let args := body.getAppArgs
    let mut epigraphs := #[]
    let mut hypographs := #[]
    let mut graphs := #[]
    let mut outputHead? := none
    if body.isAppOfArity ``LE.le 4 then
      outputHead? ← fixedTypeHead? args[0]!
      epigraphs := epigraphs.push (← operation? args[2]!)
      hypographs := hypographs.push (← operation? args[3]!)
    else if body.isAppOfArity ``GE.ge 4 then
      outputHead? ← fixedTypeHead? args[0]!
      epigraphs := epigraphs.push (← operation? args[3]!)
      hypographs := hypographs.push (← operation? args[2]!)
    else if body.isAppOfArity ``Eq 3 then
      outputHead? ← fixedTypeHead? args[0]!
      graphs := graphs.push (← operation? args[1]!)
      graphs := graphs.push (← operation? args[2]!)
    for view in (← Comparison.signedViews body (fun e => structural e)).toList.drop 1 do
      let args := view.predicate.getAppArgs
      if view.predicate.isAppOfArity ``LE.le 4 then
        epigraphs := epigraphs.push (← operation? args[2]!)
        hypographs := hypographs.push (← operation? args[3]!)
      else if view.predicate.isAppOfArity ``Eq 3 then
        graphs := graphs.push (← operation? args[1]!)
        graphs := graphs.push (← operation? args[2]!)
    -- Deduplicate sorted declarations across comparison views.
    return (← entries target).filterMap fun entry =>
      let compatible := match entry.family with
        | .exact => sourceHead == some entry.head
        | .epigraph => epigraphs.any (compatibleOperation entry)
        | .hypograph => hypographs.any (compatibleOperation entry)
        | .graph => graphs.any (compatibleOperation entry)
      let compatibleType := match entry.outputHead?, outputHead? with
        | some expected, some actual => expected == actual
        | _, _ => true
      if compatible && compatibleType then some entry.declaration else none

end Morew.Elab.Rewrite.Registry
