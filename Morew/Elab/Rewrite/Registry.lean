/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Lean

/-!
# Registered exact representations

`@[morew_conic]` and `@[morew_nlp]` register proof-bearing representation
definitions for automatic constraint rewriting. A definition may carry both
attributes. Registration is scoped in the usual Lean sense: `attribute [local
morew_nlp] rule`, `attribute [scoped morew_nlp] rule`, and `attribute
[-morew_nlp] rule` have their ordinary activation and restoration behavior.

The registry stores lookup information, never trusted certificates. Consumers
instantiate and check every candidate, then require one fully certified result.
An explicit `using` certificate does not need registration.

Representation records live in `Type`, so rule authors normally use `def` or
`noncomputable def`, rather than `theorem`. For example, a definition of type
`EpigraphRepresentation f` may carry `@[morew_conic, morew_nlp]`; its target must
then pass the respective conic or smooth certification whenever it is selected.
Namespaces do not register rules. Malformed records and variable-headed source
patterns are rejected when the attribute is applied, before any model uses them.

For example, the following definition reuses the checked absolute-value rule
for a named helper (a compiled version is in the command regression tests):

```lean
open Morew

noncomputable def shiftedAbs (center x : ℝ) : ℝ := |x - center|

@[morew_conic, morew_nlp]
noncomputable def shiftedAbsEpigraph (center : ℝ) :
    EpigraphRepresentation (shiftedAbs center) where
  Auxiliary := Unit
  target x t _ := x - center ≤ t ∧ -(x - center) ≤ t
  source_iff_exists x t := Rewrite.absEpigraph.source_iff_exists (x - center) t
```

Import `Morew.Reformulation` for the public commands and built-in registrations.
Metaprograms can instead import `Morew.Elab.Conic.Rules` or
`Morew.Elab.NLP.Rules`; these modules do not import the modeling DSL. This
registry module alone defines the attributes without registering built-ins.
The semantic `Morew.Rewrite`, `Morew.Conic`, and `Morew.NLP` entry points remain
independent of registration and command elaboration.

Automatic rewriting tries every matching registration and accepts exactly one
fully certified result. Ambiguity lists fully qualified declaration names in
sorted order. `conic at bound using shiftedAbsEpigraph` and the corresponding
`nlp` command infer `center` from the entire selected row. Applied certificate
expressions use ordinary Lean elaboration. Explicit selection never falls back
to another rule, and a namespace by itself gives a declaration no priority.

Unconditional exact records may introduce auxiliaries. Conic consumers can
also discharge input-domain obligations from retained constraints under their
existing margin policy, but only for replacements without auxiliaries. NLP
exactness is unconditional; retained and generated rows can still justify the
evaluation domains of the resulting smooth residuals.
-/

namespace Morew.Elab.Rewrite.Registry

open Lean Lean.Meta

/-- The two consumers of exact representation declarations. -/
inductive Target where
  | conic | nlp
  deriving BEq, Inhabited

/-- The source orientation recorded by a representation. -/
inductive Family where
  | exact | graph | epigraph | hypograph
  deriving BEq, Inhabited, Repr

/-- Closed lookup data; actual types and certificates are checked on every use. -/
structure Entry where
  /-- The fully qualified declaration to instantiate and check. -/
  declaration : Name
  /-- The certificate family and source orientation. -/
  family : Family
  /-- The fixed operation or complete-predicate head. -/
  head : Name
  /-- A fixed output-type head, or a wildcard for generic output types. -/
  outputHead? : Option Name := none
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

private def entry (declaration : Name) : MetaM Entry := do
  let type := (← getConstInfo declaration).type
  forallTelescopeReducing type fun _ body => do
    let body ← whnf body
    let (family, input, represented) ← representation body
    let outputHead? ← if family == .exact then pure none else do
      let output ← whnf body.getAppArgs[1]!
      pure output.getAppFn.constName?
    withLocalDeclD `input input fun input => do
      let body ← structural (mkApp represented input)
      let .const head _ := body.getAppFn
        | throwError "cannot register {declaration}: the represented source has no fixed operation head: {body}; reduced type is {← whnf (← inferType (← mkConstWithFreshMVarLevels declaration))}"
      let head := if family == .exact && head == ``GE.ge then ``LE.le else head
      return { declaration, family, head, outputHead? }

private def makeExtension (name : Name) : IO (SimpleScopedEnvExtension Entry (Array Entry)) :=
  registerSimpleScopedEnvExtension {
    name, initial := #[]
    addEntry := fun entries value =>
      if entries.any (·.declaration == value.declaration) then entries else entries.push value }

/-- Scoped persistent registrations for the conic consumer. -/
initialize conicExtension : SimpleScopedEnvExtension Entry (Array Entry) ←
  makeExtension `morewConicRegistry

/-- Scoped persistent registrations for the smooth-NLP consumer. -/
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

private def operationHead? (expression : Expr) : MetaM (Option Name) := do
  let expression ← structural expression
  return match expression.getAppFn with
    | .const name _ => some name
    | _ => none

/-- Discover only source-head/orientation-compatible declarations. Matching and
target certification still run before a candidate can be accepted. -/
def candidates (target : Target) (source : Expr) : MetaM (Array Name) := do
  let type ← whnf (← inferType source)
  let .forallE _ domain _ _ := type | throwError "expected a constraint predicate"
  withLocalDeclD `point domain fun point => do
    let body ← structural (mkApp source point)
    let sourceHead ← operationHead? body
    let sourceHead := if sourceHead == some ``GE.ge then some ``LE.le else sourceHead
    let args := body.getAppArgs
    let mut epi := none
    let mut hypo := none
    let mut graphLeft := none
    let mut graphRight := none
    let mut outputHead? := none
    if body.isAppOfArity ``LE.le 4 then
      outputHead? := (← whnf args[0]!).getAppFn.constName?
      epi ← operationHead? args[2]!
      hypo ← operationHead? args[3]!
    else if body.isAppOfArity ``GE.ge 4 then
      outputHead? := (← whnf args[0]!).getAppFn.constName?
      epi ← operationHead? args[3]!
      hypo ← operationHead? args[2]!
    else if body.isAppOfArity ``Eq 3 then
      outputHead? := (← whnf args[0]!).getAppFn.constName?
      graphLeft ← operationHead? args[1]!
      graphRight ← operationHead? args[2]!
    return (← entries target).filterMap fun entry =>
      let compatible := match entry.family with
        | .exact => sourceHead == some entry.head
        | .epigraph => epi == some entry.head
        | .hypograph => hypo == some entry.head
        | .graph => graphLeft == some entry.head || graphRight == some entry.head
      let compatibleType := match entry.outputHead?, outputHead? with
        | some expected, some actual => expected == actual
        | _, _ => true
      if compatible && compatibleType then some entry.declaration else none

end Morew.Elab.Rewrite.Registry
