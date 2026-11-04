/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform.Parameterization
import Morew.Elab.Rewrite.Registry

/-! Register coordinate parameterizations through `morew_substitute` with Lean attribute scope.
Store discovery metadata; matching checks complete maps and operation instances. -/

namespace Morew.Elab.Substitution.Registry

open Lean Lean.Meta

/-- Discovery key; the bare fresh coordinate has its own identity case. -/
inductive Key where
  | identity
  | operation (head : Name)
  deriving BEq, Inhabited

/-- Discovery metadata for a parameterization declaration. -/
structure Entry where
  /-- The registered declaration. -/
  declaration : Name
  /-- The identity shape or fixed mathematical operation head. -/
  key : Key
  deriving BEq, Inhabited

/-- Reduce binding syntax while preserving named mathematical functions. -/
abbrev structural := Morew.Elab.Rewrite.Registry.structural

/-- Read the retained, new, and old types and complete coordinate map. -/
def parameterization (type : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let type ← whnf type
  unless type.isAppOfArity ``Morew.CoordinateParameterization 4 do
    throwError "expected CoordinateParameterization; reduced type is {type}"
  let args := type.getAppArgs
  return (args[0]!, args[1]!, args[2]!, args[3]!)

private def mapKey? (map : Expr) : MetaM (Option Key) := do
  let type ← whnf (← inferType map)
  let .forallE _ retainedType _ _ := type
    | throwError "expected a map from retained and new coordinates"
  withLocalDeclD `retained retainedType fun retained => do
    let type ← whnf (← inferType (mkApp map retained))
    let .forallE _ newType _ _ := type
      | throwError "expected a map from retained and new coordinates"
    withLocalDeclD `coordinate newType fun coordinate => do
      let body ← structural (mkApp2 map retained coordinate)
      if body == coordinate then return some .identity
      return body.getAppFn.constName?.map Key.operation

private def entry (declaration : Name) : MetaM Entry := do
  forallTelescopeReducing (← getConstInfo declaration).type fun _ type => do
    let (_, _, _, map) ← parameterization type
    let some key ← mapKey? map
      | throwError "cannot register {declaration}: the coordinate map must be identity or have a fixed operation head"
    return { declaration, key }

/-- Persistent scoped parameterization declarations. -/
initialize extension : SimpleScopedEnvExtension Entry (Array Entry) ←
  registerSimpleScopedEnvExtension {
    name := `morewSubstitutionRegistry
    initial := #[]
    addEntry := fun entries value =>
      if entries.any (·.declaration == value.declaration) then entries else entries.push value }

initialize registerBuiltinAttribute {
  name := `morew_substitute
  descr := "checked coordinate parameterization"
  applicationTime := .afterCompilation
  add := fun declaration stx kind => MetaM.run' do
    Attribute.Builtin.ensureNoArgs stx
    extension.add (← entry declaration) kind
  erase := fun declaration =>
    modifyEnv fun env => extension.modifyState env fun entries =>
      entries.filter (·.declaration != declaration) }

/-- Active declarations sorted independently of registration and import order. -/
def entries : CoreM (Array Entry) := do
  return (extension.getState (← getEnv)).qsort fun a b =>
    a.declaration.toString < b.declaration.toString

/-- Discover map shapes for later type, instance, premise, and coverage checks. -/
def candidates (map : Expr) : MetaM (Array Name) := do
  let some key ← mapKey? map | return #[]
  return (← entries).filterMap fun entry =>
    if entry.key == key then some entry.declaration else none

end Morew.Elab.Substitution.Registry
