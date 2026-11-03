/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform.Parameterization
import Lean.Meta

/-! Separate a selected coordinate from retained coordinates in original order.
Use left-associated products, with Unit for no retained coordinates. -/

namespace Morew.Elab.Substitution.Coordinates

open Lean Lean.Meta

/-- Pack components into a left-associated product, or `()` for no components. -/
def pack (components : Array Expr) : MetaM Expr := do
  if h : components.size > 0 then
    let mut point := components[0]
    for index in [1:components.size] do
      point ← mkAppM ``Prod.mk #[point, components[index]!]
    return point
  return mkConst ``Unit.unit

/-- Construct the type of a left-associated tuple, using `Unit` for an empty tuple. -/
def productType (types : Array Expr) : MetaM Expr := do
  if h : types.size > 0 then
    let mut result := types[0]
    for index in [1:types.size] do
      result ← mkAppM ``Prod #[result, types[index]!]
    return result
  return mkConst ``Unit

/-- Project one coordinate from a left-associated tuple of the given size. -/
partial def project (point : Expr) (index count : Nat) : MetaM Expr := do
  if count == 0 || index >= count then
    throwError "invalid substitution coordinate {index} in a tuple of size {count}"
  if count == 1 then return point
  if index + 1 == count then return ← mkAppM ``Prod.snd #[point]
  project (← mkAppM ``Prod.fst #[point]) index (count - 1)

/-- Construct a checked coordinate-separation equivalence for the presented tuple domain,
including type aliases. -/
def split (domain : Expr) (binderTypes : Array Expr) (selected : Nat) : MetaM Expr := do
  if selected >= binderTypes.size then
    throwError "invalid substitution coordinate {selected} in a tuple of size {binderTypes.size}"
  unless ← isDefEq domain (← productType binderTypes) do
    throwError "substitution binder types do not match the current decision domain"
  let retainedTypes := binderTypes.extract 0 selected ++ binderTypes.extract (selected + 1)
  let retainedType ← productType retainedTypes
  let selectedType := binderTypes[selected]!
  let target ← mkAppM ``Prod #[retainedType, selectedType]
  let toFun ← withLocalDeclD `point domain fun point => do
    let mut retained := #[]
    for index in [:binderTypes.size] do
      if index != selected then
        retained := retained.push (← project point index binderTypes.size)
    let result ← mkAppM ``Prod.mk
      #[← pack retained, ← project point selected binderTypes.size]
    mkLambdaFVars #[point] result
  let invFun ← withLocalDeclD `point target fun point => do
    let retained ← mkAppM ``Prod.fst #[point]
    let coordinate ← mkAppM ``Prod.snd #[point]
    let mut components := #[]
    for index in [:binderTypes.size] do
      if index == selected then
        components := components.push coordinate
      else
        let retainedIndex := if index < selected then index else index - 1
        components := components.push
          (← project retained retainedIndex retainedTypes.size)
    mkLambdaFVars #[point] (← pack components)
  let leftInverse ← withLocalDeclD `point domain fun point => do
    mkLambdaFVars #[point] (← mkEqRefl point)
  let rightInverse ← withLocalDeclD `point target fun point => do
    let proof ← if retainedTypes.isEmpty then do
      let reconstructed := mkApp toFun (mkApp invFun point)
      let unitEq ← mkAppM ``Subsingleton.elim
        #[mkConst ``Unit.unit, ← mkAppM ``Prod.fst #[point]]
      let coordinateEq ← mkEqRefl (← mkAppM ``Prod.snd #[point])
      mkAppOptM ``Prod.ext #[some retainedType, some selectedType,
        some reconstructed, some point, some unitEq, some coordinateEq]
    else
      mkEqRefl point
    mkLambdaFVars #[point] proof
  let result ← mkAppM ``Equiv.mk #[toFun, invFun, leftInverse, rightInverse]
  let result ← instantiateMVars result
  checkWithKernel result
  return result

end Morew.Elab.Substitution.Coordinates
