/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Morew.Elab.Expr
import Lean.Meta.Basic

/-! Canonical normed structures and finite-dimensionality for real, Euclidean,
product, and finite-function spaces. -/

namespace Morew.Elab.NLP.Space

open Lean Lean.Meta

universe u v

/-- Compatible standard normed structures and their finite-dimensionality proof. -/
structure Structure (X : Type u) where
  /-- The chosen normed additive group. -/
  group : NormedAddCommGroup X
  /-- Real scalar multiplication for that normed additive group. -/
  space : @NormedSpace ℝ X inferInstance group.toSeminormedAddCommGroup
  /-- Finite dimensionality for precisely those additive and scalar structures. -/
  finite : @FiniteDimensional ℝ X inferInstance group.toAddCommGroup space.toModule

namespace Structure

/-- Standard real structures, fixed in this declaration's context. -/
noncomputable abbrev real : Structure ℝ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Standard finite Euclidean structures, fixed independently of ambient instances. -/
noncomputable abbrev euclidean (n : Nat) : Structure (EuclideanSpace ℝ (Fin n)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Standard product structures assembled from the supplied component structures. -/
noncomputable abbrev prod {X : Type u} {Y : Type v}
    (left : Structure X) (right : Structure Y) : Structure (X × Y) := by
  letI := left.group
  letI := left.space
  letI := left.finite
  letI := right.group
  letI := right.space
  letI := right.finite
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Standard finite-vector structures, including zero-length vectors. -/
noncomputable abbrev pi (n : Nat) {Y : Type u} (target : Structure Y) :
    Structure (Fin n → Y) := by
  letI := target.group
  letI := target.space
  letI := target.finite
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Structure

-- Fix the scalar field to the standard real field.
private noncomputable abbrev realField : NontriviallyNormedField ℝ := inferInstance

private structure BuiltSpace where
  data : Expr
  instances : Array Expr

private def finishSpace (type data : Expr) (components : Array Expr := #[]) :
    MetaM BuiltSpace := do
  -- Preserve aliases in local instance types for typeclass matching.
  let dataType ← mkAppM ``Structure #[type]
  let data ← mkAppOptM ``id #[some dataType, some data]
  let group ← mkAppM ``Structure.group #[data]
  let space ← mkAppM ``Structure.space #[data]
  let finite ← mkAppM ``Structure.finite #[data]
  return { data, instances := components ++ #[group, space, finite] }

private partial def buildSpace (type : Expr) : MetaM BuiltSpace := do
  let shape ← whnf type
  if shape.isConstOf ``Real then
    finishSpace type (mkConst ``Structure.real)
  else if let some n ← Expr.euclideanDimension? shape then
    let coordinates ← buildSpace (← mkArrow (← mkAppM ``Fin #[n]) (mkConst ``Real))
    let data ← mkAppM ``Structure.euclidean #[n]
    finishSpace type data coordinates.instances
  else if shape.isAppOfArity ``Prod 2 then
    let left ← buildSpace shape.getAppArgs[0]!
    let right ← buildSpace shape.getAppArgs[1]!
    let data ← mkAppM ``Structure.prod #[left.data, right.data]
    finishSpace type data (left.instances ++ right.instances)
  else if let .forallE name index body info := shape then
    let indexShape ← whnf index
    unless indexShape.isAppOfArity ``Fin 1 do
      throwError "smooth certification requires a Fin n function index, got {type}"
    withLocalDecl name info index fun i => do
      let body ← Core.betaReduce (← whnf (body.instantiate1 i))
      if body.containsFVar i.fvarId! then
        throwError "smooth certification requires a nondependent finite function space, got {type}"
      let target ← buildSpace body
      let data ← mkAppM ``Structure.pi #[indexShape.getAppArgs[0]!, target.data]
      -- Use `Structure.pi`'s `Fin` enumeration for componentwise calculus.
      let fintype ← mkAppM ``Fin.fintype #[indexShape.getAppArgs[0]!]
      let fintypeType ← mkAppM ``Fintype #[index]
      let fintype ← mkAppOptM ``id #[some fintypeType, some fintype]
      finishSpace type data (target.instances.push fintype)
  else
    throwError "unsupported smooth decision or value space {type}; expected ℝ, a finite Euclidean space, a product, or a Fin n function space"

private def installInstances (remaining : List Expr) (action : MetaM Expr) : MetaM Expr := do
  match remaining with
  | [] => instantiateMVars (← action)
  | inst :: rest =>
    mapLetDeclZeta `_smoothCanonical (← inferType inst) inst fun _ =>
      installInstances rest action

/-- Use canonical analytic structures on supplied spaces, their components, and `ℝ`.
Use the matching `Fin` enumeration and substitute temporary instances into the result. -/
def withCanonicalSpaces (types : Array Expr) (action : MetaM Expr) : MetaM Expr := do
  let mut instances := #[mkConst ``realField]
  for type in #[mkConst ``Real] ++ types do
    let result ← buildSpace type
    for inst in result.instances do
      unless instances.contains inst do
        instances := instances.push inst
  installInstances instances.toList action

end Morew.Elab.NLP.Space
