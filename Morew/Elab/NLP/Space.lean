/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Lean.Meta.Basic

/-!
# Canonical analytic structures for smoothness certification

The supported real, product, and finite-function spaces use their standard
normed structures. These structures and their finite-dimensionality evidence
are assembled together, independently of unrelated ambient instances.
-/

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

-- Fix the scalar field at declaration time, just as Structure.real fixes its
-- analytic structures. Ambient field instances need not agree with those data.
private noncomputable abbrev realField : NontriviallyNormedField ℝ := inferInstance

private structure BuiltSpace where
  data : Expr
  instances : Array Expr

private def finishSpace (type data : Expr) (components : Array Expr := #[]) :
    MetaM BuiltSpace := do
  -- Preserve aliases in the local instance types, so typeclass matching need
  -- not unfold their spelling merely to find an already constructed instance.
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
  else if shape.isAppOfArity ``Prod 2 then
    let left ← buildSpace shape.getAppArgs[0]!
    let right ← buildSpace shape.getAppArgs[1]!
    let data ← mkAppM ``Structure.prod #[left.data, right.data]
    finishSpace type data (left.instances ++ right.instances)
  else if let .forallE _ index body _ := shape then
    let body ← Core.betaReduce (← whnf body)
    if body.hasLooseBVars then
      throwError "smooth certification requires a nondependent finite function space, got {type}"
    let indexShape ← whnf index
    unless indexShape.isAppOfArity ``Fin 1 do
      throwError "smooth certification requires a Fin n function index, got {type}"
    let target ← buildSpace body
    let data ← mkAppM ``Structure.pi #[indexShape.getAppArgs[0]!, target.data]
    -- Projection and componentwise calculus lemmas carry their own Fintype
    -- argument. Keep it aligned with the enumeration chosen by Structure.pi;
    -- source operations still retain their original explicit finite sets.
    let fintype ← mkAppM ``Fin.fintype #[indexShape.getAppArgs[0]!]
    let fintypeType ← mkAppM ``Fintype #[index]
    let fintype ← mkAppOptM ``id #[some fintypeType, some fintype]
    finishSpace type data (target.instances.push fintype)
  else
    throwError "unsupported smooth decision or value space {type}; expected ℝ, a product, or a Fin n function space"

private def installInstances (remaining : List Expr) (action : MetaM Expr) : MetaM Expr := do
  match remaining with
  | [] => instantiateMVars (← action)
  | inst :: rest =>
    mapLetDeclZeta `_smoothCanonical (← inferType inst) inst fun _ =>
      installInstances rest action

/-- Construct a proof using canonical analytic structures on the supplied spaces.

The scalar field is fixed to the standard real field. The real scalars and
every component space receive canonical normed-group,
normed-space, and finite-dimensionality instances. Finite-function calculus uses
the matching standard Fin enumeration. Temporary instances are substituted into
the returned expression before leaving their scopes.
-/
def withCanonicalSpaces (types : Array Expr) (action : MetaM Expr) : MetaM Expr := do
  let mut instances := #[mkConst ``realField]
  for type in #[mkConst ``Real] ++ types do
    let result ← buildSpace type
    for inst in result.instances do
      unless instances.contains inst do
        instances := instances.push inst
  installInstances instances.toList action

end Morew.Elab.NLP.Space
