/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Basic
import Morew.Elab.Affine.Space
import Lean.Meta.Basic
import Qq

/-!
# Canonical normed and ordered spaces for affine rows

Row constructors fix their normed structures and coordinatewise real order
explicitly, independently of unrelated instances in the caller's context.
-/

namespace Morew.Elab.Conic.Space

open Lean Lean.Meta Qq

/-- The canonical normed structures chosen for a row's decision domain. -/
structure Structure (X : Type*) where
  /-- The chosen normed additive group. -/
  group : NormedAddCommGroup X
  /-- Real scalar multiplication for the chosen normed group. -/
  space : @NormedSpace ℝ X inferInstance group.toSeminormedAddCommGroup
  /-- Finite dimension for precisely the chosen additive and scalar structures. -/
  finite : @FiniteDimensional ℝ X inferInstance group.toAddCommGroup space.toModule

namespace Structure

-- These constructors are reducible because their projections occur in the
-- types of persisted forms. Later field notation must recognize the same
-- canonical instances using typeclass search's restricted transparency.

/-- Standard real normed structures, resolved in this fixed context. -/
noncomputable abbrev real : Structure ℝ := ⟨inferInstance, inferInstance, inferInstance⟩

/-- Standard finite Euclidean normed structures, independent of ambient instances. -/
noncomputable abbrev euclidean (n : ℕ) : Structure (EuclideanSpace ℝ (Fin n)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Product normed structures from two explicitly supplied factors. -/
noncomputable abbrev prod {X Y : Type*} (a : Structure X) (b : Structure Y) :
    Structure (X × Y) := by
  letI := a.group
  letI := a.space
  letI := a.finite
  letI := b.group
  letI := b.space
  letI := b.finite
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Finite function-space normed structures from the supplied range. -/
noncomputable abbrev pi (ι : Type*) [Fintype ι] {Y : Type*} (a : Structure Y) :
    Structure (ι → Y) := by
  letI := a.group
  letI := a.space
  letI := a.finite
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Structure

-- Preserve aliases such as Matrix in local instance types, just as the affine
-- algebra builder does. Typeclass matching need not unfold those aliases.
private def finishSpace (type data : Expr) : MetaM Expr := do
  let dataType ← mkAppM ``Structure #[type]
  mkAppOptM ``id #[some dataType, some data]

private partial def buildSpace (type : Expr) : MetaM Expr := do
  let shape ← whnf type
  if shape.isConstOf ``Real then
    finishSpace type (mkConst ``Structure.real)
  else if let some n ← Affine.Space.euclideanDimension? shape then
    finishSpace type (← mkAppM ``Structure.euclidean #[n])
  else if shape.isAppOfArity ``Prod 2 then
    let left ← buildSpace shape.getAppArgs[0]!
    let right ← buildSpace shape.getAppArgs[1]!
    finishSpace type (← mkAppM ``Structure.prod #[left, right])
  else if let .forallE _ index body _ := shape then
    let body ← Core.betaReduce (← whnf body)
    if body.hasLooseBVars || (← isProp index) then
      throwError "affine rows require a nondependent function space, got {type}"
    let target ← buildSpace body
    let fintypeType ← mkAppM ``Fintype #[index]
    let fintype ← match ← trySynthInstance fintypeType with
      | .some inst => pure inst
      | _ => mkAppOptM ``Fintype.ofFinite #[some index, none]
    let data ← mapLetDeclZeta `_rowIndex fintypeType fintype fun _ =>
      mkAppM ``Structure.pi #[index, target]
    finishSpace type data
  else
    throwError "unsupported affine row domain {type}"

/-- Expose structural decision-space aliases in a persisted form's type.
For example, instance synthesis recognizes `Fin m → Fin n → ℝ`, whereas it
need not unfold the semireducible `Matrix` alias. This changes neither the
represented problem nor its presentation's decision-domain spelling. -/
partial def structuralDomain (type : Expr) : MetaM Expr := do
  let shape ← whnf type
  if shape.isConstOf ``Real then
    return shape
  if let some dimension ← Affine.Space.euclideanDimension? shape then
    let n : Q(Nat) := dimension
    return q(EuclideanSpace ℝ (Fin $n))
  if shape.isAppOfArity ``Prod 2 then
    return ← mkAppM ``Prod #[← structuralDomain shape.getAppArgs[0]!,
      ← structuralDomain shape.getAppArgs[1]!]
  if let .forallE _ index body _ := shape then
    let body ← Core.betaReduce (← whnf body)
    if body.hasLooseBVars || (← isProp index) then
      throwError "affine rows require a nondependent function space, got {type}"
    -- Index aliases can carry their own Fintype instance. Preserve that spelling
    -- so projections synthesize the same enumeration as the stored norm.
    return ← mkArrow index (← structuralDomain body)
  throwError "unsupported affine row domain {type}"

private def realInstances : Array Expr := #[
  q(inferInstance : NormedAddCommGroup ℝ),
  q(inferInstance : NormedSpace ℝ ℝ),
  q(inferInstance : FiniteDimensional ℝ ℝ),
  q(inferInstance : PartialOrder ℝ),
  q(inferInstance : IsOrderedAddMonoid ℝ),
  q(inferInstance : PosSMulMono ℝ ℝ)]

private def targetInstances (type : Expr) : MetaM (Array Expr) := do
  let shape ← whnf type
  if shape.isConstOf ``Real then return realInstances
  let .forallE _ index body _ := shape | throwError "unsupported affine row target {type}"
  unless (← whnf body).isConstOf ``Real do
    throwError "unsupported affine row target {type}"
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 do
    throwError "unsupported affine row target {type}"
  let n : Q(Nat) := index.getAppArgs[0]!
  return #[
    q(inferInstance : NormedAddCommGroup (Fin $n → ℝ)),
    q(inferInstance : NormedSpace ℝ (Fin $n → ℝ)),
    q(inferInstance : FiniteDimensional ℝ (Fin $n → ℝ)),
    q(inferInstance : PartialOrder (Fin $n → ℝ)),
    q(inferInstance : IsOrderedAddMonoid (Fin $n → ℝ)),
    q(inferInstance : PosSMulMono ℝ (Fin $n → ℝ))]

private def installInstances (remaining : List Expr)
    (action : MetaM (Expr × Expr)) : MetaM (Expr × Expr) := do
  match remaining with
  | [] =>
      let (row, proof) ← action
      return (← instantiateMVars row, ← instantiateMVars proof)
  | inst :: rest =>
      withLetDecl `_rowCanonical (← inferType inst) inst fun binding => do
        let (row, proof) ← installInstances rest action
        return (← row.replaceFVarsM #[binding] #[inst],
          ← proof.replaceFVarsM #[binding] #[inst])

/-- Construct a row and its equivalence proof with canonical normed and ordered
structures. Substitute the temporary instances before either expression escapes.
Only finite-index evidence is synthesized from the caller's context. -/
def withCanonicalSpaces (domain target : Expr)
    (action : MetaM (Expr × Expr)) : MetaM (Expr × Expr) := do
  let data ← buildSpace domain
  let group ← mkAppM ``Structure.group #[data]
  let space ← mkAppM ``Structure.space #[data]
  let instances := realInstances ++ #[group, space] ++ (← targetInstances target)
  installInstances instances.toList action

/-- Construct a cone-membership row using canonical normed structures on its
coordinate space. Cone coordinates need no order structure. -/
def withCanonicalConeSpaces (domain target : Expr)
    (action : MetaM (Expr × Expr)) : MetaM (Expr × Expr) := do
  let domainData ← buildSpace domain
  let targetData ← buildSpace target
  let instances := realInstances ++ #[
    ← mkAppM ``Structure.group #[domainData],
    ← mkAppM ``Structure.space #[domainData],
    ← mkAppM ``Structure.group #[targetData],
    ← mkAppM ``Structure.space #[targetData],
    ← mkAppM ``Structure.finite #[targetData]]
  installInstances instances.toList action

/-- Build a complete form with canonical finite-dimensional decision structures.
The recursive finite-dimensional proof uses the same structures as the affine
maps, even in the presence of unrelated ambient instances. -/
def withCanonicalDomain (domain : Expr) (action : MetaM Expr) : MetaM Expr := do
  let data ← buildSpace domain
  let instances := realInstances ++ #[
    ← mkAppM ``Structure.group #[data],
    ← mkAppM ``Structure.space #[data],
    ← mkAppM ``Structure.finite #[data]]
  let (result, _) ← installInstances instances.toList do
    let result ← action
    return (result, result)
  return result

end Morew.Elab.Conic.Space
