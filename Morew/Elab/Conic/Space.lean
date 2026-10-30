/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Basic
import Morew.Elab.Affine.Space
import Morew.Elab.Expr
import Lean.Meta.Basic
import Qq

/-!
# Canonical decision and cone-coordinate spaces for affine rows

Decision spaces use the affine reifier's algebraic structures. Cone coordinates
retain their normed structures and coordinatewise real order. Both are fixed
explicitly, independently of unrelated instances in the caller's context.
-/

namespace Morew.Elab.Conic.Space

open Lean Lean.Meta Qq

/-- Canonical finite-dimensional algebra for a form's decision domain. -/
structure Domain (X : Type*) where
  /-- Exactly the algebra used by certified affine maps. -/
  algebra : Affine.Space.Structure X
  /-- Finite dimension for this additive group and scalar multiplication. -/
  finite : @FiniteDimensional ℝ X inferInstance algebra.group algebra.module

namespace Domain

/-- Standard real algebra and its finite dimension. -/
noncomputable abbrev real : Domain ℝ := ⟨Affine.Space.Structure.real, inferInstance⟩

/-- Standard finite Euclidean algebra. -/
noncomputable abbrev euclidean (n : ℕ) : Domain (EuclideanSpace ℝ (Fin n)) :=
  ⟨Affine.Space.Structure.euclidean n, inferInstance⟩

/-- Algebra on the named symmetric-matrix submodule. -/
noncomputable abbrev symmetricMatrix (n : ℕ) : Domain (Morew.Conic.SymmetricMatrix n) :=
  ⟨Affine.Space.Structure.symmetricMatrix n, inferInstance⟩

/-- Product algebra with finiteness proved for the supplied component structures. -/
noncomputable abbrev prod {X Y : Type*} (a : Domain X) (b : Domain Y) :
    Domain (X × Y) where
  algebra := Affine.Space.Structure.prod a.algebra b.algebra
  finite := by
    let := a.algebra.group
    let := a.algebra.module
    let := a.finite
    let := b.algebra.group
    let := b.algebra.module
    let := b.finite
    exact inferInstance

/-- Finite function-space algebra requires no enumeration or ambient norm. -/
noncomputable abbrev pi (ι : Type*) [Finite ι] {Y : Type*} (a : Domain Y) :
    Domain (ι → Y) where
  algebra := Affine.Space.Structure.pi ι a.algebra
  finite := by
    let := a.algebra.group
    let := a.algebra.module
    let := a.finite
    exact inferInstance

end Domain

private def finishDomain (type data : Expr) : MetaM Expr := do
  let dataType ← mkAppM ``Domain #[type]
  mkAppOptM ``id #[some dataType, some data]

private partial def buildDomain (type : Expr) : MetaM Expr := do
  if let some n ← Expr.symmetricMatrixDimension? type then
    return ← finishDomain type (← mkAppM ``Domain.symmetricMatrix #[n])
  let shape ← whnf type
  if shape.isConstOf ``Real then
    finishDomain type (mkConst ``Domain.real)
  else if let some n ← Expr.euclideanDimension? shape then
    finishDomain type (← mkAppM ``Domain.euclidean #[n])
  else if shape.isAppOfArity ``Prod 2 then
    let left ← buildDomain shape.getAppArgs[0]!
    let right ← buildDomain shape.getAppArgs[1]!
    finishDomain type (← mkAppM ``Domain.prod #[left, right])
  else if let .forallE _ index body _ := shape then
    let body ← Core.betaReduce (← whnf body)
    if body.hasLooseBVars || (← isProp index) then
      throwError "affine rows require a nondependent function space, got {type}"
    let target ← buildDomain body
    finishDomain type (← mkAppM ``Domain.pi #[index, target])
  else
    throwError "unsupported affine row domain {type}"

/-- The canonical normed structures chosen for cone coordinates. -/
structure Structure (X : Type*) where
  /-- The chosen normed additive group. -/
  group : NormedAddCommGroup X
  /-- Real scalar multiplication for the chosen normed group. -/
  space : @NormedSpace ℝ X inferInstance group.toSeminormedAddCommGroup
  /-- Finite dimension for precisely the chosen additive and scalar structures. -/
  finite : @FiniteDimensional ℝ X inferInstance group.toAddCommGroup space.toModule

namespace Structure

-- Coordinate instances must remain recognizable by instance search.

/-- Standard real normed structures, resolved in this fixed context. -/
noncomputable abbrev real : Structure ℝ := ⟨inferInstance, inferInstance, inferInstance⟩

/-- Standard finite Euclidean normed structures, independent of ambient instances. -/
noncomputable abbrev euclidean (n : ℕ) : Structure (EuclideanSpace ℝ (Fin n)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The symmetric submodule inherits the fixed nested-function matrix norm. -/
noncomputable abbrev symmetricMatrix (n : ℕ) : Structure (Morew.Conic.SymmetricMatrix n) :=
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
  if let some n ← Expr.symmetricMatrixDimension? type then
    return ← finishSpace type (← mkAppM ``Structure.symmetricMatrix #[n])
  let shape ← whnf type
  if shape.isConstOf ``Real then
    finishSpace type (mkConst ``Structure.real)
  else if let some n ← Expr.euclideanDimension? shape then
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
  if let some n ← Expr.symmetricMatrixDimension? type then
    return ← mkAppM ``Morew.Conic.SymmetricMatrix #[n]
  let shape ← whnf type
  if shape.isConstOf ``Real then
    return shape
  if let some dimension ← Expr.euclideanDimension? shape then
    let n : Q(Nat) := dimension
    return q(EuclideanSpace ℝ (Fin $n))
  if shape.isAppOfArity ``Prod 2 then
    return ← mkAppM ``Prod #[← structuralDomain shape.getAppArgs[0]!,
      ← structuralDomain shape.getAppArgs[1]!]
  if let .forallE _ index body _ := shape then
    let body ← Core.betaReduce (← whnf body)
    if body.hasLooseBVars || (← isProp index) then
      throwError "affine rows require a nondependent function space, got {type}"
    -- Index aliases can carry their own finiteness evidence. Preserve that spelling.
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

/-- Construct a row with canonical decision algebra and normed, ordered targets.
Substitute the temporary instances before either expression escapes. -/
def withCanonicalSpaces (domain target : Expr)
    (action : MetaM (Expr × Expr)) : MetaM (Expr × Expr) := do
  let (group, module) ← Affine.Space.canonicalSpace domain
  let instances := realInstances ++ #[group, module] ++ (← targetInstances target)
  installInstances instances.toList action

/-- Construct a cone-membership row using canonical normed structures on its
coordinate space. Cone coordinates need no order structure. -/
def withCanonicalConeSpaces (domain target : Expr)
    (action : MetaM (Expr × Expr)) : MetaM (Expr × Expr) := do
  let (group, module) ← Affine.Space.canonicalSpace domain
  let targetData ← buildSpace target
  let instances := realInstances ++ #[
    group, module,
    ← mkAppM ``Structure.group #[targetData],
    ← mkAppM ``Structure.space #[targetData],
    ← mkAppM ``Structure.finite #[targetData]]
  installInstances instances.toList action

/-- Build a complete form with canonical finite-dimensional decision structures.
The recursive finite-dimensional proof uses the same structures as the affine
maps, even in the presence of unrelated ambient instances. -/
def withCanonicalDomain (domain : Expr) (action : MetaM Expr) : MetaM Expr := do
  let data ← buildDomain domain
  let algebra ← mkAppM ``Domain.algebra #[data]
  let instances := #[
    q(inferInstance : AddCommGroup ℝ), q(inferInstance : Module ℝ ℝ),
    ← mkAppM ``Affine.Space.Structure.group #[algebra],
    ← mkAppM ``Affine.Space.Structure.module #[algebra],
    ← mkAppM ``Domain.finite #[data]]
  let (result, _) ← installInstances instances.toList do
    let result ← action
    return (result, result)
  return result

end Morew.Elab.Conic.Space
