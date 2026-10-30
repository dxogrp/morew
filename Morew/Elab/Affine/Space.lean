/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Affine
import Morew.Elab.Expr
import Lean.Meta.Basic
import Lean.Meta.Transform
import Qq

/-!
# Canonical real vector-space structures for affine reification

This internal module builds standard real, Euclidean, product, and function-space
structures explicitly. Ambient local instances therefore cannot change the
meaning of a certified affine construction. Finiteness of function indices is
checked by the caller; it is not needed to construct their algebraic structures.
-/

namespace Morew.Elab.Affine.Space

open Lean Lean.Meta Qq

/-- A real vector-space structure with its additive group fixed explicitly. -/
structure Structure (X : Type*) where
  /-- The chosen additive group, independent of ambient instances. -/
  group : AddCommGroup X
  /-- Real scalar multiplication compatible with that additive group. -/
  module : @Module ℝ X _ group.toAddCommMonoid

namespace Structure

-- Persisted conic forms expose these structures in their public types. Keep
-- them reducible so ordinary instance search recognizes the canonical algebra.

/-- Standard real structures, resolved in this declaration's fixed context. -/
noncomputable abbrev real : Structure ℝ where
  group := inferInstance
  module := inferInstance

/-- Standard finite Euclidean structures, fixed independently of local instances. -/
noncomputable abbrev euclidean (n : ℕ) : Structure (EuclideanSpace ℝ (Fin n)) where
  group := inferInstance
  module := inferInstance

/-- Canonical structures on the named symmetric-matrix submodule. -/
noncomputable abbrev symmetricMatrix (n : ℕ) : Structure (Morew.Conic.SymmetricMatrix n) where
  group := inferInstance
  module := inferInstance

/-- The standard product structures on two explicitly supplied spaces. -/
noncomputable abbrev prod {X Y : Type*} (a : Structure X) (b : Structure Y) :
    Structure (X × Y) where
  group := @Prod.instAddCommGroup X Y a.group b.group
  module := @Prod.instModule ℝ X Y inferInstance
    a.group.toAddCommMonoid b.group.toAddCommMonoid a.module b.module

/-- The standard pointwise structures on a nondependent function space. -/
noncomputable abbrev pi (ι : Type*) {Y : Type*} (a : Structure Y) :
    Structure (ι → Y) where
  group := @Pi.addCommGroup ι (fun _ => Y) (fun _ => a.group)
  module := @Pi.module ι (fun _ => Y) ℝ inferInstance
    (fun _ => a.group.toAddCommMonoid) (fun _ => a.module)

end Structure

private structure BuiltSpace where
  data : Expr
  instances : Array Expr

private def finishSpace (type data : Expr) (instances : Array Expr := #[]) :
    MetaM BuiltSpace := do
  -- Keep aliases such as `Matrix` in the inferred instance types. Instance
  -- synthesis need not unfold these aliases when matching a local instance.
  let dataType ← mkAppM ``Structure #[type]
  let data ← mkAppOptM ``id #[some dataType, some data]
  let group ← mkAppM ``Structure.group #[data]
  let module ← mkAppM ``Structure.module #[data]
  pure { data, instances := instances ++ #[group, module] }

private partial def buildSpace (type : Expr) : MetaM BuiltSpace := do
  if let some n ← Expr.symmetricMatrixDimension? type then
    return ← finishSpace type (← mkAppM ``Structure.symmetricMatrix #[n])
  -- This reduction concerns types only, so aliases such as `Matrix` can expose
  -- their product/function structure. It never unfolds a modeled expression.
  let shape ← whnf type
  if shape.isConstOf ``Real then
    finishSpace type (mkConst ``Structure.real)
  else if let some n ← Expr.euclideanDimension? shape then
    finishSpace type (← mkAppM ``Structure.euclidean #[n])
  else if shape.isAppOfArity ``Prod 2 then
    let left ← buildSpace shape.getAppArgs[0]!
    let right ← buildSpace shape.getAppArgs[1]!
    let data ← mkAppM ``Structure.prod #[left.data, right.data]
    finishSpace type data (left.instances ++ right.instances)
  else if let .forallE _ index body _ := shape then
    let body ← Core.betaReduce (← whnf body)
    if body.hasLooseBVars || (← isProp index) then
      throwError "affine certification requires a nondependent function space, got {type}"
    let target ← buildSpace body
    let data ← mkAppM ``Structure.pi #[index, target.data]
    finishSpace type data target.instances
  else
    throwError "unsupported affine vector-space type {type}; expected ℝ, a finite Euclidean space, a product, or a function space over these"

/-- Return canonical `AddCommGroup` and `Module ℝ` instance expressions.

This function does not synthesize either structure from ambient instances.
It accepts real and finite Euclidean spaces, products, and nondependent function
spaces, reducing type aliases only. Callers are responsible for any finite-index restriction.
-/
def canonicalSpace (type : Expr) : MetaM (Expr × Expr) := do
  let result ← buildSpace type
  pure (← mkAppM ``Structure.group #[result.data],
    ← mkAppM ``Structure.module #[result.data])

/-- Install each canonical instance and substitute its value into the result. -/
private def installInstances (remaining : List Expr) (action : MetaM Expr) : MetaM Expr := do
  match remaining with
  | [] => instantiateMVars (← action)
  | inst :: rest =>
      mapLetDeclZeta `_affineCanonical (← inferType inst) inst fun _ =>
        installInstances rest action

/-- Construct an expression with canonical structures taking local precedence.

The supplied spaces, all their component spaces, and `ℝ` receive canonical
local instances. Other local instances, including index `Fintype` instances,
remain available. Inserted let instances are substituted back into the result
before their scope ends, so the returned expression has no escaping instance
free variables. The result is deliberately an `Expr`, rather than arbitrary
data whose embedded expressions could accidentally retain those variables.
-/
def withCanonicalSpaces (types : Array Expr) (action : MetaM Expr) : MetaM Expr := do
  let mut instances := #[]
  for type in #[mkConst ``Real] ++ types do
    let result ← buildSpace type
    for inst in result.instances do
      unless instances.contains inst do
        instances := instances.push inst
  installInstances instances.toList action

end Morew.Elab.Affine.Space
