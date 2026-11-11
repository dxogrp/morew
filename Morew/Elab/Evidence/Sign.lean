/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Evidence
import Morew.Elab.Cone.Nonneg
import Morew.Elab.Rewrite.Decomposition
import Morew.Elab.Expr

/-! Prove signs from independent constants or retained non-strict lower bounds.
Project finite vector bounds or specialize retained finite families in presentation
order. Exclude strict rows, arithmetic deductions, and the selected predicate. -/

namespace Morew.Elab.Evidence.Sign

open Lean Lean.Meta Qq

open Morew.Elab.Rewrite.Decomposition (conjunctionParts)

private theorem positiveOfMargin {epsilon value : ℝ}
    (positive : 0 < epsilon) (bound : epsilon ≤ value) : 0 < value :=
  lt_of_lt_of_le positive bound

private theorem nonnegOfMargin {epsilon value : ℝ}
    (nonneg : 0 ≤ epsilon) (bound : epsilon ≤ value) : 0 ≤ value :=
  le_trans nonneg bound

private def canonicalDifference (value epsilon : ℝ) : ℝ := value - epsilon

private def canonicalVectorDifference (n : Nat) (value epsilon : Fin n → ℝ) :
    Fin n → ℝ := value - epsilon

private def canonicalVectorLE (n : Nat) (epsilon value : Fin n → ℝ) : Prop :=
  epsilon ≤ value

private theorem vectorBoundAt {n : Nat} {epsilon value : Fin n → ℝ}
    (bound : epsilon ≤ value) (i : Fin n) : epsilon i ≤ value i := bound i

private theorem marginOfNonnegDifference {epsilon value : ℝ}
    (bound : value - epsilon ∈ ℝ₊) : epsilon ≤ value :=
  sub_nonneg.mp bound

private theorem nonnegOfMembership {value : ℝ} (bound : value ∈ ℝ₊) :
    0 ≤ value := bound

private theorem nonnegVectorAt {n : Nat} {value : Fin n → ℝ}
    (bound : value ∈ ℝ₊^n) (i : Fin n) : 0 ≤ value i := bound i

private theorem marginOfNonnegVectorDifference {n : Nat}
    {epsilon value : Fin n → ℝ} (bound : value - epsilon ∈ ℝ₊^n) (i : Fin n) :
    epsilon i ≤ value i := sub_nonneg.mp (bound i)

-- Check the finite vector shape before applying an actual retained proof.
private def vectorDimension? (point type index : Expr) : MetaM (Option Expr) := do
  let .forallE _ domain range _ ← whnf type | return none
  if range.hasLooseBVars then return none
  unless (← isDefEq range q(ℝ)) && (← isDefEq domain (← inferType index)) do return none
  let domain ← whnf domain
  unless domain.isAppOfArity ``Fin 1 do return none
  let n := domain.getAppArgs[0]!
  if (← Expr.depends point n) || (← Expr.hasUnresolved n) then return none
  return some n

private def signInMembership? (point value body evidence : Expr) (strict : Bool)
    (index? : Option Expr) :
    MetaM (Option Expr) := do
  let some coordinate ← Cone.nonnegValue? point body | return none
  let coordinate ← Expr.reduceStructure coordinate
  unless ← isDefEq (← inferType coordinate) q(ℝ) do
    let some index := index? | return none
    let some n ← vectorDimension? point (← inferType coordinate) index | return none
    if !strict && (← isDefEq (mkApp coordinate index) value) then
      return some (← mkAppM ``nonnegVectorAt #[evidence, index])
    unless coordinate.isAppOfArity ``HSub.hSub 6 do return none
    let args := coordinate.getAppArgs
    let upper := args[4]!
    let epsilon := args[5]!
    let canonical := (mkAppN (← getConstInfo ``canonicalVectorDifference).value!
      #[n, upper, epsilon]).headBeta
    unless (← isDefEq args[3]! canonical.getAppArgs[3]!) &&
        (← isDefEq coordinate canonical) && (← isDefEq (mkApp upper index) value) do return none
    let some sign ← constantSign? point (mkApp epsilon index) strict index? | return none
    let bound ← mkAppM ``marginOfNonnegVectorDifference #[evidence, index]
    return some (← mkAppM
      (if strict then ``positiveOfMargin else ``nonnegOfMargin) #[sign, bound])
  if !strict && (← isDefEq coordinate value) then
    return some (← mkAppM ``nonnegOfMembership #[evidence])
  unless coordinate.isAppOfArity ``HSub.hSub 6 do return none
  let args := coordinate.getAppArgs
  let upper := args[4]!
  let epsilon := args[5]!
  let canonical := (mkAppN (← getConstInfo ``canonicalDifference).value!
    #[upper, epsilon]).headBeta
  unless (← isDefEq args[3]! canonical.getAppArgs[3]!) &&
      (← isDefEq coordinate canonical) && (← isDefEq upper value) do return none
  let some sign ← constantSign? point epsilon strict index? | return none
  let bound ← mkAppM ``marginOfNonnegDifference #[evidence]
  return some (← mkAppM
    (if strict then ``positiveOfMargin else ``nonnegOfMargin) #[sign, bound])

private partial def signInRow? (point value body evidence : Expr) (strict : Bool)
    (index? : Option Expr) (allowForall : Bool := true) :
    MetaM (Option Expr) := do
  let body ← Expr.reduceStructure body (preserveLets := true)
  if let .letE name type initial rest nondep := body then
    if (← Expr.depends point type) || (← Expr.depends point initial) then
      return ← signInRow? point value (rest.instantiate1 initial) evidence strict index? allowForall
    return ← withLetDecl name type initial (nondep := nondep) fun binding => do
      let proof? ← signInRow? point value (rest.instantiate1 binding) evidence strict index? allowForall
      proof?.mapM fun proof => proof.replaceFVarsM #[binding] #[initial]
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    if let some proof ← signInRow? point value args[0]!
        (← mkAppM ``And.left #[evidence]) strict index? allowForall then return some proof
    return ← signInRow? point value args[1]!
      (← mkAppM ``And.right #[evidence]) strict index? allowForall
  if let .forallE _ domain rest _ := body then
    let some index := index? | return none
    unless allowForall && (← isDefEq domain (← inferType index)) &&
        (← whnf domain).isAppOfArity ``Fin 1 do return none
    return ← signInRow? point value (rest.instantiate1 index) (mkApp evidence index)
      strict index? false
  if body.isAppOfArity ``Membership.mem 5 then
    return ← signInMembership? point value body evidence strict index?
  let ge := body.isAppOfArity ``GE.ge 4
  unless ge || body.isAppOfArity ``LE.le 4 do return none
  let args := body.getAppArgs
  let epsilon := args[if ge then 3 else 2]!
  let upper ← Expr.reduceStructure args[if ge then 2 else 3]!
  unless ← isDefEq args[0]! q(ℝ) do
    let some index := index? | return none
    let some n ← vectorDimension? point args[0]! index | return none
    let canonical := (mkAppN (← getConstInfo ``canonicalVectorLE).value!
      #[n, epsilon, upper]).headBeta
    unless ← isDefEq args[1]! canonical.getAppArgs[1]! do return none
    unless ← isDefEq (mkApp upper index) value do return none
    let some sign ← constantSign? point (mkApp epsilon index) strict index? | return none
    let bound ← mkAppM ``vectorBoundAt #[evidence, index]
    return some (← mkAppM
      (if strict then ``positiveOfMargin else ``nonnegOfMargin) #[sign, bound])
  unless ← isDefEq args[1]! (mkConst ``Real.instLE) do return none
  unless ← isDefEq upper value do return none
  let some sign ← constantSign? point epsilon strict index? | return none
  return some (← mkAppM
    (if strict then ``positiveOfMargin else ``nonnegOfMargin) #[sign, evidence])

/-- Certify strict or non-strict nonnegativity from an independent constant or
the first usable retained lower margin. The caller excludes the selected row. -/
def signFromRetained? (point value : Expr) (retainedBodies : Array Expr)
    (remainderProof : Expr) (strict : Bool) (index? : Option Expr := none) : MetaM (Option Expr) := do
  if let some proof ← constantSign? point value strict index? then return some proof
  let parts ← conjunctionParts retainedBodies.size remainderProof
  for body in retainedBodies, proof in parts do
    if let some sign ← signInRow? point value body proof strict index? then return some sign
  return none

end Morew.Elab.Evidence.Sign
