/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Plan
import Morew.Elab.Expr

/-!
# Retained lower bounds for exact conic rewrites

Only independent constants with checked sign evidence, or native non-strict
lower bounds in retained entries, establish a domain fact. Finite coordinate
goals project canonical vector bounds or specialize one retained finite family.
Search preserves presentation order and conjunction boundaries. Strict rows,
arithmetic deductions, and the selected predicate are not sources of evidence.
-/

namespace Morew.Elab.Conic.Domain

open Lean Lean.Meta Qq

open Morew.Elab.Rewrite.Decomposition (conjunctionParts)

private theorem nonnegativeOfPositive {value : ℝ} (h : 0 < value) : 0 ≤ value :=
  le_of_lt h

/-- Prove the sign of an independent real constant from an independent local
hypothesis or bounded numeral/rational evaluation, using canonical real order. -/
def constantSign? (point value : Expr) (strict : Bool)
    (index? : Option Expr := none) : MetaM (Option Expr) := do
  if (← Expr.depends point value) || (← Morew.Elab.Rewrite.Plan.unresolved value) then return none
  let value : Q(ℝ) := value
  let obligation : Q(Prop) := if strict then q(0 < $value) else q(0 ≤ $value)
  -- A coordinate of the canonical zero vector reduces to `Real.zero` rather
  -- than numeral syntax; reflexivity supplies its sign without arithmetic search.
  if !strict && (← isDefEq value q((0 : ℝ))) then return some q(le_refl (0 : ℝ))
  if let some proof ← Evidence.proveIndependent? point obligation index? then return some proof
  if !strict then
    if let some positive ← Evidence.proveIndependent? point q(0 < $value) index? then
      return some (← mkAppM ``nonnegativeOfPositive #[positive])
  return none

private theorem positiveOfMargin {epsilon value : ℝ}
    (positive : 0 < epsilon) (bound : epsilon ≤ value) : 0 < value :=
  lt_of_lt_of_le positive bound

private theorem nonnegativeOfMargin {epsilon value : ℝ}
    (nonnegative : 0 ≤ epsilon) (bound : epsilon ≤ value) : 0 ≤ value :=
  le_trans nonnegative bound

private def canonicalDifference (value epsilon : ℝ) : ℝ := value - epsilon

private def canonicalVectorDifference (n : Nat) (value epsilon : Fin n → ℝ) :
    Fin n → ℝ := value - epsilon

private def canonicalVectorLE (n : Nat) (epsilon value : Fin n → ℝ) : Prop :=
  epsilon ≤ value

private theorem vectorBoundAt {n : Nat} {epsilon value : Fin n → ℝ}
    (bound : epsilon ≤ value) (i : Fin n) : epsilon i ≤ value i := bound i

private theorem marginOfNonnegativeDifference {epsilon value : ℝ}
    (bound : value - epsilon ∈ ℝ₊) : epsilon ≤ value :=
  sub_nonneg.mp bound

private theorem nonnegativeOfMembership {value : ℝ} (bound : value ∈ ℝ₊) :
    0 ≤ value := bound

private theorem nonnegativeVectorAt {n : Nat} {value : Fin n → ℝ}
    (bound : value ∈ ℝ₊^n) (i : Fin n) : 0 ≤ value i := bound i

private theorem marginOfNonnegativeVectorDifference {n : Nat}
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
  if (← Expr.depends point n) || (← Morew.Elab.Rewrite.Plan.unresolved n) then return none
  return some n

private def signInMembership? (point value body evidence : Expr) (strict : Bool)
    (index? : Option Expr) :
    MetaM (Option Expr) := do
  let some coordinate ← nonnegativeValue? point body | return none
  let coordinate ← Expr.reduceStructure coordinate
  unless ← isDefEq (← inferType coordinate) q(ℝ) do
    let some index := index? | return none
    let some n ← vectorDimension? point (← inferType coordinate) index | return none
    if !strict && (← isDefEq (mkApp coordinate index) value) then
      return some (← mkAppM ``nonnegativeVectorAt #[evidence, index])
    unless coordinate.isAppOfArity ``HSub.hSub 6 do return none
    let args := coordinate.getAppArgs
    let upper := args[4]!
    let epsilon := args[5]!
    let canonical := (mkAppN (← getConstInfo ``canonicalVectorDifference).value!
      #[n, upper, epsilon]).headBeta
    unless (← isDefEq args[3]! canonical.getAppArgs[3]!) &&
        (← isDefEq coordinate canonical) && (← isDefEq (mkApp upper index) value) do return none
    let some sign ← constantSign? point (mkApp epsilon index) strict index? | return none
    let bound ← mkAppM ``marginOfNonnegativeVectorDifference #[evidence, index]
    return some (← mkAppM
      (if strict then ``positiveOfMargin else ``nonnegativeOfMargin) #[sign, bound])
  if !strict && (← isDefEq coordinate value) then
    return some (← mkAppM ``nonnegativeOfMembership #[evidence])
  unless coordinate.isAppOfArity ``HSub.hSub 6 do return none
  let args := coordinate.getAppArgs
  let upper := args[4]!
  let epsilon := args[5]!
  let canonical := (mkAppN (← getConstInfo ``canonicalDifference).value!
    #[upper, epsilon]).headBeta
  unless (← isDefEq args[3]! canonical.getAppArgs[3]!) &&
      (← isDefEq coordinate canonical) && (← isDefEq upper value) do return none
  let some sign ← constantSign? point epsilon strict index? | return none
  let bound ← mkAppM ``marginOfNonnegativeDifference #[evidence]
  return some (← mkAppM
    (if strict then ``positiveOfMargin else ``nonnegativeOfMargin) #[sign, bound])

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
      (if strict then ``positiveOfMargin else ``nonnegativeOfMargin) #[sign, bound])
  unless ← isDefEq args[1]! (mkConst ``Real.instLE) do return none
  unless ← isDefEq upper value do return none
  let some sign ← constantSign? point epsilon strict index? | return none
  return some (← mkAppM
    (if strict then ``positiveOfMargin else ``nonnegativeOfMargin) #[sign, evidence])

/-- Certify strict or non-strict nonnegativity from an independent constant or
the first usable retained lower margin. The caller excludes the selected row. -/
def signFromRetained? (point value : Expr) (retainedBodies : Array Expr)
    (remainderProof : Expr) (strict : Bool) (index? : Option Expr := none) : MetaM (Option Expr) := do
  if let some proof ← constantSign? point value strict index? then return some proof
  let parts ← conjunctionParts retainedBodies.size remainderProof
  for body in retainedBodies, proof in parts do
    if let some sign ← signInRow? point value body proof strict index? then return some sign
  return none

end Morew.Elab.Conic.Domain
