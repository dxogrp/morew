/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Decomposition
import Morew.Elab.Affine.State
import Morew.Elab.Conic.Space

/-!
# Checked final cone-membership normalization

Rewrite native affine comparisons to cone membership without inspecting or
expanding their operands. This pass preserves conjunction trees and local lets;
a caller supplies the already checked affine maps and transports their evidence.
-/

namespace Morew.Elab.Conic

open Lean Lean.Meta

/-- A proposition and a checked equivalence from its original spelling. -/
structure BodyNormalization where
  /-- The proposition after comparison-to-membership normalization. -/
  body : Expr
  /-- Proof of `original ↔ body`. -/
  iff : Expr
  /-- Whether a comparison leaf was replaced. -/
  changed : Bool

/-- A predicate and a checked pointwise equivalence from its original spelling. -/
structure PredicateNormalization where
  /-- The predicate after comparison-to-membership normalization. -/
  predicate : Expr
  /-- Proof of `∀ x, original x ↔ predicate x`. -/
  pointwiseIff : Expr
  /-- Whether a comparison leaf was replaced. -/
  changed : Bool

private theorem comparisonEq
    {Y : Type} [NormedAddCommGroup Y] (lhs rhs value : Y)
    (h : lhs - rhs = value) : lhs = rhs ↔ value ∈ ({0} : Set Y) := by
  rw [Set.mem_singleton_iff, ← h, sub_eq_zero]

private theorem comparisonLE
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [PartialOrder Y] [IsOrderedAddMonoid Y] [PosSMulMono ℝ Y]
    (lhs rhs value : Y) (h : rhs - lhs = value) :
    lhs ≤ rhs ↔ value ∈ ConvexCone.positive ℝ Y := by
  change lhs ≤ rhs ↔ 0 ≤ value
  rw [← h, sub_nonneg]

private def coneMembership (cone : Morew.Conic.Cone) (value : cone.Space) : Prop :=
  value ∈ cone.carrier

private def zeroMembership {Y : Type} [NormedAddCommGroup Y] (value : Y) : Prop :=
  value ∈ ({0} : Set Y)

-- Fix primitive operations where these templates are declared, so unrelated
-- local `HSub`, `Neg`, or `Zero` instances cannot affect the generated margin.
private def nativeDifference {Y : Type} [NormedAddCommGroup Y] (lhs rhs : Y) : Y :=
  lhs - rhs

private def nativeZero {Y : Type} [NormedAddCommGroup Y] : Y := 0

private def nativeNegation {Y : Type} [NormedAddCommGroup Y] (value : Y) : Y := -value

private theorem nativeSubZero {Y : Type} [NormedAddCommGroup Y] (value : Y) :
    value - 0 = value := sub_zero value

private theorem nativeZeroSub {Y : Type} [NormedAddCommGroup Y] (value : Y) :
    0 - value = -value := zero_sub value

private def exposeTemplate (value : Expr) : MetaM Expr := do
  let some result ← unfoldDefinition? value
    | throwError "could not construct a native normalization expression"
  return result

-- Match a literal zero before checking its native instance. In particular, a
-- local definition or helper whose value is zero keeps its named reference.
private def literalZero (value zero : Expr) : MetaM Bool := do
  let value := value.consumeMData
  let args := value.getAppArgs
  let literal := value.isAppOfArity ``Zero.zero 2 ||
    (value.isAppOfArity ``OfNat.ofNat 3 &&
      (args[1]! == mkRawNatLit 0 || args[1]! == mkNatLit 0))
  return literal && (← isDefEq value zero)

private def subtract (lhs rhs : Expr) : MetaM (Expr × Expr) := do
  let difference ← exposeTemplate (← mkAppM ``nativeDifference #[lhs, rhs])
  let type ← inferType lhs
  let zero ← exposeTemplate (← mkAppOptM ``nativeZero #[some type, none])
  if ← literalZero rhs zero then
    return (lhs, ← mkAppM ``nativeSubZero #[lhs])
  if ← literalZero lhs zero then
    return (← exposeTemplate (← mkAppM ``nativeNegation #[rhs]),
      ← mkAppM ``nativeZeroSub #[rhs])
  return (difference, ← mkEqRefl difference)

private def nonnegativeCone (type : Expr) : MetaM Expr := do
  let type ← whnf type
  if type.isConstOf ``Real then
    return mkConst ``Morew.Conic.Cone.nonnegativeScalar
  let .forallE _ index target _ := type
    | throwError "expected real scalar or finite-vector comparison operands"
  unless !target.hasLooseBVars && (← whnf target).isConstOf ``Real do
    throwError "expected real scalar or finite-vector comparison operands"
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 do
    throwError "expected real scalar or finite-vector comparison operands"
  return ← mkAppM ``Morew.Conic.Cone.nonnegative #[index.getAppArgs[0]!]

private def normalizeComparison (body : Expr) : MetaM BodyNormalization := do
  let args := body.getAppArgs
  let equality := body.isAppOfArity ``Eq 3
  let greaterEqual := body.isAppOfArity ``GE.ge 4
  let type := args[0]!
  -- Constructing the native cone checks the supported scalar/vector shape even
  -- for equality, where the resulting presentation uses a singleton set.
  let cone ← nonnegativeCone type
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  let (normalized, proof) ← Space.withCanonicalSpaces type type do
    let (left, right) := if equality || greaterEqual then (lhs, rhs) else (rhs, lhs)
    let (value, differenceEq) ← subtract left right
    let normalized ← if equality then
        unfoldDefinition? (← mkAppM ``zeroMembership #[value])
      else
        unfoldDefinition? (← mkAppM ``coneMembership #[cone, value])
    let some normalized := normalized | throwError "could not construct native cone membership"
    let proof ← if equality then
        mkAppM ``comparisonEq #[lhs, rhs, value, differenceEq]
      else if greaterEqual then
        mkAppM ``comparisonLE #[rhs, lhs, value, differenceEq]
      else
        mkAppM ``comparisonLE #[lhs, rhs, value, differenceEq]
    return (normalized, proof)
  unless equality do
    let relation := (← inferType proof).getAppArgs[0]!
    unless ← isDefEq args[1]! relation.getAppArgs[1]! do
      throwError "comparison uses an unsupported order instance"
  let expected := mkApp2 (mkConst ``Iff) body normalized
  unless ← isDefEq (← inferType proof) expected do
    throwError "comparison uses an unsupported order or arithmetic instance"
  return { body := normalized, iff := proof, changed := true }

private partial def normalizeBodyCore (original : Expr) : MetaM BodyNormalization := do
  let body ← Affine.reduceStructure original (preserveLets := true)
  if let .letE name type value rest nondep := body then
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← normalizeBodyCore (rest.instantiate1 binding)
      return {
        body := ← mkLetFVars #[binding] result.body
          (usedLetOnly := false) (generalizeNondepLet := false)
        iff := ← mkLetFVars #[binding] result.iff
          (usedLetOnly := false) (generalizeNondepLet := false)
        changed := result.changed
      }
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    let left ← normalizeBodyCore args[0]!
    let right ← normalizeBodyCore args[1]!
    return {
      body := mkApp2 (mkConst ``And) left.body right.body
      iff := ← mkAppM ``and_congr #[left.iff, right.iff]
      changed := left.changed || right.changed
    }
  if body.isAppOfArity ``Eq 3 || body.isAppOfArity ``LE.le 4 ||
      body.isAppOfArity ``GE.ge 4 then
    return ← normalizeComparison body
  return { body := original, iff := mkApp (mkConst ``Iff.rfl) original, changed := false }

private partial def unresolved (expression : Expr) (seen : FVarIdSet := {}) :
    MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then return true
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    unless seen.contains id do
      seen := seen.insert id
      let declaration ← id.getDecl
      if ← unresolved declaration.type seen then return true
      if let some value := declaration.value? (allowNondep := true) then
        if ← unresolved value seen then return true
  return false

private def isolated (action : MetaM α) : MetaM α := do
  let result ← Affine.withIsolatedMVars (ε := Empty) do
    return .ok (← action)
  match result with
  | .ok result => return result
  | .error impossible => nomatch impossible

/-- Normalize native scalar/vector comparisons while retaining each operand,
local let and conjunction boundary. The result proves the actual proposition,
not merely its printed representation. Non-comparison leaves remain intact.
Unresolved inputs are rejected without changing caller metavariables. -/
def normalizeBody (original : Expr) : MetaM BodyNormalization := isolated do
  if ← unresolved original then
    throwError "membership normalization requires fully elaborated expressions"
  let result ← normalizeBodyCore original
  let body ← instantiateMVars result.body
  let proof ← instantiateMVars result.iff
  let result := { result with body, iff := proof }
  let expected := mkApp2 (mkConst ``Iff) original result.body
  unless ← isDefEq (← inferType result.iff) expected do
    throwError "membership normalization does not match the source proposition"
  if result.body.hasMVar || result.iff.hasMVar then
    throwError "membership normalization contains unresolved metavariables"
  checkWithKernel result.iff
  return result

/-- Normalize a whole constraint predicate and check its pointwise equivalence.
The decision space and all operand expressions remain unchanged. -/
def normalizePredicate (predicate : Expr) : MetaM PredicateNormalization := isolated do
  if ← unresolved predicate then
    throwError "membership normalization requires fully elaborated expressions"
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | throwError "expected a predicate on the decision space"
  unless codomain == mkSort .zero do
    throwError "expected a predicate on the decision space"
  withLocalDeclD `point domain fun point => do
    let result ← normalizeBodyCore (mkApp predicate point)
    let normalized ← instantiateMVars (← mkLambdaFVars #[point] result.body)
    let pointwiseIff ← instantiateMVars (← mkLambdaFVars #[point] result.iff)
    let expected ← mkForallFVars #[point] (mkApp2 (mkConst ``Iff)
      (mkApp predicate point) (mkApp normalized point))
    unless ← isDefEq (← inferType pointwiseIff) expected do
      throwError "membership normalization does not match the source predicate"
    if normalized.hasMVar || pointwiseIff.hasMVar then
      throwError "membership normalization contains unresolved metavariables"
    checkWithKernel pointwiseIff
    return { predicate := normalized, pointwiseIff, changed := result.changed }

end Morew.Elab.Conic
