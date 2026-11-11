/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Expr

/-! Flatten conjunctions with equivalence proofs and scoped local evidence. -/

namespace Morew.Elab.Rewrite

open Lean Lean.Meta

namespace Decomposition

/-- Project exactly the requested ordered entries, retaining any conjunction
inside an entry. The count comes from the checked presentation or decomposition. -/
def conjunctionParts (count : Nat) (proof : Expr) : MetaM (Array Expr) := do
  if count == 0 then return #[]
  let mut result := #[]
  let mut rest := proof
  for _ in [:count - 1] do
    result := result.push (← mkAppM ``And.left #[rest])
    rest ← mkAppM ``And.right #[rest]
  return result.push rest

private theorem appendHead (p q r s : Prop) (h : q ∧ r ↔ s) :
    (p ∧ q) ∧ r ↔ p ∧ s :=
  and_assoc.trans (and_congr Iff.rfl h)

/-- Join two normalized conjunctions without losing their equivalence. -/
partial def appendIff (left right : List Expr) : MetaM Expr := do
  match left, right with
  | [], _ => mkIffOfEq (mkApp (mkConst ``true_and) (mkAndN right))
  | _, [] => mkIffOfEq (mkApp (mkConst ``and_true) (mkAndN left))
  | [_], _ => pure <| mkApp (mkConst ``Iff.rfl) (mkAndN (left ++ right))
  | p :: rest, _ =>
      mkAppM ``appendHead #[p, mkAndN rest, mkAndN right,
        mkAndN (rest ++ right), ← appendIff rest right]

/-- Split a proposition using only the supplied structural reduction. Local
lets remain attached to every conjunct and to the decomposition proof. -/
partial def split (body : Expr) (reduce : Expr → MetaM Expr) :
    MetaM (List Expr × Expr) := do
  let body ← reduce body
  if let .letE name type value rest _ := body then
    return ← withLetDecl name type value fun binding => do
      let (rows, proof) ← split (rest.instantiate1 binding) reduce
      let rows ← rows.mapM fun row =>
        mkLetFVars #[binding] row (usedLetOnly := false) (generalizeNondepLet := false)
      let proof ← mkLetFVars #[binding] proof
        (usedLetOnly := false) (generalizeNondepLet := false)
      return (rows, proof)
  if body.isConstOf ``True then
    return ([], mkApp (mkConst ``Iff.rfl) body)
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    let (left, hl) ← split args[0]! reduce
    let (right, hr) ← split args[1]! reduce
    let split ← mkAppM ``and_congr #[hl, hr]
    let combined ← mkAppM ``Iff.trans #[split, ← appendIff left right]
    return (left ++ right, combined)
  return ([body], mkApp (mkConst ``Iff.rfl) body)

end Decomposition

/-- Decompose into ordered atomic predicates with conjunction equivalence.
`True` contributes no conjuncts; retain unsupported atomic predicates. -/
def decomposePredicate (predicate : Expr) : MetaM (Array Expr × Expr) := do
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | throwError "expected a predicate on the decision space"
  unless codomain == mkSort .zero do
    throwError "expected a predicate on the decision space"
  withLocalDeclD `point domain fun point => do
    let (bodies, proof) ← Decomposition.split (mkApp predicate point)
      (fun body => Expr.reduceStructure body (preserveLets := true))
    let predicates ← bodies.toArray.mapM (mkLambdaFVars #[point])
    let proof ← instantiateMVars (← mkLambdaFVars #[point] proof)
    let expected ← mkForallFVars #[point] (mkApp2 (mkConst ``Iff)
      (mkApp predicate point) (mkAndN bodies))
    unless ← isDefEq (← inferType proof) expected do
      throwError "constraint decomposition does not match its source predicate"
    if proof.hasMVar then
      throwError "constraint decomposition contains unresolved metavariables"
    checkWithKernel proof
    return (predicates, proof)

end Morew.Elab.Rewrite
