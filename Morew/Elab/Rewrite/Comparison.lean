/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Real.Basic
import Lean
import Qq

/-!
# Checked comparison views

Conic discovery and matching may expose a real function beneath outer unary
negations. Every alternative retains an exact proof from the original predicate.
The caller supplies structural reduction, so this module does not unfold named
mathematical functions or depend on the representation registry.
-/

namespace Morew.Elab.Rewrite.Comparison

open Lean Lean.Meta Qq

/-- An alternative predicate with exactness from the original selected row. -/
structure View where
  /-- The predicate inspected by discovery and matching. -/
  predicate : Expr
  /-- A kernel-checked proof of `original ↔ predicate`. -/
  sourceIff : Expr
  deriving Inhabited

/-- Normalize comparison direction without changing its order instance. -/
def normalize (expression : Expr) (reduce : Expr → MetaM Expr) : MetaM Expr := do
  let expression ← reduce expression
  if expression.isAppOfArity ``GE.ge 4 then
    let args := expression.getAppArgs
    return mkAppN (mkConst ``LE.le expression.getAppFn.constLevels!)
      #[args[0]!, args[1]!, args[3]!, args[2]!]
  return expression

private theorem realNegLeft (a b : ℝ) : (-a ≤ b) ↔ (-b ≤ a) := neg_le

private theorem realNegRight (a b : ℝ) : (a ≤ -b) ↔ (b ≤ -a) := le_neg

private theorem realDoubleNeg (a : ℝ) : - -a = a := neg_neg a

private theorem realLeCongr (a a' b b' : ℝ) (ha : a = a') (hb : b = b') :
    (a ≤ b) ↔ (a' ≤ b') := by
  rw [ha, hb]

-- Comparison checks must not assign a caller's unresolved instance metavariable.
private def same (first second : Expr) : MetaM Bool :=
  withNewMCtxDepth <| isDefEq first second

private def realNeg? (expression : Expr) (reduce : Expr → MetaM Expr) :
    MetaM (Option Expr) := do
  let expression ← reduce expression
  unless expression.isAppOfArity ``Neg.neg 3 do return none
  let args := expression.getAppArgs
  unless ← same args[0]! q(ℝ) do return none
  let value : Q(ℝ) := args[2]!
  let canonical : Expr := q(-$value)
  unless ← same args[1]! canonical.getAppArgs[1]! do return none
  return some (← reduce value)

private structure Endpoint where
  value : Expr
  equality : Expr

-- Consume pairs from an original endpoint only. These alternatives preserve
-- its sign; the single-negation transfer below changes comparison orientation.
private partial def endpoints (expression : Expr) (reduce : Expr → MetaM Expr) :
    MetaM (Array Endpoint) := do
  let value ← reduce expression
  let mut result := #[{ value, equality := ← mkEqRefl value : Endpoint }]
  let mut current := value
  let mut equality ← mkEqRefl value
  repeat
    let some inner ← realNeg? current reduce | break
    let some value ← realNeg? inner reduce | break
    let step ← mkAppM ``realDoubleNeg #[value]
    equality ← mkEqTrans equality step
    current := value
    result := result.push { value, equality }
  return result

-- Only a newly introduced double negation is simplified. In particular, this
-- function never feeds its output back into the enumeration of source signs.
private def introducedNeg (expression : Expr) (reduce : Expr → MetaM Expr) :
    MetaM Endpoint := do
  let value : Q(ℝ) := expression
  if let some inner ← realNeg? expression reduce then
    return { value := inner, equality := ← mkAppM ``realDoubleNeg #[inner] }
  return { value := q(-$value), equality := ← mkEqRefl q(-$value) }

private def checked (source predicate proof : Expr) : MetaM View := do
  let proof ← instantiateMVars proof
  unless ← same (← inferType proof) (mkApp2 (mkConst ``Iff) source predicate) do
    throwError "comparison view proves the wrong equivalence"
  checkWithKernel proof
  return { predicate, sourceIff := proof }

-- Deduplication follows only the comparison and negation syntax introduced by
-- this module. Definitional equality is reserved for their types and instances;
-- distinct named mathematical heads remain distinct even when they unfold alike.
private partial def sameSpelling (first second : Expr) (reduce : Expr → MetaM Expr) :
    MetaM Bool := do
  let first ← reduce first
  let second ← reduce second
  if first == second then return true
  let comparison := first.isAppOfArity ``LE.le 4 && second.isAppOfArity ``LE.le 4
  let negation := first.isAppOfArity ``Neg.neg 3 && second.isAppOfArity ``Neg.neg 3
  unless comparison || negation do return false
  let firstArgs := first.getAppArgs
  let secondArgs := second.getAppArgs
  unless (← same firstArgs[0]! secondArgs[0]!) &&
      (← same firstArgs[1]! secondArgs[1]!) do return false
  unless ← sameSpelling firstArgs[2]! secondArgs[2]! reduce do return false
  if !comparison then return true
  return ← sameSpelling firstArgs[3]! secondArgs[3]! reduce

private def pushView (views : Array View) (source predicate proof : Expr)
    (reduce : Expr → MetaM Expr) :
    MetaM (Array View) := do
  for view in views do
    if ← sameSpelling view.predicate predicate reduce then return views
  return views.push (← checked source predicate proof)

/-- Enumerate deterministic, checked sign views for canonical real comparisons.

The direct view is always first, including for predicates that do not support
sign adaptation. Alternatives consume only negations found on the original
endpoints. This finite enumeration preserves intermediate negative heads for
direct negative registrations and never repeatedly processes inserted signs.
-/
def conicViews (source : Expr) (reduce : Expr → MetaM Expr) : MetaM (Array View) := do
  let body ← normalize source reduce
  let directProof ← mkAppM ``Iff.refl #[body]
  let mut views := #[← checked source body directProof]
  unless body.isAppOfArity ``LE.le 4 do return views
  let args := body.getAppArgs
  unless ← same args[0]! q(ℝ) do return views
  let left : Q(ℝ) := args[2]!
  let right : Q(ℝ) := args[3]!
  let canonical : Expr := q($left ≤ $right)
  unless ← same args[1]! canonical.getAppArgs[1]! do return views
  let lefts ← endpoints left reduce
  let rights ← endpoints right reduce
  for lhs in lefts do
    for rhs in rights do
      let a : Q(ℝ) := lhs.value
      let b : Q(ℝ) := rhs.value
      let congr ← mkAppM ``realLeCongr
        #[left, a, right, b, lhs.equality, rhs.equality]
      let base ← mkAppM ``Iff.trans #[directProof, congr]
      views ← pushView views source q($a ≤ $b) base reduce
      if let some inner ← realNeg? a reduce then
        let moved ← mkAppM ``realNegLeft #[inner, b]
        let bound ← introducedNeg b reduce
        let originalBound : Q(ℝ) := q(-$b)
        let adapted ← mkAppM ``realLeCongr
          #[originalBound, bound.value, inner, inner,
            bound.equality, ← mkEqRefl inner]
        let proof ← mkAppM ``Iff.trans
          #[base, ← mkAppM ``Iff.trans #[moved, adapted]]
        let newLeft : Q(ℝ) := bound.value
        let newRight : Q(ℝ) := inner
        views ← pushView views source q($newLeft ≤ $newRight) proof reduce
      if let some inner ← realNeg? b reduce then
        let moved ← mkAppM ``realNegRight #[a, inner]
        let bound ← introducedNeg a reduce
        let originalBound : Q(ℝ) := q(-$a)
        let adapted ← mkAppM ``realLeCongr
          #[inner, inner, originalBound, bound.value,
            ← mkEqRefl inner, bound.equality]
        let proof ← mkAppM ``Iff.trans
          #[base, ← mkAppM ``Iff.trans #[moved, adapted]]
        let newLeft : Q(ℝ) := inner
        let newRight : Q(ℝ) := bound.value
        views ← pushView views source q($newLeft ≤ $newRight) proof reduce
  return views

end Morew.Elab.Rewrite.Comparison
