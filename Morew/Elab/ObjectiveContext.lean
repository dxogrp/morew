/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Atom
import Morew.Elab.Conic.Domain
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Checked context proofs for bound lifts

This deliberately bounded recognizer transports an existing bound through
native real arithmetic. It never unfolds user function heads, assumes a sign
depending on a decision variable, or changes an operation's instance. Failure
asks the caller for an explicit context certificate.
-/

namespace Morew.Elab.ObjectiveContext

open Lean Lean.Meta Qq

private theorem reflexive (a : ℝ) : a ≤ a := le_refl a
private theorem add {a b c d : ℝ} (h : a ≤ b) (k : c ≤ d) : a + c ≤ b + d :=
  add_le_add h k
private theorem sub {a b c d : ℝ} (h : a ≤ b) (k : d ≤ c) : a - c ≤ b - d :=
  sub_le_sub h k
private theorem neg {a b : ℝ} (h : b ≤ a) : -a ≤ -b := neg_le_neg h
private theorem mulLeft {a b c : ℝ} (h : a ≤ b) (sign : 0 ≤ c) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h sign
private theorem mulRight {a b c : ℝ} (h : a ≤ b) (sign : 0 ≤ c) : a * c ≤ b * c :=
  mul_le_mul_of_nonneg_right h sign
private theorem mulLeftNeg {a b c : ℝ} (h : b ≤ a) (sign : c ≤ 0) : c * a ≤ c * b :=
  mul_le_mul_of_nonpos_left h sign
private theorem mulRightNeg {a b c : ℝ} (h : b ≤ a) (sign : c ≤ 0) : a * c ≤ b * c :=
  mul_le_mul_of_nonpos_right h sign
private theorem exp {a b : ℝ} (h : a ≤ b) : Real.exp a ≤ Real.exp b :=
  Real.exp_le_exp.mpr h
private theorem nonpositiveOfNegative {a : ℝ} (h : a < 0) : a ≤ 0 := le_of_lt h
private theorem nonpositiveOfNegNonnegative {a : ℝ} (h : 0 ≤ -a) : a ≤ 0 :=
  neg_nonneg.mp h
private theorem trans {a b c : ℝ} (h : a ≤ b) (k : b ≤ c) : a ≤ c := le_trans h k

private abbrev ContextM := ExceptT MessageData MetaM

private def reject (left right : Expr) (reason : MessageData) : ContextM α := do
  throwThe MessageData (← addMessageContext
    m!"cannot certify bound context from {left} to {right}: {reason}; use `using` with an explicit context certificate")

/-- Compare typed expressions structurally, ignoring metadata and respecting
proof irrelevance. Computational function heads are never unfolded. By default
local-definition free variables retain their identities. `reduceStructure`
additionally reduces computational lets, projections, and tuple matchers, for
use after an occurrence has already been selected. -/
partial def sameExpression (left right : Expr) (reduceStructure : Bool := false) : MetaM Bool := do
  let left ← if reduceStructure then Expr.reduceStructure left else pure left.consumeMData
  let right ← if reduceStructure then Expr.reduceStructure right else pure right.consumeMData
  if left == right then return true
  -- Lean may extract instance proof fields (notably OfNat's AtLeastTwo
  -- evidence) into auxiliary theorems when a source declaration is compiled.
  -- Respect proof irrelevance without unfolding computational function heads.
  if ← isProof left then
    return (← isProof right) && (← isDefEq left right)
  match left, right with
  | .app lf la, .app rf ra =>
    return (← sameExpression lf rf reduceStructure) && (← sameExpression la ra reduceStructure)
  | .proj ln li lv, .proj rn ri rv =>
    return ln == rn && li == ri && (← sameExpression lv rv reduceStructure)
  | .lam _ lt lb li, .lam _ rt rb ri
  | .forallE _ lt lb li, .forallE _ rt rb ri =>
    unless li == ri && (← sameExpression lt rt reduceStructure) do return false
    withLocalDecl `_context li lt fun binder =>
      sameExpression (lb.instantiate1 binder) (rb.instantiate1 binder) reduceStructure
  | .letE _ lt lv lb ln, .letE _ rt rv rb rn =>
    unless ln == rn && (← sameExpression lt rt reduceStructure) &&
        (← sameExpression lv rv reduceStructure) do return false
    withLetDecl `_context lt lv (nondep := ln) fun binder =>
      sameExpression (lb.instantiate1 binder) (rb.instantiate1 binder) reduceStructure
  | _, _ => return false

private def same (left right : Expr) : MetaM Bool :=
  sameExpression left right (reduceStructure := true)

private def canonicalPrefix (source expected : Expr) (operands : Nat) : MetaM Bool := do
  let source := source.consumeMData
  let expected := expected.consumeMData
  unless source.getAppFn == expected.getAppFn &&
      source.getAppNumArgs == expected.getAppNumArgs do return false
  let sourceArgs := source.getAppArgs
  let expectedArgs := expected.getAppArgs
  for i in [:sourceArgs.size - operands] do
    unless ← isDefEq sourceArgs[i]! expectedArgs[i]! do return false
  return true

private inductive Arithmetic where
  | add | sub | neg | mul | exp
  deriving BEq

private def arithmetic? (expression : Expr) : MetaM (Option (Arithmetic × Array Expr)) := do
  let expression := expression.consumeMData
  let args := expression.getAppArgs
  let binary (kind : Arithmetic) (expected : Expr) : MetaM (Option (Arithmetic × Array Expr)) := do
    if ← canonicalPrefix expression expected 2 then return some (kind, args.extract 4 6)
    return none
  if args.size == 6 then
    let a : Q(ℝ) := args[4]!
    let b : Q(ℝ) := args[5]!
    if expression.isAppOf ``HAdd.hAdd then return ← binary .add q($a + $b)
    if expression.isAppOf ``HSub.hSub then return ← binary .sub q($a - $b)
    if expression.isAppOf ``HMul.hMul then return ← binary .mul q($a * $b)
  if expression.isAppOfArity ``Neg.neg 3 then
    let a : Q(ℝ) := args[2]!
    if ← canonicalPrefix expression q(-$a) 1 then return some (.neg, #[a])
  if let some atom ← Atom.recognizeAtom? expression then
    if atom.kind == .exp then return some (.exp, atom.operands)
  return none

private def realRelation? (expression : Expr) : MetaM (Option (Expr × Expr)) := do
  let expression := expression.consumeMData
  let ge := expression.isAppOfArity ``GE.ge 4
  unless ge || expression.isAppOfArity ``LE.le 4 do return none
  let args := expression.getAppArgs
  unless (← isDefEq args[0]! q(ℝ)) &&
      (← isDefEq args[1]! (mkConst ``Real.instLE)) do return none
  return some (args[if ge then 3 else 2]!, args[if ge then 2 else 3]!)

private def nonpositive? (point value : Expr) : MetaM (Option Expr) := do
  if (← Expr.depends point value) || (← Morew.Elab.Rewrite.Plan.unresolved value) then return none
  let value : Q(ℝ) := value
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if !(← Expr.depends point declaration.toExpr) &&
          !(← Morew.Elab.Rewrite.Plan.unresolved declaration.toExpr) then
        if ← isDefEq declaration.type q($value ≤ 0) then
          checkWithKernel declaration.toExpr
          return some declaration.toExpr
        if ← isDefEq declaration.type q($value < 0) then
          return some (← mkAppM ``nonpositiveOfNegative #[declaration.toExpr])
  if let some proof ← Conic.Domain.constantSign? point q(-$value) false then
    return some (← mkAppM ``nonpositiveOfNegNonnegative #[proof])
  return none

private def boundRelation? (expression : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut expression := expression
  -- A full whnf would also unfold LE.le to Real's private relation. Unfold one
  -- wrapper at a time so operation/instance recognition remains meaningful.
  for _ in [:8] do
    if expression.isAppOf ``LE.le || expression.isAppOf ``GE.ge then
      return ← realRelation? expression
    if let some next ← reduceRecMatcher? expression then
      expression := next.consumeMData
      continue
    let some next ← unfoldDefinition? expression | return none
    expression := next.consumeMData
  return none

private partial def inequality (point left right bound : Expr) : ContextM Expr := do
  let left ← Expr.reduceStructure left
  let right ← Expr.reduceStructure right
  -- Only the supplied bound may justify a changed leaf. Unfold the proposition
  -- wrapper (for example BoundDirection.Rel), not either endpoint.
  if let some (lower, upper) ← boundRelation? (← inferType bound) then
    if (← same lower left) && (← same upper right) then return bound
  unless (← isDefEq (← inferType left) q(ℝ)) &&
      (← isDefEq (← inferType right) q(ℝ)) do
    reject left right "automatic arithmetic context certification requires real values"
  if ← same left right then return ← mkAppM ``reflexive #[left]
  let some (kind, lhs) ← arithmetic? left
    | reject left right "unsupported operation or polarity"
  let some (other, rhs) ← arithmetic? right
    | reject left right "unsupported operation or arithmetic instance"
  unless kind == other do reject left right "the surrounding operations differ"
  match kind with
  | .add =>
    return ← mkAppM ``add #[← inequality point lhs[0]! rhs[0]! bound,
      ← inequality point lhs[1]! rhs[1]! bound]
  | .sub =>
    return ← mkAppM ``sub #[← inequality point lhs[0]! rhs[0]! bound,
      ← inequality point rhs[1]! lhs[1]! bound]
  | .neg => return ← mkAppM ``neg #[← inequality point rhs[0]! lhs[0]! bound]
  | .exp => return ← mkAppM ``exp #[← inequality point lhs[0]! rhs[0]! bound]
  | .mul =>
    for i in [:2] do
      let coefficient := lhs[i]!
      if (← same coefficient rhs[i]!) && !(← Expr.depends point coefficient) then
        let j := 1 - i
        if let some sign ← Conic.Domain.constantSign? point coefficient false then
          let attempt : Except MessageData Expr ← liftM (inequality point lhs[j]! rhs[j]! bound).run
          if let .ok proof := attempt then
            return ← mkAppM (if i == 0 then ``mulLeft else ``mulRight) #[proof, sign]
        if let some sign ← nonpositive? point coefficient then
          let attempt : Except MessageData Expr ← liftM (inequality point rhs[j]! lhs[j]! bound).run
          if let .ok proof := attempt then
            return ← mkAppM (if i == 0 then ``mulLeftNeg else ``mulRightNeg) #[proof, sign]
    reject left right "multiplication requires an unchanged decision-independent scalar with a proved sign"

private partial def predicate (point source target bound sourceProof : Expr) : ContextM Expr := do
  let source ← Expr.reduceStructure source
  let target ← Expr.reduceStructure target
  if ← same source target then return sourceProof
  if source.isAppOfArity ``And 2 && target.isAppOfArity ``And 2 then
    let sourceArgs := source.getAppArgs
    let targetArgs := target.getAppArgs
    let left ← predicate point sourceArgs[0]! targetArgs[0]! bound
      (← mkAppM ``And.left #[sourceProof])
    let right ← predicate point sourceArgs[1]! targetArgs[1]! bound
      (← mkAppM ``And.right #[sourceProof])
    return ← mkAppM ``And.intro #[left, right]
  let some (sourceLeft, sourceRight) ← realRelation? source
    | reject source target "expected a canonical non-strict real comparison or conjunction"
  let some (targetLeft, targetRight) ← realRelation? target
    | reject source target "expected a canonical non-strict real comparison or conjunction"
  let left ← inequality point targetLeft sourceLeft bound
  let right ← inequality point sourceRight targetRight bound
  return ← mkAppM ``trans #[left, ← mkAppM ``trans #[sourceProof, right]]

private def checked (inputs : Array Expr) (expected : Expr) (action : ContextM Expr) :
    MetaM (Except MessageData Expr) :=
  State.withIsolatedMVars do
    for input in inputs do
      if ← Morew.Elab.Rewrite.Plan.unresolved input then
        return .error m!"cannot certify an unresolved bound context"
    let result ← try action.run catch exception => pure (.error exception.toMessageData)
    match result with
    | .error reason => return .error reason
    | .ok proof =>
      let proof ← instantiateMVars proof
      if proof.hasMVar || proof.hasSorry then
        return .error m!"bound context certification produced incomplete evidence"
      unless ← isDefEq (← inferType proof) expected do
        return .error m!"bound context certification produced evidence for a different proposition"
      checkWithKernel proof
      return .ok proof

/-- Prove `lower ≤ upper` in the canonical real order by transporting the
supplied bound through a bounded arithmetic context. Caller metavariables and
failed attempts' environment changes are isolated. -/
def proveInequality (point lower upper boundProof : Expr) : MetaM (Except MessageData Expr) := do
  let lower : Q(ℝ) := lower
  let upper : Q(ℝ) := upper
  checked #[point, lower, upper, boundProof] q($lower ≤ $upper) <|
    inequality point lower upper boundProof

/-- Recover `target` from `sourceProof : source` and a supplied scalar bound.
Supports native non-strict real comparisons and conjunctions. For a constraint
lift, `source` is the rewritten predicate and `target` the original predicate. -/
def provePredicate (point source target boundProof sourceProof : Expr) :
    MetaM (Except MessageData Expr) :=
  checked #[point, source, target, boundProof, sourceProof] target <|
    predicate point source target boundProof sourceProof

end Morew.Elab.ObjectiveContext
