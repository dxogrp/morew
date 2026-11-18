/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/
module

public meta import Morew.Elab.Atom
public import Morew.Elab.Evidence
public meta import Morew.Elab.Expr
public meta import Morew.Elab.State

/-! Transport scalar bounds through real arithmetic, exponentials, maxima, minima, and
positive parts. Fixed scalar products use independent sign evidence. Unrecognized
contexts require an explicit certificate. -/

public section

namespace Morew.Elab.ObjectiveContext

open Lean Lean.Meta Qq

theorem reflexive (a : ℝ) : a ≤ a := le_refl a
theorem add {a b c d : ℝ} (h : a ≤ b) (k : c ≤ d) : a + c ≤ b + d :=
  add_le_add h k
theorem sub {a b c d : ℝ} (h : a ≤ b) (k : d ≤ c) : a - c ≤ b - d :=
  sub_le_sub h k
theorem neg {a b : ℝ} (h : b ≤ a) : -a ≤ -b := neg_le_neg h
theorem maximum {a b c d : ℝ} (h : a ≤ b) (k : c ≤ d) :
    max a c ≤ max b d := max_le_max h k
theorem minimum {a b c d : ℝ} (h : a ≤ b) (k : c ≤ d) :
    min a c ≤ min b d := min_le_min h k
theorem positive {a b : ℝ} (h : a ≤ b) : a⁺ ≤ b⁺ := posPart_mono h
theorem mulLeft {a b c : ℝ} (h : a ≤ b) (sign : 0 ≤ c) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h sign
theorem mulRight {a b c : ℝ} (h : a ≤ b) (sign : 0 ≤ c) : a * c ≤ b * c :=
  mul_le_mul_of_nonneg_right h sign
theorem mulLeftNeg {a b c : ℝ} (h : b ≤ a) (sign : c ≤ 0) : c * a ≤ c * b :=
  mul_le_mul_of_nonpos_left h sign
theorem mulRightNeg {a b c : ℝ} (h : b ≤ a) (sign : c ≤ 0) : a * c ≤ b * c :=
  mul_le_mul_of_nonpos_right h sign
theorem nonposOfNegative {a : ℝ} (h : a < 0) : a ≤ 0 := le_of_lt h
theorem nonposOfNegNonneg {a : ℝ} (h : 0 ≤ -a) : a ≤ 0 :=
  neg_nonneg.mp h
theorem trans {a b c : ℝ} (h : a ≤ b) (k : b ≤ c) : a ≤ c := le_trans h k

private meta abbrev ContextM := ExceptT MessageData MetaM

private meta def reject (left right : Expr) (reason : MessageData) : ContextM α := do
  throwThe MessageData (← addMessageContext
    m!"cannot certify bound context from {left} to {right}: {reason}; use `using` with an explicit context certificate")

/-- Compare typed expressions structurally with proof irrelevance and fixed function heads.
Preserve local-definition identities unless `reduceStructure` requests `let`, projection,
and tuple-match reduction after occurrence selection. -/
meta partial def sameExpression (left right : Expr) (reduceStructure : Bool := false) : MetaM Bool := do
  let left ← if reduceStructure then Expr.reduceStructure left else pure left.consumeMData
  let right ← if reduceStructure then Expr.reduceStructure right else pure right.consumeMData
  if left == right then return true
  -- Respect proof irrelevance for extracted instance proof fields.
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

private meta def same (left right : Expr) : MetaM Bool :=
  sameExpression left right (reduceStructure := true)

private meta def canonicalPrefix (source expected : Expr) (operands : Nat) : MetaM Bool := do
  let source := source.consumeMData
  let expected := expected.consumeMData
  return (← Expr.operationPrefixMismatch? source expected operands).isNone

private meta inductive Arithmetic where
  | add | sub | neg | mul | exp | maximum | minimum | pos
  deriving BEq

private meta def arithmetic? (expression : Expr) : MetaM (Option (Arithmetic × Array Expr)) := do
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
    match atom.kind with
    | .exp => return some (.exp, atom.operands)
    | .maximum => return some (.maximum, atom.operands)
    | .minimum => return some (.minimum, atom.operands)
    | .pos => return some (.pos, atom.operands)
    | _ => pure ()
  return none

private meta def realRelation? (expression : Expr) : MetaM (Option (Expr × Expr)) := do
  let expression := expression.consumeMData
  let ge := expression.isAppOfArity ``GE.ge 4
  unless ge || expression.isAppOfArity ``LE.le 4 do return none
  let args := expression.getAppArgs
  unless (← isDefEq args[0]! q(ℝ)) &&
      (← isDefEq args[1]! (mkConst ``Real.instLE)) do return none
  return some (args[if ge then 3 else 2]!, args[if ge then 2 else 3]!)

private meta def nonpos? (point value : Expr) : MetaM (Option Expr) := do
  if (← Expr.depends point value) || (← Expr.hasUnresolved value) then return none
  let value : Q(ℝ) := value
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if !(← Expr.depends point declaration.toExpr) &&
          !(← Expr.hasUnresolved declaration.toExpr) then
        if ← isDefEq declaration.type q($value ≤ 0) then
          checkWithKernel declaration.toExpr
          return some declaration.toExpr
        if ← isDefEq declaration.type q($value < 0) then
          return some (← mkAppM ``nonposOfNegative #[declaration.toExpr])
  if let some proof ← Evidence.constantSign? point q(-$value) false then
    return some (← mkAppOptM ``nonposOfNegNonneg #[some value, some proof])
  return none

private meta def boundRelation? (expression : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut expression := expression
  -- Unfold one relation definition at a time to retain operation and instance identity.
  for _ in [:8] do
    if expression.isAppOf ``LE.le || expression.isAppOf ``GE.ge then
      return ← realRelation? expression
    if let some next ← reduceRecMatcher? expression then
      expression := next.consumeMData
      continue
    let some next ← unfoldDefinition? expression | return none
    expression := next.consumeMData
  return none

private meta partial def inequality (point left right bound : Expr) : ContextM Expr := do
  let left ← Expr.reduceStructure left
  let right ← Expr.reduceStructure right
  -- Unfold the bound's definition while preserving its endpoints.
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
  | .exp => return ← mkAppM ``Real.exp_le_exp_of_le #[← inequality point lhs[0]! rhs[0]! bound]
  | .maximum =>
    return ← mkAppM ``maximum #[← inequality point lhs[0]! rhs[0]! bound,
      ← inequality point lhs[1]! rhs[1]! bound]
  | .minimum =>
    return ← mkAppM ``minimum #[← inequality point lhs[0]! rhs[0]! bound,
      ← inequality point lhs[1]! rhs[1]! bound]
  | .pos => return ← mkAppM ``positive #[← inequality point lhs[0]! rhs[0]! bound]
  | .mul =>
    for i in [:2] do
      let coefficient := lhs[i]!
      if (← same coefficient rhs[i]!) && !(← Expr.depends point coefficient) then
        let j := 1 - i
        if let some sign ← Evidence.constantSign? point coefficient false then
          let attempt : Except MessageData Expr ← liftM (inequality point lhs[j]! rhs[j]! bound).run
          if let .ok proof := attempt then
            return ← mkAppM (if i == 0 then ``mulLeft else ``mulRight) #[proof, sign]
        if let some sign ← nonpos? point coefficient then
          let attempt : Except MessageData Expr ← liftM (inequality point rhs[j]! lhs[j]! bound).run
          if let .ok proof := attempt then
            return ← mkAppM (if i == 0 then ``mulLeftNeg else ``mulRightNeg) #[proof, sign]
    reject left right "multiplication requires an unchanged decision-independent scalar with a proved sign"

private meta partial def predicate (point source target bound sourceProof : Expr) : ContextM Expr := do
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

private meta def checked (inputs : Array Expr) (expected : Expr) (action : ContextM Expr) :
    MetaM (Except MessageData Expr) :=
  State.withIsolatedMVars do
    for input in inputs do
      if ← Expr.hasUnresolved input then
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

/-- Prove `lower ≤ upper` by transporting the supplied bound through real arithmetic,
exponentials, maxima, minima, and positive parts.
Isolate caller metavariables and failed environment changes. -/
meta def proveInequality (point lower upper boundProof : Expr) : MetaM (Except MessageData Expr) := do
  let lower : Q(ℝ) := lower
  let upper : Q(ℝ) := upper
  checked #[point, lower, upper, boundProof] q($lower ≤ $upper) <|
    inequality point lower upper boundProof

/-- Prove `target` from `sourceProof : source` and a scalar bound through standard
non-strict real comparisons and conjunctions. For constraints, `source` is the rewritten predicate. -/
meta def provePredicate (point source target boundProof sourceProof : Expr) :
    MetaM (Except MessageData Expr) :=
  checked #[point, source, target, boundProof, sourceProof] target <|
    predicate point source target boundProof sourceProof

end Morew.Elab.ObjectiveContext
