/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Cone
import Morew.Syntax.PowerChainView
import Mathlib.Tactic.NormNum
import Lean.Elab.Term

/-!
# Conservative mathematical printing of finite power chains

Recognize complete canonical chains in the final typed rows of a reformulation.
This changes only print metadata. No expression, instance, dimension, or proof
is rewritten, and incomplete or ambiguous chains keep their ordinary display.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab.Term Qq
open Morew.Conic

private def nativePowerMembership (α : ℝ) (value : ℝ × ℝ × ℝ) : Prop :=
  value ∈ Cone.powerSet α

private def nativeBundledPowerMembership (α : ℝ) (hα : 0 < α ∧ α < 1)
    (value : ℝ × ℝ × ℝ) : Prop := value ∈ (Cone.power α hα).carrier

private def nativeZeroMembership (value : ℝ) : Prop := value ∈ ({0} : Set ℝ)

private def nativeNonnegativeMembership (value : ℝ) : Prop :=
  value ∈ Cone.nonnegativeScalar.carrier

-- Check the operation independently of its current operands: altered instances
-- can agree with native arithmetic at one particular value.
private def nativePrefix (value canonical : Expr) (operands : Nat) : MetaM Bool := do
  let args := value.getAppArgs
  let expected := canonical.getAppArgs
  unless value.getAppFn == canonical.getAppFn && args.size == expected.size &&
      operands ≤ args.size do return false
  for i in [:args.size - operands] do
    unless ← isDefEq args[i]! expected[i]! do return false
  return true

private def naturalLiteral? (value : Expr) : MetaM (Option Nat) := do
  let value := value.consumeMData
  if let .lit (.natVal n) := value then return some n
  unless value.isAppOfArity ``OfNat.ofNat 3 do return none
  let args := value.getAppArgs
  let .lit (.natVal n) := args[1]! | return none
  let canonical ← mkAppM ``instOfNatNat #[mkRawNatLit n]
  unless (← isDefEq args[0]! q(Nat)) && (← isDefEq args[2]! canonical) do return none
  return some n

private def realLiteral (value : Expr) (n : Nat) : MetaM Bool := do
  let value := value.consumeMData
  unless value.isAppOfArity ``OfNat.ofNat 3 && value.getAppArgs[1]! == mkRawNatLit n do
    return false
  let numeral : Q(Nat) := mkRawNatLit n
  let ⟨canonical, _⟩ ← Mathlib.Meta.NormNum.mkOfNat (u := .zero)
    q(ℝ) q(inferInstance) numeral
  nativePrefix value canonical 0

private def nativeNatBinary? (value : Expr) (addition : Bool) :
    MetaM (Option (Expr × Expr)) := do
  let value := value.consumeMData
  let name := if addition then ``Nat.add else ``Nat.sub
  if value.isAppOfArity name 2 then return some (value.getAppArgs[0]!, value.getAppArgs[1]!)
  unless value.isAppOfArity (if addition then ``HAdd.hAdd else ``HSub.hSub) 6 do return none
  unless ← isDefEq (value.getBoundedAppFn 2) (mkConst name) do return none
  return some (value.getAppArgs[4]!, value.getAppArgs[5]!)

-- Mathematical dimensions keep named leaves opaque, but an explicit numeral
-- or arithmetic operation must have its native meaning. In particular, a
-- custom `OfNat Nat 3` must not become the mathematical dimension three.
private partial def nativeDimension (value : Expr) : MetaM Bool := do
  let value := value.consumeMData
  if value.isFVar || value.isConst then return true
  if (← naturalLiteral? value).isSome then return true
  if value.isAppOfArity ``Nat.succ 1 then
    return ← nativeDimension value.getAppArgs[0]!
  for addition in [true, false] do
    if let some (left, right) ← nativeNatBinary? value addition then
      return (← nativeDimension left) && (← nativeDimension right)
  return false

private def nativeRealBinary? (value : Expr) (name : Name) :
    MetaM (Option (Expr × Expr)) := do
  let value := value.consumeMData
  unless value.isAppOfArity name 6 do return none
  let left : Q(ℝ) := value.getAppArgs[4]!
  let right : Q(ℝ) := value.getAppArgs[5]!
  let canonical := if name == ``HAdd.hAdd then q($left + $right)
    else if name == ``HSub.hSub then q($left - $right)
    else q($left / $right)
  unless ← nativePrefix value canonical 2 do return none
  return some (left, right)

private def nativeRealCast? (value : Expr) : MetaM (Option Expr) := do
  let value := value.consumeMData
  unless value.isAppOfArity ``Nat.cast 3 do return none
  let natural : Q(Nat) := value.getAppArgs[2]!
  unless ← nativePrefix value q(($natural : ℝ)) 1 do return none
  return some natural

private def same (a b : Expr) : Bool := a.consumeMData == b.consumeMData

private def vectorDimension? (value : Expr) : MetaM (Option Expr) := do
  -- Replayed tuple-binder types can carry pattern-reference annotations around
  -- `Fin` and its arguments. These are presentation metadata, not type casts.
  let type ← erasePatternRefAnnotations (← inferType value)
  let .forallE _ index result _ := (← whnf type) | return none
  unless !result.hasLooseBVars && (← isDefEq result q(ℝ)) do return none
  let index ← erasePatternRefAnnotations (← whnf index)
  unless index.isAppOfArity ``Fin 1 do return none
  return some index.getAppArgs[0]!

private structure Coordinate where
  vector : Expr
  dimension : Expr
  index : Expr

private def coordinate? (value : Expr) : MetaM (Option Coordinate) := do
  let .app vector index := value.consumeMData | return none
  let index := index.consumeMData
  unless index.isAppOfArity ``Fin.mk 3 do return none
  let some dimension ← vectorDimension? vector | return none
  unless same dimension index.getAppArgs[0]! do return none
  return some { vector, dimension, index := index.getAppArgs[1]! }

private def tuple? (value : Expr) : Option (Expr × Expr × Expr) := do
  let value := value.consumeMData
  guard <| value.isAppOfArity ``Prod.mk 4
  let rest := value.getAppArgs[3]!.consumeMData
  guard <| rest.isAppOfArity ``Prod.mk 4
  return (value.getAppArgs[2]!, rest.getAppArgs[2]!, rest.getAppArgs[3]!)

private def membershipHead (row : Expr) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
      let row := row.consumeMData
      if row.isApp && row.getAppFn.isLambda then membershipHead row.headBeta fuel else some row

private def powerMembership? (row : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  -- The conic planner applies a literal membership template. Remove just that
  -- application scaffolding, including wrappers retained after replay. Do not
  -- unfold a named predicate or its instances.
  let some row := membershipHead row 32 | return none
  unless row.isAppOfArity ``Membership.mem 5 do return none
  let args := row.getAppArgs
  let carrier := args[3]!.consumeMData
  let (exponent, canonical) ← if carrier.isAppOfArity ``Cone.powerSet 1 then do
      let exponent := carrier.getAppArgs[0]!
      let canonical := (mkAppN (← getConstInfo ``nativePowerMembership).value!
        #[exponent, args[4]!]).headBeta
      pure (exponent, canonical)
    else do
      unless carrier.isAppOfArity ``Cone.carrier 1 do return none
      let cone := carrier.getAppArgs[0]!.consumeMData
      unless cone.isAppOfArity ``Cone.power 2 do return none
      let exponent := cone.getAppArgs[0]!
      let canonical := (mkAppN (← getConstInfo ``nativeBundledPowerMembership).value!
        #[exponent, cone.getAppArgs[1]!, args[4]!]).headBeta
      pure (exponent, canonical)
  unless (← nativePrefix row canonical 2) && (← isDefEq row canonical) do return none
  let some (x, y, z) := tuple? args[4]! | return none
  return some (exponent, x, y, z)

private def nativeMembershipValue? (row : Expr) (template : Name) : MetaM (Option Expr) := do
  let row := row.consumeMData
  unless row.isAppOfArity ``Membership.mem 5 do return none
  let value := row.getAppArgs[4]!
  let canonical := (mkApp (← getConstInfo template).value! value).headBeta
  let carrier := row.getAppArgs[3]!.consumeMData
  if template == ``nativeZeroMembership then
    let canonicalCarrier := canonical.getAppArgs[3]!.consumeMData
    unless ← nativePrefix carrier canonicalCarrier 1 do return none
    unless ← realLiteral carrier.getAppArgs.back! 0 do return none
  else
    unless carrier.isConstOf ``Cone.nonnegativeScalarCarrier ||
        (carrier.isAppOfArity ``Cone.carrier 1 &&
          carrier.getAppArgs[0]!.isConstOf ``Cone.nonnegativeScalar) do return none
  unless (← nativePrefix row canonical 2) && (← isDefEq row canonical) do return none
  return some value

private def realComparison? (row : Expr) (equality : Bool) : MetaM (Option (Expr × Expr)) := do
  let row := row.consumeMData
  if equality then
    unless row.isAppOfArity ``Eq 3 do return none
    unless ← isDefEq row.getAppArgs[0]! q(ℝ) do return none
    return some (row.getAppArgs[1]!, row.getAppArgs[2]!)
  unless row.isAppOfArity ``LE.le 4 do return none
  let left : Q(ℝ) := row.getAppArgs[2]!
  let right : Q(ℝ) := row.getAppArgs[3]!
  unless ← nativePrefix row q($left ≤ $right) 2 do return none
  return some (left, right)

private def isCoordinate (value vector dimension index : Expr) : MetaM Bool := do
  let some coordinate ← coordinate? value | return false
  return same coordinate.vector vector && same coordinate.dimension dimension &&
    same coordinate.index index

private structure Chain where
  auxiliary : Expr
  source : Expr
  dimension : Expr
  size : Expr
  indexName : Name

private def recurrence? (row : Expr) : MetaM (Option Chain) := do
  let .forallE name indexType body _ := row.consumeMData | return none
  let indexType ← whnf indexType
  unless indexType.isAppOfArity ``Fin 1 do return none
  let size := indexType.getAppArgs[0]!
  let some (dimension, one) ← nativeNatBinary? size false | return none
  unless (← naturalLiteral? one) == some 1 && (← nativeDimension dimension) do return none
  let mut names ← getLCtx
  for declaration in ← getLCtx do
    names := names.setUserName declaration.fvarId declaration.userName.eraseMacroScopes
  let indexName := names.getUnusedName
    (if name.isAnonymous then `j else name.eraseMacroScopes)
  withLocalDeclD indexName indexType fun index => do
    let some (exponent, x, y, z) ← powerMembership? (body.instantiate1 index) | return none
    let some left ← coordinate? x | return none
    let some input ← coordinate? y | return none
    let some right ← coordinate? z | return none
    unless same left.dimension dimension && same input.dimension dimension &&
        same right.dimension dimension && same left.vector right.vector do return none
    if (left.vector.find? (· == index)).isSome ||
        (input.vector.find? (· == index)).isSome then return none
    let value := mkApp2 (mkConst ``Fin.val) size index
    unless same left.index value do return none
    let some (next, one) ← nativeNatBinary? right.index true | return none
    unless same next value && (← naturalLiteral? one) == some 1 &&
        same input.index right.index do return none
    let some (numerator, denominator) ← nativeRealBinary? exponent ``HDiv.hDiv | return none
    let some (n, one) ← nativeRealBinary? numerator ``HAdd.hAdd | return none
    let some (d, two) ← nativeRealBinary? denominator ``HAdd.hAdd | return none
    unless (← realLiteral one 1) && (← realLiteral two 2) do return none
    let some n ← nativeRealCast? n | return none
    let some d ← nativeRealCast? d | return none
    unless same n value && same d value do return none
    return some {
      auxiliary := left.vector
      source := input.vector
      dimension := dimension
      size := size
      indexName := indexName
    }

private def first? (chain : Chain) (row : Expr) : MetaM (Option Bool) := do
  let (left, right, membership) ← if let some (left, right) ← realComparison? row true then
      pure (left, right, false)
    else do
      let some value ← nativeMembershipValue? row ``nativeZeroMembership | return none
      let some (left, right) ← nativeRealBinary? value ``HSub.hSub | return none
      pure (left, right, true)
  let some left ← coordinate? left | return none
  let some right ← coordinate? right | return none
  unless same left.vector chain.auxiliary && same right.vector chain.source &&
      same left.dimension chain.dimension && same right.dimension chain.dimension &&
      (← naturalLiteral? left.index) == some 0 &&
      (← naturalLiteral? right.index) == some 0 do return none
  return some membership

private def nonnegative? (chain : Chain) (row : Expr) : MetaM (Option Bool) := do
  if let some (left, right) ← realComparison? row false then
    unless (← realLiteral left 0) &&
        (← isCoordinate right chain.auxiliary chain.dimension chain.size) do return none
    return some false
  let some value ← nativeMembershipValue? row ``nativeNonnegativeMembership | return none
  unless ← isCoordinate value chain.auxiliary chain.dimension chain.size do return none
  return some true

private def bound? (chain : Chain) (row : Expr) : MetaM (Option (Expr × Bool)) := do
  if let some (left, right) ← realComparison? row false then
    unless ← isCoordinate right chain.auxiliary chain.dimension chain.size do return none
    return some (left, false)
  let some value ← nativeMembershipValue? row ``nativeNonnegativeMembership | return none
  let some (left, right) ← nativeRealBinary? value ``HSub.hSub | return none
  unless ← isCoordinate left chain.auxiliary chain.dimension chain.size do return none
  return some (right, true)

-- `some true` is the original cast-bearing expression; `some false` is its
-- already-normalized literal form. The distinction controls only formatting.
private def inverseExponent? (exponent dimension : Expr) : MetaM (Option Bool) := do
  if let some (one, denominator) ← nativeRealBinary? exponent ``HDiv.hDiv then
    if ← realLiteral one 1 then
      if let some (n, one) ← nativeRealBinary? denominator ``HAdd.hAdd then
        if ← realLiteral one 1 then
          if let some n ← nativeRealCast? n then
            if same n dimension then return some true
  -- Literal dimensions may already have the proof-producing rational
  -- normalization performed by the conic planner. Named dimensions stay named.
  let some n ← naturalLiteral? dimension | return none
  unless n < 100000 do return none
  let some (numerator, denominator) ← nativeRealBinary? exponent ``HDiv.hDiv | return none
  unless (← realLiteral numerator 1) && (← realLiteral denominator (n + 1)) do return none
  return some false

private def inverse? (chain : Chain) (row : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let some (exponent, value, last, one) ← powerMembership? row | return none
  unless (← isCoordinate last chain.auxiliary chain.dimension chain.size) &&
      (← realLiteral one 1) do return none
  let some hasCast ← inverseExponent? exponent chain.dimension | return none
  return some (value, exponent, hasCast)

private structure Candidate where
  rows : Array (Nat × Morew.Syntax.PowerChainRow)

private partial def syntaxMentions (name : Name) (stx : Syntax) : Bool :=
  (stx.isIdent && stx.getId.eraseMacroScopes == name) ||
    stx.getArgs.any (syntaxMentions name)

private def candidate? (rows : Array Expr) (step : Nat) (chain : Chain)
    (renderLeaf : Expr → TermElabM Syntax) : TermElabM (Option Candidate) := do
  let mut starts := #[]
  let mut signs := #[]
  let mut bounds := #[]
  let mut inverses := #[]
  for i in [:rows.size] do
    if i == step then continue
    if rows[i]!.hasMVar || rows[i]!.hasSorry then continue
    if let some membership ← first? chain rows[i]! then starts := starts.push (i, membership)
    if let some membership ← nonnegative? chain rows[i]! then signs := signs.push (i, membership)
    if let some bound ← bound? chain rows[i]! then bounds := bounds.push (i, bound)
    if let some inverse ← inverse? chain rows[i]! then inverses := inverses.push (i, inverse)
  let [(start, startMembership)] := starts.toList | return none
  let auxiliary ← renderLeaf chain.auxiliary
  let source ← renderLeaf chain.source
  let size ← renderLeaf chain.size
  -- Global names need protection too: a vector printed as `j` must not become
  -- captured by the mathematical recurrence's natural-number binder.
  let mut indexName := chain.indexName
  let mut suffix := 1
  while #[auxiliary, source, size].any (syntaxMentions indexName) do
    indexName := chain.indexName.appendIndexAfter suffix
    suffix := suffix + 1
  let initial := #[(start, Morew.Syntax.PowerChainRow.first auxiliary source startMembership),
    (step, .step auxiliary source indexName size)]
  if let [(final, (value, exponent, hasCast))] := inverses.toList then
    unless signs.isEmpty && bounds.isEmpty do return none
    -- A dimension is a natural-number value. Removing its cast is harmless for
    -- an atomic name or numeral, but moving a compound expression into real
    -- arithmetic can change its meaning (notably truncated Nat subtraction).
    let dimension := chain.dimension.consumeMData
    let atomicDimension := dimension.isFVar || dimension.isConst ||
      (← naturalLiteral? dimension).isSome
    let exponent ← if hasCast && atomicDimension then do
        let dimension : TSyntax `term := ⟨← renderLeaf chain.dimension⟩
        pure (← `(1 / ($dimension + 1))).raw
      else renderLeaf exponent
    return some ⟨initial.push (final, .inverse (← renderLeaf value) auxiliary size
      exponent)⟩
  unless inverses.isEmpty do return none
  let [(sign, signMembership)] := signs.toList | return none
  -- `0 ≤ u[last]` is also a lower bound. It occupies only the sign role.
  let finalBounds := bounds.filter (·.1 != sign)
  let [(final, (value, membership))] := finalBounds.toList | return none
  return some ⟨initial ++ #[(sign, .nonnegative auxiliary size signMembership),
    (final, .bound (← renderLeaf value) auxiliary size membership)]⟩

/-- Build optional mathematical recipes for complete canonical finite power
chains. Rows retain their positions. Incomplete, ambiguous, overlapping, or
unsupported shapes fall back independently to the ordinary presentation. -/
def powerChainPrintRows (rows : Array Expr) (renderLeaf : Expr → TermElabM Syntax) :
    TermElabM (Array (Option Morew.Syntax.PowerChainRow)) := do
  let mut candidates := #[]
  for i in [:rows.size] do
    let candidate? ← withoutModifyingState do
      try
        if rows[i]!.hasMVar || rows[i]!.hasSorry then return none
        let some chain ← recurrence? rows[i]! | return none
        candidate? rows i chain renderLeaf
      catch _ => return none
    if let some candidate := candidate? then candidates := candidates.push candidate
  let mut counts := Array.replicate rows.size 0
  for candidate in candidates do
    for (i, _) in candidate.rows do counts := counts.modify i (· + 1)
  let mut result := Array.replicate rows.size none
  for candidate in candidates do
    unless candidate.rows.all (fun (i, _) => counts[i]! == 1) do continue
    for (i, row) in candidate.rows do result := result.set! i (some row)
  return result

end Morew.Reformulation.Internal
