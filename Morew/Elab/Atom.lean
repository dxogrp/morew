/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Group.PosPart
import Lean.Meta.Basic

/-!
# Typed recognition of mathematical operations

This internal, unstable interface identifies selected native mathlib operations
without rewriting their expressions. It does not restrict what users can write
in a problem, establish domain conditions, or certify a transformation.

Additional mathematical functions may live under `Morew.Fn`. They are ordinary
Lean definitions: namespace membership alone does not register an operation.
-/

namespace Morew.Elab.Atom

open Lean Lean.Meta

/-- An operation understood by the native-operation recognizer.
This is an internal implementation interface, not a public modeling type. -/
inductive AtomKind where
  /-- The real exponential function. -/
  | exp
  /-- Mathlib's totalized real logarithm. -/
  | log
  /-- Mathlib's totalized real square root. -/
  | sqrt
  /-- The standard real inverse. -/
  | inv
  /-- The standard real absolute value. -/
  | abs
  /-- The standard real positive part. -/
  | pos
  /-- The standard binary real maximum. -/
  | maximum
  /-- The standard binary real minimum. -/
  | minimum
  /-- The real sine function. -/
  | sin
  /-- The real cosine function. -/
  | cos
  /-- The real hyperbolic sine function. -/
  | sinh
  /-- The real hyperbolic cosine function. -/
  | cosh
  /-- The real hyperbolic tangent function. -/
  | tanh
  /-- Mathlib's totalized real power with a real exponent. -/
  | rpow
  deriving Inhabited, BEq, Repr

/-- A recognized application, retaining its original expression for consumers
that construct proofs or preserve presentation. This interface is internal. -/
structure AtomApplication where
  /-- The expression supplied to the recognizer, without rewriting. -/
  original : Expr
  /-- The recognized operation. -/
  kind : AtomKind
  /-- The operands in application order, without recursive normalization. -/
  operands : Array Expr

private structure AtomHead where
  name : Name
  kind : AtomKind
  arity : Nat
  operandCount : Nat

private def atomHeads : Array AtomHead := #[
  ⟨``Real.exp, .exp, 1, 1⟩,
  ⟨``Real.log, .log, 1, 1⟩,
  ⟨``Real.sqrt, .sqrt, 1, 1⟩,
  ⟨``Inv.inv, .inv, 3, 1⟩,
  ⟨``abs, .abs, 4, 1⟩,
  ⟨``PosPart.posPart, .pos, 3, 1⟩,
  ⟨``Max.max, .maximum, 4, 2⟩,
  ⟨``Min.min, .minimum, 4, 2⟩,
  ⟨``Real.sin, .sin, 1, 1⟩,
  ⟨``Real.cos, .cos, 1, 1⟩,
  ⟨``Real.sinh, .sinh, 1, 1⟩,
  ⟨``Real.cosh, .cosh, 1, 1⟩,
  ⟨``Real.tanh, .tanh, 1, 1⟩,
  ⟨``Real.rpow, .rpow, 2, 2⟩,
  ⟨``HPow.hPow, .rpow, 6, 2⟩
]

-- Ignore metadata on the application spine, but retain it on operands and
-- preserve the complete original expression in the result.
private def applicationParts (expression : Expr) : Expr × Array Expr :=
  let rec visit (expression : Expr) (reversed : Array Expr) : Expr × Array Expr :=
    match expression with
    | .app function argument => visit function (reversed.push argument)
    | .mdata _ inner => visit inner reversed
    | head => (head, reversed.reverse)
  visit expression #[]

-- These instances are fixed explicitly. In particular, recognition must not
-- synthesize a potentially overridden local instance as its expected value.
private def canonicalPrefix (head : AtomHead) : Array Expr :=
  let real := mkConst ``Real
  let lattice := mkConst ``Real.lattice
  let addGroup := mkConst ``Real.instAddGroup
  match head.kind with
  | .exp | .log | .sqrt | .sin | .cos | .sinh | .cosh | .tanh => #[]
  | .rpow =>
      if head.name == ``Real.rpow then #[] else
        let power := mkApp3 (mkConst ``instHPow [.zero, .zero])
          real real (mkConst ``Real.instPow)
        #[real, real, real, power]
  | .inv => #[real, mkConst ``Real.instInv]
  | .abs => #[real, lattice, addGroup]
  | .pos =>
      let subNegMonoid :=
        mkApp2 (mkConst ``AddGroup.toSubNegMonoid [.zero]) real addGroup
      let posPart := mkApp3 (mkConst ``instPosPart [.zero]) real lattice subNegMonoid
      #[real, posPart]
  | .maximum => #[real, mkConst ``Real.instMax]
  | .minimum => #[real, mkConst ``Real.instMin]

private def recognizeApplication? (original : Expr) : MetaM (Option AtomApplication) := do
  -- Unresolved elaboration is not enough evidence for an operation's identity.
  -- In particular, do not specialize metavariables to make a candidate match.
  if original.hasMVar then return none
  let (function, arguments) := applicationParts original
  let .const name _ := function | return none
  let some head := atomHeads.find? (·.name == name) | return none
  unless arguments.size == head.arity do return none
  let expectedArguments := canonicalPrefix head
  for expected in expectedArguments, actual in arguments do
    unless ← isDefEq actual expected do return none
  let operands := arguments.extract (head.arity - head.operandCount) head.arity
  for operand in operands do
    let type ← inferType operand
    if type.hasMVar then return none
    unless ← isDefEq type (mkConst ``Real) do return none
  return some { original, kind := head.kind, operands }

/-- Recognize a fully applied, supported native real operation.

Only the explicit constant-head table chooses an operation identity. Known type
and instance arguments are checked against fixed canonical mathlib values by
definitional equality; arbitrary function heads are never unfolded. Unsupported
or incompletely elaborated expressions return `none`.

Recognition preserves the supplied expression and the caller's metavariable
state. Domain obligations belong to consumers, not to this internal API. -/
def recognizeAtom? (expression : Expr) : MetaM (Option AtomApplication) := do
  let saved ← saveState
  try
    -- Existing metavariables must also remain rigid when hidden in a local
    -- declaration's type or value, where `expression.hasMVar` cannot see them.
    withNewMCtxDepth <| recognizeApplication? expression
  finally
    saved.restore

end Morew.Elab.Atom
