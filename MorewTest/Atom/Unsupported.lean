/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Atom.Support

/-!
# Atom recognition boundaries
-/

namespace MorewTest.Atom.Unsupported

open Lean Lean.Meta Lean.Elab.Term
open Morew Morew.Elab.Atom

/-! Recognition is intentionally bounded by typed heads and canonical instances. -/

noncomputable def equivalentExponential (x : ℝ) : ℝ := Real.exp (x + 0)

noncomputable abbrev sineAlias (x : ℝ) : ℝ := Real.sin x

noncomputable abbrev hyperbolicTangentAlias (x : ℝ) : ℝ := Real.tanh x

noncomputable def realPowerWrapper (x y : ℝ) : ℝ := Real.rpow x y

noncomputable abbrev realPowerAlias (x y : ℝ) : ℝ := x ^ y

theorem equivalentExponential_eq (x : ℝ) :
    equivalentExponential x = Real.exp x := by
  simp [equivalentExponential]

namespace Shadowed

def exp (x : ℝ) : ℝ := x

def sin (x : ℝ) : ℝ := x

def tanh (x : ℝ) : ℝ := x

def rpow (x _y : ℝ) : ℝ := x

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => exp x))
  assertUnsupported (← `(fun x : ℝ => sin x))
  assertUnsupported (← `(fun x : ℝ => tanh x))
  assertUnsupported (← `(fun x y : ℝ => rpow x y))

end Shadowed

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => exponentialAlias x))
  assertUnsupported (← `(fun x : ℝ => equivalentExponential x))
  assertUnsupported (← `(fun x : ℝ => sineAlias x))
  assertUnsupported (← `(fun x : ℝ => hyperbolicTangentAlias x))
  assertUnsupported (← `(fun x y : ℝ => realPowerWrapper x y))
  assertUnsupported (← `(fun x y : ℝ => realPowerAlias x y))
  assertUnsupported (← `(fun f : ℝ → ℝ → ℝ => fun x y : ℝ => f x y))
  assertUnsupported (← `(fun x : ℝ => Real.tan x))
  assertUnsupported (← `(fun x : ℂ => Complex.sin x))
  assertUnsupported (← `(fun x : ℂ => Complex.cos x))
  assertUnsupported (← `(fun x : ℂ => Complex.sinh x))
  assertUnsupported (← `(fun x : ℂ => Complex.cosh x))
  assertUnsupported (← `(fun x : ℂ => Complex.tanh x))
  assertUnsupported (← `(fun x : ℚ => x⁻¹))
  assertUnsupported (← `(fun x : ℤ => |x|))
  assertUnsupported (← `(fun x : ℤ => x⁺))
  assertUnsupported (← `(fun x y : ℕ => max x y))
  assertUnsupported (← `(fun x y : ℕ => min x y))
  assertUnsupported (← `(Real.exp))
  assertUnsupported (← `(Real.sin))
  assertUnsupported (← `(Real.cos))
  assertUnsupported (← `(Real.sinh))
  assertUnsupported (← `(Real.cosh))
  assertUnsupported (← `(Real.tanh))
  assertUnsupported (← `(Real.rpow))
  assertUnsupported (← `(fun x : ℝ => Real.rpow x))
  assertUnsupported (← `(fun x : ℝ => (HPow.hPow x : ℝ → ℝ)))
  -- Natural powers remain outside the real-exponent atom classification.
  assertUnsupported (← `(fun x : ℝ => x ^ (2 : ℕ)))
  assertUnsupported (← `(fun x : ℝ => fun n : ℕ => x ^ n))
  assertUnsupported (← `((Inv.inv : ℝ → ℝ)))
  assertUnsupported (← `((abs : ℝ → ℝ)))
  assertUnsupported (← `((posPart : ℝ → ℝ)))
  assertUnsupported (← `(fun x : ℝ => max x))
  assertUnsupported (← `(fun x : ℝ => min x))
  assertUnsupported (← `(fun [Inv ℝ] (x : ℝ) => x⁻¹))
  assertUnsupported (← `(fun [Max ℝ] (x y : ℝ) => max x y))
  assertUnsupported (← `(fun [Min ℝ] (x y : ℝ) => min x y))
  assertUnsupported (← `(fun [Lattice ℝ] (x : ℝ) => |x|))
  assertUnsupported (← `(fun [AddGroup ℝ] (x : ℝ) => |x|))
  assertUnsupported (← `(fun [PosPart ℝ] (x : ℝ) => x⁺))
  assertUnsupported (← `(fun [Lattice ℝ] (x : ℝ) => x⁺))
  assertUnsupported (← `(fun [SubNegMonoid ℝ] (x : ℝ) => x⁺))
  assertUnsupported (← `(fun [Pow ℝ ℝ] (x y : ℝ) => x ^ y))
  assertUnsupported (← `(fun [HPow ℝ ℝ ℝ] (x y : ℝ) => x ^ y))

private noncomputable abbrev canonicalInverse : Inv ℝ := inferInstance

private noncomputable abbrev canonicalRealPower : HPow ℝ ℝ ℝ := inferInstance

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAtom (← `(fun x : ℝ => @Inv.inv ℝ canonicalInverse x)) .inv #[0]
  assertAtom (← `(fun x y : ℝ => @HPow.hPow ℝ ℝ ℝ canonicalRealPower x y)) .rpow #[0, 1]
  assertAtom (← `(fun [Pow ℝ ℝ] (x y : ℝ) =>
    @HPow.hPow ℝ ℝ ℝ canonicalRealPower x y)) .rpow #[1, 2]
  assertUnsupported (← `(fun x : ℝ => @Inv.inv ℝ ⟨fun _ => 0⟩ x))
  assertUnsupported (← `(fun x y : ℝ => @max ℝ ⟨fun a _ => a⟩ x y))
  assertUnsupported (← `(fun x y : ℝ => @min ℝ ⟨fun _ b => b⟩ x y))
  assertUnsupported (← `(fun x : ℝ => @posPart ℝ ⟨fun _ => 0⟩ x))
  assertUnsupported (← `(fun x : ℝ =>
    @abs ℝ (inferInstanceAs (Lattice (OrderDual ℝ))) Real.instAddGroup x))
  assertUnsupported (← `(fun x y : ℝ =>
    @HPow.hPow ℝ ℝ ℝ ⟨fun a b => a + b⟩ x y))
  assertUnsupported (← `(fun x y : ℝ =>
    @HPow.hPow ℝ ℝ ℝ (@instHPow ℝ ℝ ⟨fun a b => a + b⟩) x y))

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let instanceType ← elaborate (← `(Inv ℝ))
  let unresolvedInstance ← mkFreshExprMVar instanceType
  withLocalDeclD `x real fun x => do
    let expression := mkAppN (mkConst ``Inv.inv [Level.zero]) #[real, unresolvedInstance, x]
    if (← recognizeAtom? expression).isSome then
      throwError "recognized an unresolved inverse instance"
    if ← unresolvedInstance.mvarId!.isAssigned then
      throwError "recognition assigned an instance metavariable"
    withLetDecl `hiddenInstance instanceType unresolvedInstance fun hiddenInstance => do
      let expression := mkAppN (mkConst ``Inv.inv [Level.zero]) #[real, hiddenInstance, x]
      if expression.hasMVar then
        throwError "the hidden-instance regression no longer hides its metavariable"
      if (← recognizeAtom? expression).isSome then
        throwError "recognized an unresolved inverse instance hidden behind a local let"
      if ← unresolvedInstance.mvarId!.isAssigned then
        throwError "recognition assigned a hidden instance metavariable"

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let missing ← mkFreshExprMVar real
  let two ← mkNumeral real 2
  for expression in #[mkApp2 (mkConst ``Real.rpow) missing two,
      mkApp2 (mkConst ``Real.rpow) two missing] do
    if (← recognizeAtom? expression).isSome then
      throwError "recognized a real power with an unresolved operand"
    if ← missing.mvarId!.isAssigned then
      throwError "real-power recognition assigned an operand metavariable"

  let instanceType ← elaborate (← `(HPow ℝ ℝ ℝ))
  let missingInstance ← mkFreshExprMVar instanceType
  let makePower := fun operation =>
    mkAppN (mkConst ``HPow.hPow [.zero, .zero, .zero])
      #[real, real, real, operation, two, two]
  if (← recognizeAtom? (makePower missingInstance)).isSome then
    throwError "recognized an unresolved real-power instance"
  withLetDecl `hiddenPower instanceType missingInstance fun hidden => do
    let expression := makePower hidden
    if expression.hasMVar then
      throwError "hidden real-power instance regression no longer hides its metavariable"
    if (← recognizeAtom? expression).isSome then
      throwError "recognized an unresolved real-power instance hidden in a local let"
  if ← missingInstance.mvarId!.isAssigned then
    throwError "real-power recognition assigned an instance metavariable"

  let missingType ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `exponent missingType fun exponent => do
    let expression := mkApp2 (mkConst ``Real.rpow) two exponent
    if expression.hasMVar then
      throwError "hidden exponent-type regression no longer hides its metavariable"
    if (← recognizeAtom? expression).isSome then
      throwError "recognized a real power with an unresolved exponent type"
  if ← missingType.mvarId!.isAssigned then
    throwError "real-power recognition assigned an exponent type"

end MorewTest.Atom.Unsupported
