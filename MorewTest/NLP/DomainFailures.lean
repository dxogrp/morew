/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.DomainSupport

/-!
# Structured rejection of unsupported domains and feasibility rows

Every input elaborates before certification. Rejections retain the original
source, its position, the local obstruction, and any missing domain condition.
-/

namespace MorewTest.NLP.Domain

open Lean Lean.Meta Lean.Elab.Term

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomainRejected (← `(((fun x : ℝ => 0 ≤ x), #[fun x : ℝ => Real.log x])))
    .feasibleInclusion 0 (some 0) none (some ``Real.log)
  assertDomainRejected (← `(((fun x : ℝ => 0 ≤ x), #[fun x : ℝ => Real.sqrt x])))
    .feasibleInclusion 0 (some 0) none (some ``Real.sqrt)
  assertDomainRejected (← `(((fun x : ℝ => 0 ≤ x), #[fun x : ℝ => x⁻¹])))
    .feasibleInclusion 0 (some 0) none (some ``Inv.inv)
  assertDomainRejected (← `(((fun x : ℝ => 0 ≤ x), #[fun x : ℝ => 1 / x])))
    .feasibleInclusion 0 (some 0) none (some ``HDiv.hDiv)
  assertDomainRejected (← `(((fun x : ℝ => 0 ≤ x), #[fun x : ℝ => x ^ (2 : ℝ)])))
    .feasibleInclusion 0 (some 0) none (some ``HPow.hPow)
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => Real.log (Real.log x)])))
    .feasibleInclusion 0 (some 0) none (some ``Real.log)
  assertDomainRejected (← `(((fun _x : ℝ => True), #[fun _x : ℝ => Real.log 0])))
    .feasibleInclusion 0 (some 0) none (some ``Real.log)
  assertDomainRejected (← `(((fun _x : ℝ => True), #[fun _x : ℝ => Real.log (-1)])))
    .feasibleInclusion 0 (some 0) none (some ``Real.log)
  assertDomainRejected (← `(((fun _x : ℝ => True), #[fun _x : ℝ => Real.sqrt 0])))
    .feasibleInclusion 0 (some 0) none (some ``Real.sqrt)
  assertDomainRejected (← `(((fun _x : ℝ => True), #[fun _x : ℝ => (0 : ℝ)⁻¹])))
    .feasibleInclusion 0 (some 0) none (some ``Inv.inv)
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => Real.exp x, fun x : ℝ => Real.log x])))
    .feasibleInclusion 0 (some 1) none (some ``Real.log)

-- A missing positivity obligation identifies exactly the logarithm's argument.
run_cmd Lean.Elab.Command.liftTermElabM do
  withInput (← `(((fun x : ℝ => 0 ≤ x), #[fun x : ℝ => Real.log (x + 0)]))) 0
      fun feasible sources => do
    let error ← checkFailure feasible sources .feasibleInclusion (some 0)
      none (some ``Real.log)
    let some obligation := error.obligation? | throwError "missing domain condition"
    unless obligation.isAppOfArity ``LT.lt 4 &&
        obligation.getAppArgs[3]! == error.expression.getAppArgs[0]! do
      throwError "domain diagnostic changed the missing positivity condition"

/-! Real exponents must be fixed, including the direct native spelling. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => x ^ x]))) .dependency
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => Real.rpow 2 x]))) .dependency
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x),
    #[fun x : ℝ => x ^ Real.log 0]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => Real.exp (Real.log x - Real.log x)]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True), #[fun x : ℝ => 0 * Real.log x])))
    .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True), #[fun x : ℝ => (Real.log x) ^ (0 : Nat)])))
    .feasibleInclusion

/-! The whole feasibility predicate is admitted before looking at any sources. -/

private def hiddenPredicate (x : ℝ) : Prop := 1 ≤ x
private abbrev inlinePredicate (x : ℝ) : Prop := 1 ≤ x

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomainRejected (← `(((fun x : ℝ => 0 < x), (#[] : Array (ℝ → ℝ)))))
    .unsupportedRow 0 none (some 0)
  assertDomainRejected (← `(((fun x : ℝ => x ≠ 0), #[fun x : ℝ => x * x])))
    .unsupportedRow 0 none (some 0)
  assertDomainRejected (← `(((fun x : ℝ => x ≤ -1 ∨ 1 ≤ x), #[fun x : ℝ => x])))
    .unsupportedRow 0 none (some 0)
  assertDomainRejected (← `(((fun x : ℝ => ∀ y : ℝ, y ≤ x), (#[] : Array (ℝ → ℝ)))))
    .unsupportedRow 0 none (some 0)
  assertDomainRejected (← `(((fun x : ℝ => ∃ y : ℝ, x = y), #[fun x : ℝ => Real.exp x])))
    .unsupportedRow 0 none (some 0)
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x ∧ (True ∧ x ≠ 0)),
    #[fun x : ℝ => Real.log x]))) .unsupportedRow 0 none (some 2)
  assertDomainRejected (← `(((fun x : ℝ => hiddenPredicate x), #[fun x : ℝ => Real.log x])))
    .unsupportedRow 0 none (some 0) (some ``hiddenPredicate)
  assertDomainRejected (← `(((fun x : ℝ => inlinePredicate x), (#[] : Array (ℝ → ℝ)))))
    .unsupportedRow 0 none (some 0) (some ``inlinePredicate)
  assertDomainRejected (← `(((fun _x : ℝ => (1 : Nat) = 1), #[fun x : ℝ => x])))
    .unsupportedRow 0 none (some 0)
  assertDomainRejected (← `(fun [LE ℝ] =>
    ((fun x : ℝ => x ≤ x), #[fun x : ℝ => x]))) .unsupportedRow 1 none (some 0)
  assertDomainRejected (← `(((fun x : ℝ => @LE.le ℝ ⟨fun _ _ => True⟩ 1 x),
    #[fun x : ℝ => Real.log x]))) .unsupportedRow 0 none (some 0)

/-! A shadowed name cannot transfer positivity to another decision variable. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomainRejected (← `(fun x : ℝ => fun _hx : 0 < x =>
    ((fun _y : ℝ => True), #[fun x : ℝ => Real.log x]))) .feasibleInclusion 2
  assertDomainRejected (← `(((fun x : ℝ => 0 ≤ x),
    #[fun x : ℝ => let log := fun y : ℝ => Real.log y; log x]))) .feasibleInclusion
  -- Structural reduction must still expose selected restricted tuple values.
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => x + (Real.log 0, (0 : Nat)).1]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => let p := ((0 : Nat), Real.log 0); x + p.2]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => x + (let p := (Real.log 0, (0 : Nat)); p).1]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => x + (let p := ((0 : Nat), Real.log 0); p).2]))) .feasibleInclusion

private noncomputable def hiddenSquare (x : ℝ) : ℝ := x * x
private noncomputable abbrev inlineSquare (x : ℝ) : ℝ := x * x
private noncomputable def ignoredScalar (_value : ℝ) : ℝ := 0
private noncomputable def ignoredPair (_value : ℝ × ℝ) : ℝ := 0
private noncomputable def ignoredVector (_value : Fin 2 → ℝ) : ℝ := 0

/-! Helpers do not unfold, and constant helper arguments keep their own requirements. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => hiddenSquare x])))
    .unknownHead 0 (some 0) none (some ``hiddenSquare)
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => inlineSquare x])))
    .unknownHead 0 (some 0) none (some ``inlineSquare)
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x),
    #[fun x : ℝ => ignoredScalar (Real.log x)])))
    .unknownHead 0 (some 0) none (some ``ignoredScalar)
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredScalar (Real.log x)])))
    .feasibleInclusion 0 (some 0) none (some ``Real.log)
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun _x : ℝ => ignoredScalar (Real.log 0)]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun _x : ℝ => ignoredPair (Real.log 0, 1)]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun _x : ℝ => ignoredVector (fun _i => Real.log 0)]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredVector
      ((fun _i => Real.log 0) * (fun _i => (0 : ℝ))) + x]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredVector ((fun _i => Real.log 0) ^ (0 : Nat)) + x])))
    .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredPair ((Real.log 0, (1 : ℝ)) * (0, 0)) + x])))
    .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredPair (((1 : ℝ), Real.sqrt 0) ^ (0 : Nat)) + x])))
    .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ∑ _i ∈ (∅ : Finset Nat), hiddenSquare x]))) .unknownHead
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ∑ _i ∈ (∅ : Finset Nat), |x|]))) .nonsmooth
  assertDomainRejected (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => |x|]))) .nonsmooth

/-! Altered arithmetic instances cannot reuse the native restricted-operation rules. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomainRejected (← `(fun [HDiv ℝ ℝ ℝ] =>
    ((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => x / x]))) .invalidInstance 1
  assertDomainRejected (← `(fun [Inv ℝ] =>
    ((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => x⁻¹]))) .invalidInstance 1
  assertDomainRejected (← `(fun [HPow ℝ ℝ ℝ] =>
    ((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => x ^ (2 : ℝ)]))) .invalidInstance 1
  assertDomainRejected (← `(fun [HAdd ℝ ℝ ℝ] =>
    ((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => Real.log (x + x)]))) .invalidInstance 1
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => @HDiv.hDiv ℝ ℝ ℝ ⟨fun a _ => |a|⟩ x 1]))) .invalidInstance
  assertDomainRejected (← `(fun [HMul (Fin 2 → ℝ) (Fin 2 → ℝ) (Fin 2 → ℝ)] =>
    ((fun _x : ℝ => True), #[fun x : ℝ => ignoredVector
      ((fun _i : Fin 2 => (2 : ℝ)) * (fun _i : Fin 2 => (3 : ℝ))) + x])))
    .invalidInstance 1
  assertDomainRejected (← `(fun [Mul ℝ] => ((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredPair (((2 : ℝ), (3 : ℝ)) * (4, 5)) + x]))) .invalidInstance 1
  assertDomainRejected (← `(fun [Pow (Fin 2 → ℝ) Nat] => ((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredVector ((fun _i => (2 : ℝ)) ^ (2 : Nat)) + x])))
    .invalidInstance 1
  assertDomainRejected (← `(fun [HPow (ℝ × ℝ) Nat (ℝ × ℝ)] => ((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredPair (((2 : ℝ), (3 : ℝ)) ^ (2 : Nat)) + x])))
    .invalidInstance 1
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredVector
      (@HMul.hMul (Fin 2 → ℝ) (Fin 2 → ℝ) (Fin 2 → ℝ)
        ⟨fun _ _ => fun _ => 0⟩ (fun _ => 0) (fun _ => 0)) + x]))) .invalidInstance
  -- The fallback is only for fixed values; it adds no vector calculus rule.
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredVector ((fun _i => x) * (fun _i => (2 : ℝ)))])))
    .invalidInstance

run_cmd Lean.Elab.Command.liftTermElabM do
  withInput (← `(fun [Pow (Fin 2 → ℝ) Nat] => ((fun _x : ℝ => True),
    #[fun x : ℝ => ignoredVector ((fun _i => (2 : ℝ)) ^ (2 : Nat)) + x]))) 1
      fun feasible sources => do
    discard <| checkFailure feasible sources .invalidInstance (some 0)
    -- The global API still treats fixed operations as arbitrary constants.
    discard <| MorewTest.NLP.Smooth.checkSuccess sources[0]!

/-! Empty source arrays still require a supported analytic decision space. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => x + Real.log 0 ^ (-1 : ℤ)]))) .feasibleInclusion
  assertDomainRejected (← `(((fun _x : ℕ => True), (#[] : Array (ℕ → ℝ)))))
    .unsupportedSpace 0 none

end MorewTest.NLP.Domain
