/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.SmoothSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Structured rejection of unsupported smoothness expressions

Each input elaborates before certification. Assertions check the failure class,
original source, failing operand, and its type, so an unrelated elaboration
error cannot satisfy a negative test.
-/

namespace MorewTest.NLP.Smooth

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.NLP.Smooth

private noncomputable def hiddenSquare (x : ℝ) : ℝ := x * x
private noncomputable abbrev inlineSquare (x : ℝ) : ℝ := x * x
private noncomputable def ignoredArgument (_x : ℝ) : ℝ := 0

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => Real.log x)) .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => x + Real.log x)) .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun n : ℕ => fun x : Fin n → ℝ => ∑ i, Real.log (x i)))
    .restrictedDomain 1 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => Real.sqrt x)) .restrictedDomain 0 (some ``Real.sqrt)
  assertRejected (← `(fun x : ℝ => x / 2)) .restrictedDomain 0 (some ``HDiv.hDiv)
  assertRejected (← `(fun x : ℝ => 1 / x)) .restrictedDomain 0 (some ``HDiv.hDiv)
  assertRejected (← `(fun c : ℝ => fun (_ : c ≠ 0) => fun x : ℝ => x / c))
    .restrictedDomain 2 (some ``HDiv.hDiv)
  assertRejected (← `(fun x : ℝ => x⁻¹)) .restrictedDomain 0 (some ``Inv.inv)
  assertRejected (← `(fun x : ℝ => |x|)) .nonsmooth 0 (some ``abs)
  assertRejected (← `(fun x : ℝ => max x 0)) .nonsmooth 0 (some ``max)
  assertRejected (← `(fun x : ℝ => min x 0)) .nonsmooth 0 (some ``min)

/-! Unsupported subexpressions are not removed by algebraic cancellation. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => 0 * Real.log x)) .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => Real.log x - Real.log x))
    .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => (Real.log x) ^ (0 : ℕ)))
    .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => ∑ _i ∈ (∅ : Finset ℕ), Real.log x))
    .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => |x| - |x|)) .nonsmooth 0 (some ``abs)

/-! Disabling expansion retains the original named-helper boundary. -/

set_option morew.smooth.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => hiddenSquare x)) .unknownHead 0 (some ``hiddenSquare)
  assertRejected (← `(fun x : ℝ => inlineSquare x)) .unknownHead 0 (some ``inlineSquare)
  assertRejected (← `(fun x : ℝ => ignoredArgument x)) .unknownHead 0 (some ``ignoredArgument)
  assertRejected (← `(hiddenSquare ∘ Real.exp)) .unknownHead 0 (some ``hiddenSquare)
  assertRejected (← `(Real.exp ∘ hiddenSquare)) .unknownHead 0 (some ``hiddenSquare)
  assertRejected (← `(fun x : ℝ => let f := hiddenSquare; f x))
    .unknownHead 0 (some ``hiddenSquare)

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => hiddenSquare x))
  assertSmooth (← `(fun x : ℝ => inlineSquare x))
  assertSmooth (← `(fun x : ℝ => ignoredArgument x))
  assertSmooth (← `(hiddenSquare ∘ Real.exp))
  assertSmooth (← `(Real.exp ∘ hiddenSquare))
  assertSmooth (← `(fun x : ℝ => let f := hiddenSquare; f x))
  assertRejected (← `(fun f : ℝ → ℝ => fun x : ℝ => f x)) .unknownHead 1
  assertRejected (← `(fun x : ℝ => hiddenSquare (Real.log x)))
    .restrictedDomain 0 (some ``Real.log)
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => hiddenSquare c + x)) 1
  assertSmooth (← `(fun x : ℝ => let f := fun y : ℝ => y * y; f x))

/-! Selecting a model field must not unfold a named decision-dependent model
builder. Independent models and literal local containers remain structural. -/

private noncomputable def squareModel (c : ℝ) : Morew.Problem ℝ ℝ where
  objective := fun y => c * c + y * y
  feasible := fun _ => True

private noncomputable abbrev inlineSquareModel (c : ℝ) : Morew.Problem ℝ ℝ :=
  ⟨fun y => c * c + y * y, fun _ => True⟩

private noncomputable def constantModel (_c : ℝ) : Morew.Problem ℝ ℝ where
  objective := fun _ => 1
  feasible := fun _ => True

private def exponentModel (_c : ℝ) : Morew.Problem ℝ ℕ where
  objective := fun _ => 2
  feasible := fun _ => True

private noncomputable def independentModel : Morew.Problem ℝ ℝ where
  objective := fun x => x * x
  feasible := fun _ => True

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => (squareModel x).objective 0)) .unknownHead
  assertRejected (← `(fun x : ℝ => (inlineSquareModel x).objective 0)) .unknownHead
  assertRejected (← `(fun x : ℝ => let p := squareModel x; p.objective 0)) .unknownHead
  assertRejected (← `(fun x : ℝ => Real.log ((constantModel x).objective 0)))
    .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => x ^ (exponentModel x).objective 0)) .dependency
  assertSmooth (← `(fun x : ℝ =>
    (Morew.Problem.mk (fun y : ℝ => x * y) (fun _ => True)).objective x))
  assertSmooth (← `(fun x : ℝ =>
    let p : Morew.Problem ℝ ℝ := ⟨fun y => x * y, fun _ => True⟩
    p.objective x))
  assertSmooth (← `(independentModel.objective))
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => (squareModel c).objective x)) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => (inlineSquareModel c).objective x)) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => Real.log ((constantModel c).objective x))) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => x ^ (exponentModel c).objective 0)) 1
  assertSmooth (← `(fun x : ℝ => (squareModel ((fun _ : ℝ => 2) x)).objective x))
  assertSmooth (← `(fun x : ℝ => (squareModel (let _y := x; 2)).objective x))
  assertSmooth (← `(fun x : ℝ => (squareModel ((2 : ℝ), x).1).objective x))
  assertSmooth (← `(fun x : ℝ =>
    (squareModel (((fun _ : ℝ => 2) ∘ (fun y => y * y)) x)).objective x))

/-! Different operation instances cannot borrow native smoothness theorems. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun [HAdd ℝ ℝ ℝ] => fun x : ℝ => x + x)) .invalidInstance 1
  assertRejected (← `(fun [HSub ℝ ℝ ℝ] => fun x : ℝ => x - x)) .invalidInstance 1
  assertRejected (← `(fun [HMul ℝ ℝ ℝ] => fun x : ℝ => x * x)) .invalidInstance 1
  assertRejected (← `(fun [Neg ℝ] => fun x : ℝ => -x)) .invalidInstance 1
  assertRejected (← `(fun [HPow ℝ ℕ ℝ] => fun x : ℝ => x ^ (2 : ℕ))) .invalidInstance 1
  assertRejected (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a _ => |a|⟩ x x)) .invalidInstance
  assertRejected (← `(fun x : ℝ =>
    @HMul.hMul ℝ ℝ ℝ ⟨fun a _ => |a|⟩ x x)) .invalidInstance
  -- The altered operations coincide with native arithmetic on these operands;
  -- that coincidence does not establish that their instances are native.
  assertRejected (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun _ b => b + b⟩ x x)) .invalidInstance
  assertRejected (← `(fun x : ℝ =>
    @HMul.hMul ℝ ℝ ℝ ⟨fun _ b => b * b⟩ x x)) .invalidInstance
  assertRejected (← `(fun x : ℝ =>
    @Neg.neg ℝ ⟨fun a => |a|⟩ x)) .invalidInstance
  assertRejected (← `(fun x : ℝ =>
    @HPow.hPow ℝ ℕ ℝ ⟨fun a _ => |a|⟩ x 2)) .invalidInstance
  assertRejected (← `(fun [AddCommMonoid ℝ] => fun x : Fin 2 → ℝ => ∑ i, x i))
    .invalidInstance 1
  assertSmooth (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a _ => |a|⟩ 2 3 + x))

/-! The initial decision-space whitelist is intentionally narrower than all
finite-dimensional normed spaces. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℕ => (x : ℝ))) .unsupportedSpace
  assertRejected (← `(fun x : ℚ => (x : ℝ))) .unsupportedSpace
  assertRejected (← `(fun x : Bool → ℝ => x true)) .unsupportedSpace
  assertRejected (← `(fun x : ℕ → ℝ => x 0)) .unsupportedSpace
  assertRejected (← `(fun x : ℝ => (x, x))) .unsupportedSpace

end MorewTest.NLP.Smooth
