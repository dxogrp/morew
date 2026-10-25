/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Affine.Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Unsupported affine expressions and diagnostics

Nonlinear expressions, unproved denominators, and altered
operation instances must fail with an explanation of the unsupported expression.
Dimension mismatches remain ordinary Lean elaboration errors.
-/

namespace MorewTest.Affine.Unsupported

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Affine MorewTest.Affine Matrix
open scoped BigOperators

noncomputable abbrev customCoercion : Coe ℝ ℝ := ⟨fun x => x * x⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => x * x)) 0 (some ``HMul.hMul)
  assertUnsupported (← `(fun x : ℝ => x * x - x * x))
  assertUnsupported (← `(fun x : ℝ => 0 * Real.exp x))
  assertUnsupported (← `(fun x : ℝ × ℝ => x.1 * x.2))
  assertUnsupported (← `(fun x : ℝ => x / x))
  assertUnsupported (← `(fun x : ℝ => 1 / x))
  assertUnsupported (← `(fun x : ℝ => x / 0))
  assertUnsupported (← `(fun c : ℝ => fun x : ℝ => x / c)) 1
  assertUnsupported (← `(fun x : ℝ => x ^ (2 : ℕ)))
  assertUnsupported (← `(fun x : ℝ => Real.exp x))
  assertUnsupported (← `(fun x : ℝ => x + Real.exp x)) 0 (some ``Real.exp)
  assertUnsupported (← `(fun x : ℝ => Real.log x))
  assertUnsupported (← `(fun x : ℝ => Real.sqrt x))
  assertUnsupported (← `(fun x : ℝ => |x|))
  assertUnsupported (← `(fun x : ℝ => max x 0))
  assertUnsupported (← `(fun x : ℝ => @Coe.coe ℝ ℝ customCoercion x))
  assertUnsupported (← `(fun x : ℝ => let a := x + 1; a * x))
  assertUnsupported (← `(fun x : ℝ => let a := x; let b := a + 1; b * x))
  assertUnsupported (← `(fun x : ℝ => let a := x + 1; x / a))
  assertUnsupported (← `(fun x : ℝ => ![x, x * x]))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => x ⬝ᵥ x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => !![x 0, 1; 0, 1] *ᵥ x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => x ᵥ* !![x 0, 1; 0, 1]))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => x (if x 0 ≤ 0 then 0 else 1)))
  assertUnsupported (← `(fun x : ℝ =>
    ∑ _i ∈ ({0, 1} : Finset ℕ).filter (fun _ => x ≤ 0), x))
  assertUnsupported (← `(fun x : ℝ => ∑' _i : ℕ, x))
  assertUnsupported (← `(fun x : ℝ => if x ≤ 0 then x else 2 * x))
  assertUnsupported (← `(fun x : ℕ => (x : ℝ)))

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate (← `(fun c : ℝ => fun x : ℝ => x / c))
  lambdaBoundedTelescope expression 1 fun _ source => do
    let provider : Morew.Elab.Affine.EvidenceProvider :=
      { nonzeroEvidence? := some fun _ => return some (mkConst ``True.intro) }
    if (← reifyAffine source provider).isOk then
      throwError "accepted evidence that does not establish divisor nonzeroness"

/-! Matching the operation spelling alone is not a semantic guarantee. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun [HAdd ℝ ℝ ℝ] => fun x : ℝ => x + 1)) 1
  assertUnsupported (← `(fun [HMul ℝ ℝ ℝ] => fun x : ℝ => 2 * x)) 1
  assertUnsupported (← `(fun [HDiv ℝ ℝ ℝ] => fun x : ℝ => x / 2)) 1
  assertUnsupported (← `(fun [Neg ℝ] => fun x : ℝ => -x)) 1
  assertUnsupported (← `(fun (G : AddCommGroup ℝ) => fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨G.add⟩ x x)) 1
  assertUnsupported (← `(fun (M : Module ℝ (Fin 2 → ℝ)) => fun x : Fin 2 → ℝ =>
    @HSMul.hSMul ℝ (Fin 2 → ℝ) (Fin 2 → ℝ) ⟨M.smul⟩ (2 : ℝ) x)) 1
  assertUnsupported (← `(fun [AddCommMonoid ℝ] =>
    fun x : Fin 2 → ℝ => ∑ i, x i)) 1
  assertUnsupported (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a * b⟩ x x))
  assertUnsupported (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a _ => a + a⟩ x x))
  assertUnsupported (← `(fun x : ℝ =>
    @HMul.hMul ℝ ℝ ℝ ⟨fun a b => a * b * b⟩ 2 x))
  assertUnsupported (← `(fun x : ℝ =>
    @HSMul.hSMul ℝ ℝ ℝ ⟨fun a b => a * b * b⟩ 2 x))

/-! Matrix dimensions remain enforced by ordinary Lean elaboration. -/

/--
error: Application type mismatch: The argument
  x
has type
  Fin 2 → ℝ
but is expected to have type
  Fin 3 → ℝ
in the application
  A *ᵥ x
-/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 3) ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := A *ᵥ x

end MorewTest.Affine.Unsupported
