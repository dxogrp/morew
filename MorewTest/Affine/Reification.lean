/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Affine.Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Supported affine expressions

Kernel-checked recognition of scalar arithmetic, products, vectors, symbolic
sums, and constant-coefficient matrix operations.
-/

namespace MorewTest.Affine.Reification

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Affine MorewTest.Affine Matrix
open scoped BigOperators

private noncomputable abbrev canonicalAdd : HAdd ℝ ℝ ℝ := inferInstance

/-! Scalars, ordinary notation, and external parameters. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => x))
  assertAffine (← `(fun _ : ℝ => (7 : ℝ)))
  assertAffine (← `(fun x : ℝ => 2 * x + 3))
  assertAffine (← `(fun x : ℝ => x * 2 - 3))
  assertAffine (← `(fun x : ℝ => -x + (x - 4)))
  assertAffine (← `(fun x : ℝ => (2 : ℝ) • x))
  assertAffine (← `(fun x : ℝ => x • (2 : ℝ)))
  assertAffine (← `(fun x : ℝ => @HAdd.hAdd ℝ ℝ ℝ canonicalAdd x 1))
  assertAffine (← `(fun x : ℝ => x / 2))
  assertAffine (← `(fun x : ℝ => x / (-3)))
  assertAffine (← `(fun x : ℝ => x / (3 / 2)))
  assertAffine (← `(fun x : ℝ => x ^ (0 : ℕ)))
  assertAffine (← `(fun x : ℝ => (Real.exp x) ^ (0 : ℕ)))
  assertAffine (← `(fun x : ℝ => x ^ (1 : ℕ)))
  assertAffine (← `(fun x : ℝ => let y := x + 2; 3 * y - 1))
  assertAffine (← `(fun x : ℝ => (fun y : ℝ => 2 * y) (x + 1)))
  assertAffine (← `(fun a b : ℝ => fun x : ℝ => a * x + b)) 2
  assertAffine (← `(fun a : ℝ => fun x : ℝ => Real.exp a * x + Real.log a)) 1
  assertAffine (← `(fun c : ℝ => fun (_ : c ≠ 0) => fun x : ℝ => x / c)) 2

run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← elaborate (← `(fun x : ℝ => 2 * x + 1))
  let source := mkMData {} source
  match ← reifyAffine source with
  | .ok result => checkResult source result
  | .error error => throwError "metadata prevented affine recognition: {error.reason}"

/-! A consumer may provide a nonzero proof without extending the recognizer. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate
    (← `(fun c : ℝ => fun (_ : c ≠ 0 ∧ True) => fun x : ℝ => x / c))
  lambdaBoundedTelescope expression 2 fun parameters source => do
    let config : Morew.Elab.Affine.Config := {
      nonzeroEvidence? := some fun obligation => do
        let proof ← mkAppM ``And.left #[parameters[1]!]
        unless ← isDefEq (← inferType proof) obligation do return none
        return some proof
    }
    match ← reifyAffine source config with
    | .ok result => checkResult source result
    | .error error => throwError "did not use supplied nonzero evidence: {error.reason}"

/-! The domain follows the product grouping chosen by the modeling frontend. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ × ℝ => x.1 + 2 * x.2))
  assertAffine (← `(fun x : ℝ × (ℝ × ℝ) => x.1 - x.2.1 + x.2.2))
  assertAffine (← `(fun x : (ℝ × ℝ) × ℝ => x.1.1 + x.1.2 - x.2))
  assertAffine (← `(fun x : ℝ => (x + 1, 2 * x)))
  assertAffine (← `(fun x : ℝ × ℝ => (x.2, x.1 + x.2)))
  assertAffine (← `(fun x : ℝ × (Fin 2 → ℝ) => x.1 + x.2 0 - x.2 1))

/-! Vectors are reified without enumerating parameterized dimensions. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 2 → ℝ => x))
  assertAffine (← `(fun x : Fin 2 → ℝ => x 0 + x 1))
  assertAffine (← `(fun x : Fin 2 → ℝ => (2 : ℝ) • x + ![1, 2]))
  assertAffine (← `(fun x : Fin 2 → ℝ => (2 : ℕ) • x))
  assertAffine (← `(fun x : Fin 2 → ℝ => -x - ![1, 2]))
  assertAffine (← `(fun x : ℝ => ![x + 1, 2 * x, -x]))
  assertAffine (← `(fun _ : ℝ => (![] : Fin 0 → ℝ)))
  assertAffine (← `(fun x : ℝ => ![x]))
  assertAffine (← `(fun n : ℕ => fun x : Fin n → ℝ => fun i => x i + 1)) 1
  assertAffine (← `(fun n : ℕ => fun i : Fin n => fun x : Fin n → ℝ => x i)) 2
  assertAffine (← `(fun x : ℝ => fun i : Fin 2 => x + (i.val : ℝ)))

/-! Finite sums retain their symbolic set and binder. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 3 → ℝ => ∑ i, x i))
  assertAffine (← `(fun n : ℕ => fun x : Fin n → ℝ => ∑ i, 2 * x i + 1)) 1
  assertAffine (← `(fun s : Finset ℕ => fun x : ℝ => ∑ _i ∈ s, x + 1)) 1
  assertAffine (← `(fun x : ℝ => ∑ _i ∈ (∅ : Finset ℕ), x))
  assertAffine (← `(fun (ι : Type) [Fintype ι] => fun x : ι → ℝ => ∑ i, x i)) 2
  assertAffine (← `(fun x : Fin 2 → Fin 3 → ℝ => ∑ i, ∑ j, x i j))

/-! Dot products and rectangular matrix products, in both orientations. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 2 → ℝ => ![1, 2] ⬝ᵥ x))
  assertAffine (← `(fun x : Fin 2 → ℝ => x ⬝ᵥ ![1, 2]))
  assertAffine (← `(fun x : ℝ => ![1, 2] ⬝ᵥ ![x + 1, 2 * x]))
  assertAffine (← `(fun a : Fin 2 → ℝ => fun x : Fin 2 → ℝ => a ⬝ᵥ x)) 1
  assertAffine (← `(fun x : Fin 2 → ℝ => !![1, 2; 3, 4] *ᵥ x))
  assertAffine (← `(fun x : Fin 2 → ℝ => x ᵥ* !![1, 2; 3, 4]))
  assertAffine (← `(fun A : Matrix (Fin 3) (Fin 2) ℝ =>
    fun x : Fin 2 → ℝ => A *ᵥ x)) 1
  assertAffine (← `(fun A : Matrix (Fin 2) (Fin 3) ℝ =>
    fun x : Fin 2 → ℝ => x ᵥ* A)) 1
  assertAffine (← `(fun A : Matrix (Fin 2) (Fin 0) ℝ =>
    fun x : Fin 0 → ℝ => A *ᵥ x)) 1

end MorewTest.Affine.Reification
