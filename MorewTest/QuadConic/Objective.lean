/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.QuadConic
import MorewTest.ElabSupport
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Exact objective recognition, independent curvature evidence, and failures. -/

namespace MorewTest.QuadConic.Objective

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.QuadConic MorewTest.Affine Matrix
open scoped BigOperators

private def assertQuadratic (term : TSyntax `term) (parameterCount : Nat := 0)
    (sense : Morew.ObjectiveSense := .minimize) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let result ← match ← reifyQuadratic source sense with
      | .ok result => pure result
      | .error error => throwError "quadratic recognition failed for {source}: {error.reason}"
    for proof in #[result.quadratic, result.affine, result.pointwiseEquality, result.curvature] do
      if proof.hasMVar || proof.hasSorry then throwError "incomplete quadratic certificate"
      checkWithKernel proof
    let sense := Lean.mkConst <| match sense with
      | .minimize => ``Morew.ObjectiveSense.minimize
      | .maximize => ``Morew.ObjectiveSense.maximize
    let .forallE _ domain _ _ ← whnf (← inferType source)
      | throwError "quadratic test objective is not a function"
    let expected ← Morew.Elab.Affine.Space.withCanonicalSpaces #[domain] do
      mkAppM ``Morew.QuadConic.Curvature #[sense, result.quadratic]
    unless ← isDefEq (← inferType result.curvature) expected do
      throwError "quadratic certificate has the wrong curvature"

private def assertRejected (term : TSyntax `term) (parameterCount : Nat := 0)
    (sense : Morew.ObjectiveSense := .minimize) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    match ← reifyQuadratic source sense with
    | .ok _ => throwError "unexpected quadratic recognition of {source}"
    | .error error =>
      if (← error.reason.toString).isEmpty then throwError "missing quadratic failure diagnostic"

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun x : ℝ => (x + 3) ^ 2))
  assertQuadratic (← `(fun x : ℝ => 2 * (x + 3) ^ 2 + 7 * x + 11))
  assertQuadratic (← `(fun x : ℝ => (x + 3) ^ 2 * 2 + 7 * x + 11))
  assertQuadratic (← `(fun x : ℝ => (2 : ℝ) • (x + 3) ^ 2))
  assertQuadratic (← `(fun x : ℝ => (x + 3) ^ 2 / 2))
  assertQuadratic (← `(fun x : ℝ => (x + 3) ^ 2 / (-2))) 0 .maximize
  assertQuadratic (← `(fun c : ℝ => fun x : ℝ => c * x + 7)) 1
  assertQuadratic (← `(fun c : ℝ => fun x : ℝ => c * x + 7)) 1 .maximize
  assertQuadratic (← `(fun c : ℝ => fun x : ℝ => c * (0 * x ^ 2))) 1
  assertQuadratic (← `(fun c : ℝ => fun x : ℝ => c * (0 * x ^ 2))) 1 .maximize
  assertQuadratic (← `(fun c : ℝ => fun (_ : 0 ≤ c) => fun x : ℝ => c * (x + 1)^2)) 2
  assertQuadratic (← `(fun c : ℝ => fun (_ : c ≤ 0) => fun x : ℝ => c * (x + 1)^2)) 2 .maximize
  assertQuadratic (← `(fun c : ℝ => fun (_ : 0 ≤ c) => fun x : ℝ => -c * (x + 1)^2)) 2 .maximize
  assertQuadratic (← `(fun x : ℝ => 3 * x - (x + 1)^2 - (2*x)^2)) 0 .maximize
  assertQuadratic (← `(fun x : ℝ => -(-(x + 1)^2)))
  assertQuadratic (← `(fun c : ℝ => fun (_ : 0 < c) => fun x : ℝ => (x / c)^2)) 2
  assertQuadratic (← `(fun c : ℝ => fun (_ : 0 < c) => fun x : ℝ => x^2 / c)) 2
  assertQuadratic (← `(fun c : ℝ => fun (_ : c < 0) => fun x : ℝ => x^2 / c)) 2 .maximize

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun x : Fin 2 → ℝ => Morew.Fn.norm2 (x - ![1, 2]) ^ 2))
  assertQuadratic (← `(fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2))
  assertQuadratic (← `(fun x : Fin 0 → ℝ => Morew.Fn.norm2 x ^ 2))
  assertQuadratic (← `(fun x : Fin 0 → ℝ => Morew.Fn.norm2 x ^ 2)) 0 .maximize
  assertQuadratic (← `(fun c : ℝ => fun x : Fin 0 → ℝ => c * Morew.Fn.norm2 x ^ 2)) 1 .maximize
  assertQuadratic (← `(fun x : EuclideanSpace ℝ (Fin 0) => ‖x‖ ^ 2)) 0 .maximize
  assertQuadratic (← `(fun (m n : Nat) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) =>
    fun x : Fin n → ℝ => Morew.Fn.norm2 (A *ᵥ x - b) ^ 2)) 4
  assertQuadratic (← `(fun (n : Nat) => fun x : Fin n → ℝ => ∑ i, (x i + 1)^2)) 1
  assertQuadratic (← `(fun (ι : Type) [Fintype ι] (w : ι → ℝ) (_ : ∀ i, 0 ≤ w i) =>
    fun x : ι → ℝ => ∑ i, w i * (x i + 1)^2)) 4
  assertQuadratic (← `(fun (s : Finset ℕ) (w : ℕ → ℝ) (_ : ∀ i, w i ≤ 0) =>
    fun x : ℝ => ∑ i ∈ s, w i * (x + i)^2)) 3 .maximize
  assertQuadratic (← `(fun (w : Fin 2 → Fin 3 → ℝ) (_ : ∀ i j, 0 ≤ w i j) =>
    fun x : Fin 2 → Fin 3 → ℝ => ∑ i, ∑ j, w i j * (x i j)^2)) 2
  assertQuadratic (← `(fun (w : ℕ → ℝ) =>
    fun x : ℝ => ∑ i ∈ (∅ : Finset ℕ), w i * x^2)) 1
  assertQuadratic (← `(fun (w : Fin 0 → ℝ) =>
    fun x : ℝ => ∑ i, w i * x^2)) 1 .maximize

/-! Bounded parameter evidence is retained within the exact finite support. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun (s : Finset ℕ) (w : ℕ → ℝ) (_ : ∀ i ∈ s, 0 ≤ w i) =>
    fun x : ℝ => ∑ i ∈ s, w i * (x + i)^2)) 3

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun (s : Finset ℕ) (t : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (_ : ∀ i ∈ s, ∀ j ∈ t i, 0 ≤ w i j) =>
    fun x : ℝ => ∑ i ∈ s, ∑ j ∈ t i, w i j * (x + i + j)^2)) 4

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun (s : Finset ℕ) (t : ℕ → Finset ℕ)
    (w : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (_ : ∀ i ∈ s, w i ≤ 0) (_ : ∀ i j, v i j ≤ 0) =>
    fun x : ℝ => ∑ i ∈ s, (w i*x^2 + (∑ j ∈ t i, v i j*(x + j)^2)))) 6 .maximize

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun (s : Finset ℕ) (d : ℕ → ℝ) (_ : ∀ i ∈ s, 0 < d i) =>
    fun x : ℝ => ∑ i ∈ s, x^2 / d i)) 3

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun (s : Finset ℕ) (d : ℕ → ℝ) (_ : ∀ i ∈ s, 0 < d i) =>
    fun x : ℝ => ∑ i ∈ s, (x / d i)^2)) 3

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun (s t : Finset ℕ) (w : ℕ → ℝ) (_ : ∀ i ∈ t, 0 ≤ w i) =>
    fun x : ℝ => ∑ i ∈ s, w i*x^2)) 4
  assertRejected (← `(fun (s : Finset ℕ) (t u : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (_ : ∀ i ∈ s, ∀ j ∈ u i, 0 ≤ w i j) =>
    fun x : ℝ => ∑ i ∈ s, ∑ j ∈ t i, w i j*x^2)) 5
  assertRejected (← `(fun (s t : Finset ℕ) (d : ℕ → ℝ) (_ : ∀ i ∈ t, 0 < d i) =>
    fun x : ℝ => ∑ i ∈ s, x^2 / d i)) 4

private def loss (x : ℝ) : ℝ := (x + 1)^2 + 3*x + 7
private noncomputable def vectorLoss (x : Fin 2 → ℝ) : ℝ := Morew.Fn.norm2 (x - ![1,2])^2
private opaque hiddenLoss (x : ℝ) : ℝ := x^2
private def nestedLoss (x : ℝ) : ℝ := loss x

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun x : ℝ => loss x))
  assertQuadratic (← `(fun x : Fin 2 → ℝ => vectorLoss x))
  assertQuadratic (← `(fun x : ℝ => let y := x + 1; y^2 + 2*y + 3))
  assertRejected (← `(fun x : ℝ => hiddenLoss x))

set_option morew.quadConic.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => loss x))
  assertQuadratic (← `(fun x : ℝ => (x + 1)^2))

set_option morew.quadConic.maxExpansionDepth 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => nestedLoss x))

set_option morew.quadConic.maxExpansionSteps 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => loss x + loss (x + 1)))

set_option morew.quadConic.maxExpansionNodes 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => loss x))

/-! Source instances are checked independently of their mathematical operands. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertQuadratic (← `(fun [AddCommGroup ℝ] [Module ℝ ℝ] => fun x : ℝ => x^2 + 1)) 2
  assertRejected (← `(fun x : ℝ =>
    @HPow.hPow ℝ ℕ ℝ ⟨fun _ _ => 0⟩ x 2))
  assertRejected (← `(fun x : ℝ =>
    @HMul.hMul ℝ ℝ ℝ ⟨fun _ _ => 0⟩ 2 (x^2)))
  assertRejected (← `(fun x : EuclideanSpace ℝ (Fin 2) =>
    (@Norm.norm _ ⟨fun _ => 0⟩ x)^2))

/-! Unresolved inputs never assign caller metavariables. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let hole ← mkFreshExprMVar real
  let source ← withLocalDeclD `x real fun x => mkLambdaFVars #[x] hole
  let before ← getMCtx
  let .error _ ← reifyQuadratic source .minimize
    | throwError "quadratic recognizer accepted an unresolved objective"
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter && before.depth == after.depth do
    throwError "quadratic recognizer leaked metavariable state"
  if ← hole.mvarId!.isAssigned then throwError "quadratic recognizer assigned an input metavariable"

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun c : ℝ => fun x : ℝ => c * x^2)) 1
  assertRejected (← `(fun c : ℝ => fun (_ : c < 0) => fun x : ℝ => c*x^2)) 2
  assertRejected (← `(fun x : ℝ => x^2)) 0 .maximize
  assertRejected (← `(fun c : ℝ => fun x : ℝ => (x/c)^2)) 1
  assertRejected (← `(fun x : ℝ => x^2 / 0))
  assertRejected (← `(fun x : ℝ => x^2 / x))
  assertRejected (← `(fun x : ℝ × ℝ => x.1 * x.2))
  assertRejected (← `(fun x : ℝ => x^3))
  assertRejected (← `(fun x : ℝ => Real.exp x))
  assertRejected (← `(fun x : Fin 2 → ℝ => ‖x‖^2))
  assertRejected (← `(fun x : ℝ => x ^ (2 : ℝ)))

end MorewTest.QuadConic.Objective
