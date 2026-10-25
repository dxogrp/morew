/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.SmoothSupport
import Morew.NLP

/-!
# Globally smooth expressions and manual NLP forms

The certifier recognizes a fixed collection of real operations, preserves the
source function, and does not install the problem or reformulation language.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.NLP.Smooth

open Lean Lean.Meta Lean.Elab.Term
open Morew Morew.NLP

universe u

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => x))
  assertSmooth (← `(fun _x : ℝ => (3 : ℝ)))
  assertSmooth (← `(fun x : ℝ => x ^ 4 - x ^ 2))
  assertSmooth (← `(fun x : ℝ => -(x + 2) * (x - 3)))
  assertSmooth (← `(fun n : ℕ => fun x : ℝ => x ^ n)) 1
  assertSmooth (← `(fun x : ℝ => Real.exp (x * x)))
  assertSmooth (← `(fun x : ℝ => Real.sin x + Real.cos (2 * x)))
  assertSmooth (← `(fun x : ℝ => Real.sinh x - Real.cosh x))
  assertSmooth (← `(fun x : ℝ => Real.tanh (Real.exp x)))
  assertSmooth (← `(Real.exp ∘ (fun x : ℝ => x * x)))

/-! Decision-independent terms may be arbitrary total real expressions. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => c * x + c)) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => Real.log c + x)) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => |c| * x)) 1
  assertSmooth (← `(fun f : ℝ → ℝ => fun c : ℝ => fun x : ℝ => f c + x)) 2
  assertSmooth (← `(fun _x : ℝ => Real.log 0))

/-! Product projections, symbolic coordinates, and finite sums. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ × ℝ => x.1 * x.2 + x.2 ^ 2))
  assertSmooth (← `(fun x : (ℝ × ℝ) × ℝ => x.1.1 + x.1.2 * x.2))
  assertSmooth (← `(fun x : Fin 3 → ℝ => x 0 * x 1 + x 2 ^ 2))
  assertSmooth (← `(fun n : ℕ => fun i : Fin n => fun x : Fin n → ℝ => x i)) 2
  assertSmooth (← `(fun n : ℕ => fun x : Fin n → ℝ => ∑ i, x i ^ 2)) 1
  assertSmooth (← `(fun (n : ℕ) [Fintype (Fin n)] =>
    fun x : Fin n → ℝ => ∑ i, x i ^ 2)) 2
  assertSmooth (← `(fun x : Fin 0 → ℝ => ∑ i, x i ^ 2))
  assertSmooth (← `(fun _x : Fin 0 → ℝ => (0 : ℝ)))
  assertSmooth (← `(fun n : ℕ => fun x : ℝ × (Fin n → ℝ) =>
    x.1 * x.1 + ∑ i, Real.exp (x.2 i))) 1
  assertSmooth (← `(fun s : Finset ℕ => fun a : ℕ → ℝ => fun x : ℝ =>
    ∑ i ∈ s, a i * x ^ i)) 2
  assertSmooth (← `(fun x : ℝ => ∑ _i ∈ (∅ : Finset ℕ), x))

/-! Only local structural reductions are needed for these equivalent spellings. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => let y := x + 1; y * y))
  assertSmooth (← `(fun x : ℝ => (fun y : ℝ => y * y) (x + 1)))
  assertSmooth (← `(fun x : ℝ => let f := fun y : ℝ => y * y; f x))
  assertSmooth (← `(fun c : ℝ => fun hc : 0 < c => fun x : ℝ =>
    let _h : c ≠ 0 := ne_of_gt hc
    c * x * x)) 2
  assertSmooth (← `(fun x : ℝ => let p := (x + 1, x * x); p.1 + p.2))
  assertSmooth (← `(fun p : ℝ × ℝ => match p with | (x, y) => x * y + x))
  assertSmooth (← `(fun p : ℝ × ℝ => (fun q : ℝ × ℝ => q.1 * q.2) (p.2, p.1)))
  assertSmooth (← `(fun n : ℕ => fun x : Fin n → ℝ =>
    ∑ i, (fun j : Fin n => x j * x j) i)) 1

/-! A test-only term elaborator inserts the ordinary proof returned by the API. -/

elab "test_global_smooth" : term <= expected => do
  synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  unless expected.isAppOfArity ``ContDiffOn 11 do
    throwError "expected a ContDiffOn goal"
  checkSuccess expected.getAppArgs[9]!

example (ι : Type u) (s : Finset ι) (a : ι → ℝ) :
    ContDiffOn ℝ 2 (fun x : ℝ => ∑ i ∈ s, a i * x) Set.univ :=
  test_global_smooth

noncomputable def generatedData : Data (ℝ × ℝ) where
  sense := .minimize
  domain := Set.univ
  domain_isOpen := isOpen_univ
  objective := fun x => x.1 ^ 4 - x.2 ^ 2
  objective_smooth := test_global_smooth
  rowCount := 1
  rows := fun _ => {
    residual := fun x => x.1 * x.2
    bounds := Bounds.fixed 1
    smooth := test_global_smooth
  }
  feasible_mem_domain := fun _ _ => Set.mem_univ _

noncomputable def generatedProblem : Problem (ℝ × ℝ) ℝ := generatedData.toProblem

noncomputable def generatedForm : Form generatedProblem where
  data := generatedData
  represents := rfl

example : IsSmoothNLP generatedProblem := generatedForm.isSmoothNLP
example (x : ℝ × ℝ) : generatedProblem.objective x = x.1 ^ 4 - x.2 ^ 2 := rfl

noncomputable def generatedMaximumData : Data (ℝ × ℝ) :=
  { generatedData with sense := .maximize }

noncomputable def generatedMaximum : Problem (ℝ × ℝ) (OrderDual ℝ) :=
  generatedMaximumData.toProblem

noncomputable def generatedMaximumForm : Form generatedMaximum where
  data := generatedMaximumData
  represents := rfl

example : generatedMaximumForm.data.sense = .maximize := rfl
example : IsSmoothNLP generatedMaximum := generatedMaximumForm.isSmoothNLP
example (x : ℝ × ℝ) : generatedMaximum.objective x = x.1 ^ 4 - x.2 ^ 2 := rfl

end MorewTest.NLP.Smooth
