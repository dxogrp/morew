/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.DomainSupport
import Morew.NLP.Basic

/-!
# Inferred domains and complete manual nonlinear-program forms

The original functions and feasibility predicates are checked by the kernel.
These tests exercise positive evidence, finite support, and opaque helper
arguments, followed by minimizing and maximizing forms with unchanged rows.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.NLP.Domain

open Lean Lean.Meta Lean.Elab.Term
open Morew Morew.NLP

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(((fun _x : ℝ => True), (#[] : Array (ℝ → ℝ)))))
  -- The API certifies exactly the supplied functions; rows are evidence only.
  assertDomain (← `(((fun x : ℝ => 1 ≤ |x|), #[fun x : ℝ => x])))
  assertDomain (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => Real.log x])))
  assertDomain (← `(((fun x : ℝ => x ≥ 1), #[fun x : ℝ => Real.log x])))
  assertDomain (← `(((fun _x : ℝ => True), #[fun x : ℝ => Real.log (Real.exp x)])))
  assertDomain (← `(((fun x : ℝ => 1 ≤ x),
    #[fun x : ℝ => Real.log (Real.log (Real.exp x))])))
  assertDomain (← `(((fun x : ℝ => 1 ≤ x ∧ 1 ≤ Real.log x),
    #[fun x : ℝ => Real.log (Real.log x), fun x : ℝ => Real.log x])))
  assertDomain (← `(((fun _x : ℝ => True), #[fun x : ℝ => Real.sqrt (x ^ 2 + 1)])))
  assertDomain (← `(((fun x : ℝ => x = 2), #[fun x : ℝ => Real.sqrt x])))
  assertDomain (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => x⁻¹])))
  assertDomain (← `(((fun x : ℝ => x ≤ -1), #[fun x : ℝ => x⁻¹])))
  assertDomain (← `(((fun _x : ℝ => True), #[fun x : ℝ => x / (x ^ 2 + 1)])))
  assertDomain (← `(((fun _x : ℝ => True), #[fun x : ℝ => x / (-2 : ℝ)])))
  assertDomain (← `(fun r : ℝ => ((fun x : ℝ => 1 ≤ x),
    #[fun x : ℝ => x ^ r, fun x : ℝ => Real.rpow x r]))) 1
  assertDomain (← `(fun c : ℝ => fun _hc : 0 < c => ((fun x : ℝ => 1 ≤ x),
    #[fun x : ℝ => x ^ Real.log c]))) 2

/-! Multiple supplied functions share one open domain in their original order. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(((fun x : ℝ => 1 ≤ x ∧ x ≤ 3),
    #[fun x : ℝ => Real.log x, fun x : ℝ => Real.sqrt (4 - x),
      fun x : ℝ => 1 / x, fun x : ℝ => x ^ (3 : ℝ)])))
  assertDomain (← `(((fun p : ℝ × ℝ => p.2 ≤ p.1 ∧ 1 ≤ p.2),
    #[fun p : ℝ × ℝ => Real.log p.1 + Real.sqrt p.2])))
  assertDomain (← `(((fun x : ℝ => x ≤ 0 ∧ 1 ≤ x),
    #[fun x : ℝ => Real.log x, fun _x : ℝ => Real.log 0])))
  assertDomain (← `(fun c : ℝ => fun hc : 0 < c =>
    ((fun _x : ℝ => True), #[fun x : ℝ => Real.log c + x]))) 2
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun _x : ℝ => Real.log 1 + Real.sqrt 1 + (2 : ℝ)⁻¹])))
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => x + (2 : ℝ) ^ (-1 : ℤ)])))

/-! Local structural reductions preserve domain requirements and binder identity. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(((fun x : ℝ => let y := x; 1 ≤ y),
    #[fun x : ℝ => let y := x + 1; Real.log y])))
  assertDomain (← `(((fun x : ℝ => 1 ≤ x),
    #[fun x : ℝ => (fun y : ℝ => Real.log y) x])))
  assertDomain (← `(((fun x : ℝ => 1 ≤ x),
    #[fun x : ℝ => let log := fun y : ℝ => Real.log y; log x])))
  assertDomain (← `(fun x : ℝ => fun _hx : 0 < x =>
    ((fun _y : ℝ => True), #[fun x : ℝ => x + Real.log 1]))) 2
  assertDomain (← `(fun p : ℝ × Nat =>
    ((fun _x : ℝ => True), #[fun x : ℝ => x + p.1]))) 1
  assertDomain (← `(fun p : Nat × ℝ =>
    ((fun _x : ℝ => True), #[fun x : ℝ => x + p.2]))) 1
  assertDomain (← `(fun n : Nat => fun i : Fin n => fun p : (Fin n → ℝ) × Nat =>
    ((fun _x : ℝ => True), #[fun x : ℝ => x + p.1 i]))) 3
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => x + ((1 : ℝ), Real.log 0).1])))
  assertDomain (← `(fun c : { r : ℝ // 0 < r } => ((fun _x : ℝ => True),
    #[fun x : ℝ => x + (let _hc : 0 < c.val := c.property;
      (Real.log c.val, (0 : Nat))).1]))) 1

/-! Finite support controls obligations even when the ambient index type is infinite. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(fun s : Finset Nat => fun a : Nat → ℝ =>
    fun _ha : ∀ i ∈ s, 0 < a i => ((fun _x : ℝ => True),
      #[fun x : ℝ => ∑ i ∈ s, (Real.log (a i) + x ^ i)]))) 3

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ∑ _i ∈ (∅ : Finset Nat), Real.log x])))

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(fun n : Nat => ((fun _x : Fin n → ℝ => True),
    #[fun x : Fin n → ℝ => ∑ i, Real.log (Real.exp (x i))]))) 1

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(((fun _x : Fin 0 → ℝ => True),
    #[fun x : Fin 0 → ℝ => ∑ i, Real.log (Real.exp (x i))])))

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(fun n : Nat => fun i : Fin n =>
    ((fun x : Fin n → ℝ => 1 ≤ x i), #[fun x : Fin n → ℝ => Real.log (x i)]))) 2

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(fun n : Nat => fun i : Fin n =>
    ((fun _x : ℝ => True),
      #[fun x : ℝ => (fun _j : Fin n => Real.log (Real.exp x)) i]))) 2

private noncomputable def scalarHelper (_value : ℝ) : ℝ := 7
private noncomputable def pairHelper (_value : ℝ × ℝ) : ℝ := 7
private noncomputable def vectorHelper {n : Nat} (_value : Fin n → ℝ) : ℝ := 7
private noncomputable def functionHelper (_value : ℝ → ℝ) : ℝ := 7
private noncomputable def setHelper (_value : Set ℝ) : ℝ := 7

/-! Constant helper bodies stay opaque, while supported value arguments retain obligations. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(fun c : ℝ => fun _hc : 0 < c => ((fun _x : ℝ => True),
    #[fun x : ℝ => scalarHelper (Real.log c) + x]))) 2
  assertDomain (← `(fun c : ℝ => fun _hc : 0 < c => ((fun _x : ℝ => True),
    #[fun x : ℝ => pairHelper (Real.log c, Real.sqrt c) + x]))) 2
  assertDomain (← `(fun n : Nat => fun c : ℝ => fun _hc : 0 < c =>
    ((fun _x : ℝ => True), #[fun x : ℝ => vectorHelper (fun _i : Fin n => Real.log c) + x]))) 3
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => vectorHelper (fun _i : Fin 0 => Real.log 0) + x])))
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => functionHelper (fun z : ℝ => Real.log z) + x])))
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => setHelper (Set.Ici (Real.log 0)) + x])))

/-- Test-only packaging of the API's two-source result. -/
structure PairCertificate (feasible : ℝ → Prop) (objective residual : ℝ → ℝ) where
  domain : Set ℝ
  domain_isOpen : IsOpen domain
  objective_smooth : ContDiffOn ℝ 2 objective domain
  residual_smooth : ContDiffOn ℝ 2 residual domain
  feasible_mem_domain : ∀ x, feasible x → x ∈ domain

elab "test_domain_pair" : term <= expected => do
  let expected ← instantiateMVars expected
  unless expected.isAppOfArity ``PairCertificate 3 do
    throwError "expected a two-source domain certificate"
  let args := expected.getAppArgs
  let result ← checkSuccess args[0]! #[args[1]!, args[2]!]
  mkAppM ``PairCertificate.mk #[result.domain, result.domainIsOpen,
    result.smooth[0]!, result.smooth[1]!, result.feasibleMemDomain]

private noncomputable def generatedCertificate :
    PairCertificate (fun x => 1 ≤ x) Real.log (fun x => x) := test_domain_pair

noncomputable def generatedData : Data ℝ where
  sense := .minimize
  domain := generatedCertificate.domain
  domain_isOpen := generatedCertificate.domain_isOpen
  objective := Real.log
  objective_smooth := generatedCertificate.objective_smooth
  rowCount := 1
  rows := fun _ => {
    residual := fun x => x
    bounds := Bounds.lowerBound 1
    smooth := generatedCertificate.residual_smooth
  }
  feasible_mem_domain x h :=
    generatedCertificate.feasible_mem_domain x ((Bounds.contains_lowerBound 1 x).mp (h 0))

noncomputable def generatedProblem : Problem ℝ ℝ where
  objective := Real.log
  feasible x := 1 ≤ x

noncomputable def generatedForm : Form generatedProblem where
  data := generatedData
  represents := by
    apply congrArg (Problem.mk Real.log)
    funext x
    apply propext
    simp [generatedData, Row.Holds]

example : IsSmoothNLP generatedProblem := generatedForm.isSmoothNLP
example (x : ℝ) : generatedForm.data.toProblem.feasible x ↔ 1 ≤ x := by
  simp [Data.toProblem, generatedForm, generatedData, Row.Holds]
example : generatedForm.data.rowCount = 1 := rfl
example : generatedForm.data.toProblem.objective (-1) = Real.log (-1) := rfl

noncomputable def generatedMaximumData : Data ℝ :=
  { generatedData with sense := .maximize }

noncomputable def generatedMaximum : Problem ℝ (OrderDual ℝ) := generatedProblem

noncomputable def generatedMaximumForm : Form generatedMaximum where
  data := generatedMaximumData
  represents := generatedForm.represents

example : generatedMaximumForm.data.sense = .maximize := rfl
example : IsSmoothNLP generatedMaximum := generatedMaximumForm.isSmoothNLP
example (x : ℝ) : generatedMaximum.objective x = Real.log x := rfl

end MorewTest.NLP.Domain
