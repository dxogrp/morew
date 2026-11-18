/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import Morew.Rewrite.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Exact representations of finite sums

Summands share an input and may have different auxiliary types. The semantic
construction also retains subtype domains and the bounds on empty sums.
-/

assert_not_exists Morew.Conic.Cone Morew.Syntax.ProblemView

namespace MorewTest.Rewrite.Sum

open Morew

noncomputable section

section Abstract

variable {I X : Type*} [Fintype I] (f : I → X → ℝ)

def sumRepresentation (repr : ∀ i, EpigraphRepr (f i)) :
    EpigraphRepr (fun x => ∑ i, f i x) :=
  EpigraphRepr.sum repr

example (repr : ∀ i, EpigraphRepr (f i)) :
    (EpigraphRepr.sum repr).Auxiliary =
      ((I → ℝ) × (∀ i, (repr i).Auxiliary)) := rfl

example (repr : ∀ i, EpigraphRepr (f i)) (x : X) (t : ℝ)
    (s : I → ℝ) (a : ∀ i, (repr i).Auxiliary) :
    (EpigraphRepr.sum repr).target x t (s, a) ↔
      (∀ i, (repr i).target x (s i) (a i)) ∧ (∑ i, s i) ≤ t := Iff.rfl

example (repr : ∀ i, EpigraphRepr (f i)) (x : X) (t : ℝ) :
    (∑ i, f i x) ≤ t ↔ ∃ a, (EpigraphRepr.sum repr).target x t a :=
  (EpigraphRepr.sum repr).source_iff_exists x t

example (repr : ∀ i, HypographRepr (f i)) :
    (HypographRepr.sum repr).Auxiliary =
      ((I → ℝ) × (∀ i, (repr i).Auxiliary)) := rfl

example (repr : ∀ i, HypographRepr (f i)) (x : X) (t : ℝ)
    (s : I → ℝ) (a : ∀ i, (repr i).Auxiliary) :
    (HypographRepr.sum repr).target x t (s, a) ↔
      (∀ i, (repr i).target x (s i) (a i)) ∧ t ≤ ∑ i, s i := Iff.rfl

example (repr : ∀ i, HypographRepr (f i)) (x : X) (t : ℝ) :
    t ≤ (∑ i, f i x) ↔ ∃ a, (HypographRepr.sum repr).target x t a :=
  (HypographRepr.sum repr).source_iff_exists x t

end Abstract

/-! A linear and a quadratic summand share `x`; only the latter uses a witness. -/

def mixedFunction : Bool → ℝ → ℝ
  | false, x => x
  | true, x => x ^ 2

def mixedEpigraph : ∀ i, EpigraphRepr (mixedFunction i)
  | false => {
      Auxiliary := Unit
      target x t _ := x ≤ t
      source_iff_exists _ _ := by simp only [mixedFunction, exists_const] }
  | true => {
      Auxiliary := ℝ
      target x t a := a = x ^ 2 ∧ a ≤ t
      source_iff_exists x t := by
        constructor
        · intro h
          exact ⟨x ^ 2, rfl, h⟩
        · rintro ⟨a, rfl, h⟩
          exact h }

def mixedHypograph : ∀ i, HypographRepr (mixedFunction i)
  | false => {
      Auxiliary := Unit
      target x t _ := t ≤ x
      source_iff_exists _ _ := by simp only [mixedFunction, exists_const] }
  | true => {
      Auxiliary := ℝ
      target x t a := a = x ^ 2 ∧ t ≤ a
      source_iff_exists x t := by
        constructor
        · intro h
          exact ⟨x ^ 2, rfl, h⟩
        · rintro ⟨a, rfl, h⟩
          exact h }

def mixedEpigraphWitness (x : ℝ) : ∀ i, (mixedEpigraph i).Auxiliary
  | false => ()
  | true => x ^ 2

def mixedHypographWitness (x : ℝ) : ∀ i, (mixedHypograph i).Auxiliary
  | false => ()
  | true => x ^ 2

example (x : ℝ) :
    (EpigraphRepr.sum mixedEpigraph).target x (x ^ 2 + x)
      (fun i => mixedFunction i x, mixedEpigraphWitness x) := by
  constructor
  · intro i
    cases i <;> simp [mixedEpigraph, mixedFunction, mixedEpigraphWitness]
  · simp [mixedFunction]

example (x : ℝ) :
    (HypographRepr.sum mixedHypograph).target x (x ^ 2 + x)
      (fun i => mixedFunction i x, mixedHypographWitness x) := by
  constructor
  · intro i
    cases i <;> simp [mixedHypograph, mixedFunction, mixedHypographWitness]
  · simp [mixedFunction]

example (x t : ℝ) :
    x ^ 2 + x ≤ t ↔ ∃ a, (EpigraphRepr.sum mixedEpigraph).target x t a := by
  simpa [Fintype.sum_bool, mixedFunction] using
    (EpigraphRepr.sum mixedEpigraph).source_iff_exists x t

example (x t : ℝ) :
    t ≤ x ^ 2 + x ↔ ∃ a, (HypographRepr.sum mixedHypograph).target x t a := by
  simpa [Fintype.sum_bool, mixedFunction] using
    (HypographRepr.sum mixedHypograph).source_iff_exists x t

/-! Compact constructors use the supplied positive-input domain. -/

def quotientSumEpigraph {I : Type*} [Fintype I] (c : I → ℝ) :
    EpigraphRepr (fun x : {x : ℝ // 0 < x} => ∑ i, c i / x.1) :=
  EpigraphRepr.sumOfIff (f := fun i (x : {x : ℝ // 0 < x}) => c i / x.1)
    (fun i x t => c i ≤ t * x.1) (fun _ x _ => div_le_iff₀ x.2)

def quotientSumHypograph {I : Type*} [Fintype I] (c : I → ℝ) :
    HypographRepr (fun x : {x : ℝ // 0 < x} => ∑ i, c i / x.1) :=
  HypographRepr.sumOfIff (f := fun i (x : {x : ℝ // 0 < x}) => c i / x.1)
    (fun i x t => t * x.1 ≤ c i) (fun _ x _ => le_div_iff₀ x.2)

example {I : Type*} [Fintype I] (c : I → ℝ) :
    (quotientSumEpigraph c).Auxiliary = (I → ℝ) := rfl

example {I : Type*} [Fintype I] (c : I → ℝ) :
    (quotientSumHypograph c).Auxiliary = (I → ℝ) := rfl

example {I : Type*} [Fintype I] (c : I → ℝ) (x : {x : ℝ // 0 < x}) (t : ℝ) :
    (∑ i, c i / x.1) ≤ t ↔
      ∃ s : I → ℝ, (∀ i, c i ≤ s i * x.1) ∧ (∑ i, s i) ≤ t :=
  (quotientSumEpigraph c).source_iff_exists x t

example {I : Type*} [Fintype I] (c : I → ℝ) (x : {x : ℝ // 0 < x}) (t : ℝ) :
    t ≤ (∑ i, c i / x.1) ↔
      ∃ s : I → ℝ, (∀ i, s i * x.1 ≤ c i) ∧ t ≤ ∑ i, s i :=
  (quotientSumHypograph c).source_iff_exists x t

section Empty

variable {X : Type*} (f : Fin 0 → X → ℝ) (x : X)

example (repr : ∀ i, EpigraphRepr (f i)) (t : ℝ) :
    (∃ a, (EpigraphRepr.sum repr).target x t a) ↔ 0 ≤ t := by
  simpa using ((EpigraphRepr.sum repr).source_iff_exists x t).symm

example (repr : ∀ i, HypographRepr (f i)) (t : ℝ) :
    (∃ a, (HypographRepr.sum repr).target x t a) ↔ t ≤ 0 := by
  simpa using ((HypographRepr.sum repr).source_iff_exists x t).symm

example (repr : ∀ i, EpigraphRepr (f i)) :
    ∃ a, (EpigraphRepr.sum repr).target x 0 a := by
  rw [← (EpigraphRepr.sum repr).source_iff_exists]
  simp

example (repr : ∀ i, HypographRepr (f i)) :
    ∃ a, (HypographRepr.sum repr).target x 0 a := by
  rw [← (HypographRepr.sum repr).source_iff_exists]
  simp

example (repr : ∀ i, EpigraphRepr (f i)) :
    ¬ ∃ a, (EpigraphRepr.sum repr).target x (-1) a := by
  rw [← (EpigraphRepr.sum repr).source_iff_exists]
  norm_num

example (repr : ∀ i, HypographRepr (f i)) :
    ¬ ∃ a, (HypographRepr.sum repr).target x 1 a := by
  rw [← (HypographRepr.sum repr).source_iff_exists]
  norm_num

end Empty

end
end MorewTest.Rewrite.Sum
