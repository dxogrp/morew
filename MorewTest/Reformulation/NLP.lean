/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Exact targeted smooth rewrites and their ordered presentations -/

namespace MorewTest.Reformulation.NLP

open Morew
open scoped ENNReal

noncomputable section

def scalarSource :=
  problem (x y t : ℝ)
    minimize |x|
    subject to
      before : x < 20
      absolute : |x * y - 1| ≤ t
      positive : (x ^ 3)⁺ ≤ t
      maximum : max (Real.sin x) (y ^ 2) ≤ t
      minimum : -t ≤ min (x * y) (Real.exp y)
      after : |y| ≤ 10 ∧ x ≤ 30

reformulation scalarTarget : scalarSource := by
  nlp at absolute
  nlp at positive
  nlp at maximum
  nlp at minimum

example : GlobalEquivalence scalarSource scalarTarget := scalarTarget.equivalence

example (x y t : ℝ) : scalarTarget.objective ((x, y), t) = |x| := rfl

example (x y t : ℝ) : scalarTarget.feasible ((x, y), t) ↔
    x < 20 ∧ x * y - 1 ≤ t ∧ -(x * y - 1) ≤ t ∧
      x ^ 3 ≤ t ∧ 0 ≤ t ∧ Real.sin x ≤ t ∧ y ^ 2 ≤ t ∧
      -t ≤ x * y ∧ -t ≤ Real.exp y ∧ (|y| ≤ 10 ∧ x ≤ 30) := Iff.rfl

/--
info: problem (x y t : ℝ)
  minimize |x|
  subject to
    before : x < 20
    absolute_nlp_1 : x * y - 1 ≤ t
    absolute_nlp_2 : -(x * y - 1) ≤ t
    positive_nlp_1 : x ^ 3 ≤ t
    positive_nlp_2 : 0 ≤ t
    maximum_nlp_1 : Real.sin x ≤ t
    maximum_nlp_2 : y ^ 2 ≤ t
    minimum_nlp_1 : -t ≤ x * y
    minimum_nlp_2 : -t ≤ Real.exp y
    after : |y| ≤ 10 ∧ x ≤ 30
-/
#guard_msgs in
#printp scalarTarget

def maximizing :=
  problem (x t : ℝ)
    maximize x ^ 3
    subject to
      upper : t ≥ |x ^ 2 - 1|
      lower : min (Real.sin x) (x ^ 3) ≥ -t

reformulation maximizingTarget : maximizing := by
  nlp at upper
  nlp at lower

example : GlobalEquivalence maximizing maximizingTarget := maximizingTarget.equivalence
example : Problem (ℝ × ℝ) (OrderDual ℝ) := maximizingTarget
example (x t : ℝ) : maximizingTarget.objective (x, t) = x ^ 3 := rfl

def absoluteObjective := problem (x : ℝ) minimize |x|

reformulation defaultObjective : absoluteObjective := by
  epigraph t
  nlp at epigraph_t

reformulation namedObjective : absoluteObjective := by
  epigraph t as objective_bound
  nlp at objective_bound using Rewrite.absEpigraph

example : GlobalEquivalence absoluteObjective defaultObjective := defaultObjective.equivalence
example : GlobalEquivalence absoluteObjective namedObjective := namedObjective.equivalence

def components :=
  problem (x y : ℝ)
    let first := x ^ 2
    let second := x ^ 2
    minimize first + second
    subject to
      budget : |x| + y ^ 2 ≤ 10
      untouched : first ≤ second + 1

reformulation componentTarget : components := by
  epigraph a at (|x|) in budget as abs_bound
  nlp at abs_bound

example : GlobalEquivalence components componentTarget := componentTarget.equivalence

/--
info: problem (x y a : ℝ)
  let first := x ^ 2
  let second := x ^ 2
  minimize first + second
  subject to
    budget : a + y ^ 2 ≤ 10
    untouched : first ≤ second + 1
    abs_bound_nlp_1 : x ≤ a
    abs_bound_nlp_2 : -x ≤ a
-/
#guard_msgs in
#printp componentTarget

section Vectors

variable (n : ℕ)

def vectorSource :=
  problem (v : Fin n → ℝ) (t : ℝ)
    minimize t ^ 3
    subject to
      infinity : ‖v‖ ≤ t
      explicitInfinity : ‖WithLp.toLp ∞ v‖ ≤ t
      euclidean : ‖WithLp.toLp 2 (fun i => (v i) ^ 2 - 1)‖ ≤ t

reformulation vectorTarget : (vectorSource n) := by
  nlp at infinity
  nlp at explicitInfinity
  nlp at euclidean

example : GlobalEquivalence (vectorSource n) (vectorTarget n) := vectorTarget.equivalence n

def oneNormSource :=
  problem (v : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      norm : ‖WithLp.toLp 1 (fun i => (v i) ^ 2)‖ ≤ t

reformulation oneNormTarget : (oneNormSource n) := by
  nlp at norm

example : GlobalEquivalence (oneNormSource n) (oneNormTarget n) := oneNormTarget.equivalence n

end Vectors

example (t : ℝ) : (oneNormTarget 0).feasible ((Fin.elim0, t), Fin.elim0) ↔ 0 ≤ t := by
  simp [oneNormTarget]

example : ¬ (vectorTarget 0).feasible (Fin.elim0, -1) := by
  simp [vectorTarget]

section FiniteExtrema

variable {ι : Type} (s : Finset ι) (hs : s.Nonempty) (a : ι → ℝ)

def finiteSource :=
  problem (x t : ℝ)
    minimize x ^ 4
    subject to
      largest : s.sup' hs (fun i => a i * x ^ 2) ≤ t
      smallest : -t ≤ s.inf' hs (fun i => a i * Real.sin x)

reformulation finiteTarget : (finiteSource s hs a) := by
  nlp at largest
  nlp at smallest

example : GlobalEquivalence (finiteSource s hs a) (finiteTarget s a) :=
  finiteTarget.equivalence s hs a

end FiniteExtrema

namespace Names

def budget : ℕ := 17

def source :=
  problem (budget_aux : ℝ) (v : Fin 1 → ℝ)
    let budget_aux_1 := budget_aux + 1
    let cap_nlp_1 := budget_aux ^ 2
    minimize cap_nlp_1
    subject to
      budget_nlp_1 : budget_aux ≤ 10
      budget : ‖WithLp.toLp 1 v‖ ≤ 3
      labels.cap : |budget_aux| ≤ 5
      «cap value» : budget_aux⁺ ≤ 2

reformulation target : source := by
  nlp at budget
  nlp at labels.cap
  nlp at «cap value»

example : GlobalEquivalence source target := target.equivalence

/--
info: problem (budget_aux : ℝ) (v budget_aux_2 : Fin 1 → ℝ)
  let budget_aux_1 := budget_aux + 1
  let cap_nlp_1 := budget_aux ^ 2
  minimize cap_nlp_1
  subject to
    budget_nlp_1 : budget_aux ≤ 10
    budget_nlp_1_1 : v ≤ budget_aux_2
    budget_nlp_2 : -v ≤ budget_aux_2
    budget_nlp_3 : ∑ i, budget_aux_2 i ≤ 3
    cap_nlp_1 : budget_aux ≤ 5
    cap_nlp_2 : -budget_aux ≤ 5
    «cap value_nlp_1» : budget_aux ≤ 2
    «cap value_nlp_2» : 0 ≤ 2
-/
#guard_msgs in
#printp target

def macroSource := problem (x : ℝ) minimize x subject to cap : |x| ≤ 1

macro "nlpMacro " target:ident : command =>
  `(reformulation $target : macroSource := by nlp at cap)

nlpMacro macroTarget

example : GlobalEquivalence macroSource macroTarget := macroTarget.equivalence

end Names

namespace HelperPresentation

def coefficient (c : ℝ) : ℝ := c ^ 2 + 1

def source (c : ℝ) :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : |x ^ 2| ≤ coefficient c

variable (c : ℝ)

reformulation target : (source c) := by
  nlp at bound

/--
info: problem (x : ℝ)
  minimize x
  subject to
    bound_nlp_1 : x ^ 2 ≤ coefficient c
    bound_nlp_2 : -x ^ 2 ≤ coefficient c
-/
#guard_msgs in
#printp target

end HelperPresentation

namespace Composition

def source :=
  problem (x : ℝ)
    minimize |x|
    subject to
      square : x ^ 2 ≤ 9
      magnitude : |x| ≤ 2

reformulation mixed : source := by
  conic at square
  nlp at magnitude

def shiftCoverage : FeasibleSurjection mixed (fun y : ℝ => y + 1) where
  preimage x := x.1 - 1
  rightInverse x := by simp

reformulation continued : mixed := by
  substitute x := y + 1 using shiftCoverage
  epigraph t
  nlp at epigraph_t

example : GlobalEquivalence source mixed := mixed.equivalence
example : GlobalEquivalence mixed continued := continued.equivalence

def affineSource := problem (x : ℝ) minimize x subject to cap : |x| ≤ 2

reformulation conicTarget : affineSource := by
  nlp at cap
  conic

example : IsConic conicTarget := conicTarget.isConic

end Composition

end
end MorewTest.Reformulation.NLP
