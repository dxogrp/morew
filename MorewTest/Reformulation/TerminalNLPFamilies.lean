/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Terminal NLP finite families and composition

Symbolic families remain grouped in the displayed target while concrete form
rows flatten their supported coordinates. Norm guards survive empty dimensions,
and finite extrema retain exactly their source support and parameter evidence.
-/

namespace MorewTest.Reformulation.TerminalNLPFamilies

open Morew
open scoped ENNReal
noncomputable section

section Nested
variable (m n : Nat)

def source :=
  problem (v : Fin m → Fin n → ℝ)
    minimize ∑ i, ∑ j, (v i j) ^ 2
    subject to
      nested : ∀ i : Fin m, ∀ j : Fin n, v i j ≥ 0 ∧ v i j ≤ 2

reformulation target : (source m n) := by
  nlp
example : GlobalEquivalence (source m n) (target m n) := target.equivalence m n
example : (target.nlpForm m n).data.rowCount = m * (n * 2) := by
  change (∑ _ : Fin m, ∑ _ : Fin n, (1 + 1 : ℕ)) + 0 = m * (n * 2)
  simp
example : (target.nlpForm 0 n).data.rowCount = 0 := by
  change (∑ _ : Fin 0, ∑ _ : Fin n, (1 + 1 : ℕ)) + 0 = 0
  simp
example : (target.nlpForm m 0).data.rowCount = 0 := by
  change (∑ _ : Fin m, ∑ _ : Fin 0, (1 + 1 : ℕ)) + 0 = 0
  simp

/--
info: problem (v : Fin m → Fin n → ℝ)
  minimize ∑ i, ∑ j, v i j ^ 2
  subject to
    nested : ∀ (i : Fin m) (j : Fin n), v i j ≥ 0 ∧ v i j ≤ 2
-/
#guard_msgs in
#printp target
end Nested

section Norms
variable (n : Nat)

def normSource :=
  problem (v : Fin n → ℝ) (t : ℝ)
    minimize t ^ 3
    subject to
      infinity : ‖v‖ ≤ t
      explicitInfinity : ‖WithLp.toLp ∞ v‖ ≤ t
      euclidean : ‖WithLp.toLp 2 (fun i => (v i) ^ 2 - 1)‖ ≤ t

reformulation normTarget : (normSource n) := by
  nlp
example : GlobalEquivalence (normSource n) (normTarget n) := normTarget.equivalence n
example : IsSmoothNLP (normTarget n) := normTarget.isSmoothNLP n
example (t : ℝ) : (normTarget 0).feasible (Fin.elim0, t) ↔ 0 ≤ t := by
  simp [normTarget, sq_nonneg]
example : ¬ (normTarget 0).feasible (Fin.elim0, -1) := by
  simp [normTarget, sq_nonneg]

def nativeSource :=
  problem (v : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    minimize t ^ 2
    subject to bound : ‖v‖ ≤ t

reformulation nativeTarget : (nativeSource n) := by
  nlp
example : (nativeTarget.nlpForm n).data.rowCount = 2 := rfl
example : NLP.Form (nativeTarget n) := nativeTarget.nlpForm n
example (t : ℝ) : (nativeTarget 0).feasible (0, t) ↔ 0 ≤ t := by
  simp [nativeTarget, sq_nonneg]
end Norms

section Extrema
variable {ι : Type} (s : Finset ι) (hs : s.Nonempty) (a : ι → ℝ)
variable (ha : ∀ i ∈ s, 0 < a i)

def extremaSource :=
  problem (x t : ℝ)
    minimize x ^ 4
    subject to
      largest : s.sup' hs (fun i => Real.log (a i) * x ^ 2) ≤ t
      smallest : -t ≤ s.inf' hs (fun i => a i * Real.sin x)

reformulation extremaTarget : (extremaSource s hs a) := by
  nlp
example : GlobalEquivalence (extremaSource s hs a) (extremaTarget s a) :=
  extremaTarget.equivalence s hs a
example : NLP.Form (extremaTarget s a) := extremaTarget.nlpForm s hs a ha
example : (extremaTarget.nlpForm s hs a ha).data.rowCount = s.card + s.card := by
  change (∑ _ : Fin s.card, (1 : ℕ)) + ((∑ _ : Fin s.card, (1 : ℕ)) + 0) =
    s.card + s.card
  simp
end Extrema

namespace Substitution

def source := problem (x : ℝ) minimize Real.exp x + x ^ 2

def shift : FeasibleSurjection source (fun y : ℝ => y + 1) where
  preimage x := x.1 - 1
  rightInverse x := by simp

reformulation target : source := by
  substitute x := y + 1 using shift
  nlp
example : GlobalEquivalence source target := target.equivalence
example (y : ℝ) : target.objective y = Real.exp (y + 1) + (y + 1) ^ 2 := rfl
example : target.nlpForm.data.rowCount = 0 := rfl

end Substitution
end
end MorewTest.Reformulation.TerminalNLPFamilies
