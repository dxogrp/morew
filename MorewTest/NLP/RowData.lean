/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Rows

/-!
# Concrete smooth row data

Row blocks retain exact residuals, bounds, and finite ordering while carrying
proofs of the original predicate. These tests exercise the data independently
of elaboration, including symbolic dependent families and auxiliary rebasing.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.NLP.RowData

open Morew Morew.NLP Morew.NLP.Rows

noncomputable section

def upper : Block (Set.univ : Set ℝ) (fun x => x ^ 2 ≤ x + 3) :=
  Block.le Set.univ (fun x => x ^ 2) (fun x => x + 3)
    ((contDiffOn_id.pow 2).sub (contDiffOn_id.add contDiffOn_const))

def lower : Block (Set.univ : Set ℝ) (fun x => x ≥ 2) :=
  Block.ge Set.univ id (fun _ => 2) (contDiffOn_id.sub contDiffOn_const)

def fixed : Block (Set.univ : Set ℝ) (fun x => x = 1) :=
  Block.eq Set.univ id (fun _ => 1) (contDiffOn_id.sub contDiffOn_const)

example : upper.rowCount = 1 := rfl
example : (upper.rows (0 : Fin 1)).residual = fun x => x ^ 2 - (x + 3) := rfl
example : (upper.rows (0 : Fin 1)).bounds = Bounds.upperBound 0 := rfl
example : (lower.rows (0 : Fin 1)).residual = fun x => x - 2 := rfl
example : (lower.rows (0 : Fin 1)).bounds = Bounds.lowerBound 0 := rfl
example : (fixed.rows (0 : Fin 1)).residual = fun x => x - 1 := rfl
example : (fixed.rows (0 : Fin 1)).bounds = Bounds.fixed 0 := rfl
example (x : ℝ) : (∀ i, (upper.rows i).Holds x) ↔ x ^ 2 ≤ x + 3 := upper.holds_iff x

-- A displayed True contributes no row; adjacent comparisons remain separate.
def grouped := (Block.truth (Set.univ : Set ℝ)).and (upper.and (lower.and fixed))

example : grouped.rowCount = 3 := rfl
example : (grouped.rows (0 : Fin 3)).bounds = Bounds.upperBound 0 := rfl
example : (grouped.rows (1 : Fin 3)).bounds = Bounds.lowerBound 0 := rfl
example : (grouped.rows (2 : Fin 3)).bounds = Bounds.fixed 0 := rfl
example (x : ℝ) : (∀ i, (grouped.rows i).Holds x) ↔
    True ∧ (x ^ 2 ≤ x + 3 ∧ (x ≥ 2 ∧ x = 1)) := grouped.holds_iff x

-- Symbolic and zero dimensions retain coordinate order without enumeration.
def coordinateRows (n : Nat) (limits : Fin n → ℝ) :
    Block (Set.univ : Set (Fin n → ℝ)) (fun x => ∀ i, x i ≤ limits i) :=
  Block.family (fun i (x : Fin n → ℝ) => x i ≤ limits i) fun i =>
    Block.le Set.univ (fun x : Fin n → ℝ => x i) (fun _ => limits i)
      ((contDiffOn_apply ℝ ℝ i _).sub contDiffOn_const)

example (n : Nat) (limits : Fin n → ℝ) : (coordinateRows n limits).rowCount = n := by
  simp [coordinateRows, Block.family, Block.le]
example (n : Nat) (limits : Fin n → ℝ) (i : Fin n) :
    ((coordinateRows n limits).rows (finSigmaFinEquiv (n := fun _ : Fin n => 1) ⟨i, 0⟩)).residual =
      fun x => x i - limits i := by
  exact congrArg Row.residual (Block.family_rows
    (fun j (x : Fin n → ℝ) => x j ≤ limits j)
    (fun j => Block.le Set.univ (fun x : Fin n → ℝ => x j) (fun _ => limits j)
      ((contDiffOn_apply ℝ ℝ j _).sub contDiffOn_const)) i (0 : Fin 1))
example (limits : Fin 0 → ℝ) : (coordinateRows 0 limits).rowCount = 0 := by
  simp [coordinateRows, Block.family]
example (limits x : Fin 0 → ℝ) : ∀ j, ((coordinateRows 0 limits).rows j).Holds x :=
  ((coordinateRows 0 limits).holds_iff x).mpr (fun i => Fin.elim0 i)

-- Dependent inner dimensions are concatenated in lexicographic order.
def nestedRows (n : Nat) (counts : Fin n → Nat)
    (limits : (i : Fin n) → Fin (counts i) → ℝ) :
    Block (Set.univ : Set ℝ) (fun x => ∀ i j, x ≤ limits i j) :=
  Block.family (fun i x => ∀ j, x ≤ limits i j) fun i =>
    Block.family (fun j x => x ≤ limits i j) fun j =>
      Block.le Set.univ id (fun _ => limits i j) (contDiffOn_id.sub contDiffOn_const)

example (n : Nat) (counts : Fin n → Nat)
    (limits : (i : Fin n) → Fin (counts i) → ℝ) :
    (nestedRows n counts limits).rowCount = ∑ i, counts i := by
  simp [nestedRows, Block.family, Block.le]

example {n : Nat} (counts : Fin n → Nat) (i : Fin n) (j : Fin (counts i)) :
    (finSigmaFinEquiv ⟨i, j⟩ : Nat) =
      (∑ k : Fin i, counts (Fin.castLE i.isLt.le k)) + j :=
  finSigmaFinEquiv_apply ⟨i, j⟩

example {n : Nat} {p : Fin n → ℝ → Prop}
    (blocks : ∀ i, Block (Set.univ : Set ℝ) (p i))
    (i : Fin n) (j : Fin (blocks i).rowCount) :
    (Block.family p blocks).rows (finSigmaFinEquiv ⟨i, j⟩) = (blocks i).rows j := by
  simp only [Block.family_rows]

-- Predicate transport, domain restriction, and projection retain actual data.
def transported : Block (Set.univ : Set ℝ) (fun x => ¬ x ^ 2 > x + 3) :=
  Block.ofIff _ _ (fun _ => not_lt) upper

example : transported.rows = upper.rows := rfl
example (x : ℝ) : (∀ i, (transported.rows i).Holds x) ↔ ¬ x ^ 2 > x + 3 :=
  transported.holds_iff x

def restricted := upper.mono (show (Set.Ioi (0 : ℝ)) ⊆ Set.univ from Set.subset_univ _)

example : (restricted.rows (0 : Fin 1)).residual = (upper.rows (0 : Fin 1)).residual := rfl
example : (restricted.rows (0 : Fin 1)).bounds = (upper.rows (0 : Fin 1)).bounds := rfl

def projected := restricted.pullback (Prod.fst : ℝ × ℝ → ℝ) contDiff_fst

example : projected.rowCount = restricted.rowCount := rfl
example (y : ℝ × ℝ) : (projected.rows (0 : Fin 1)).residual y = (upper.rows (0 : Fin 1)).residual y.1 := rfl
example (y : ℝ × ℝ) : (∀ i, (projected.rows i).Holds y) ↔ y.1 ^ 2 ≤ y.1 + 3 :=
  projected.holds_iff y
-- Domain membership is not inserted into row feasibility.
example : ∀ i, (projected.rows i).Holds (0, 9) := by
  apply (projected.holds_iff _).mpr
  norm_num

def maximum : Problem ℝ (OrderDual ℝ) where
  objective x := x ^ 4 - x ^ 2
  feasible x := x ^ 2 ≤ x + 3

def maximumForm : Form maximum :=
  Block.toForm maximum upper .maximize isOpen_univ
    ((contDiffOn_id.pow 4).sub (contDiffOn_id.pow 2)) (fun _ _ => Set.mem_univ _)

example : maximumForm.data.toProblem = maximum := maximumForm.represents
example : maximumForm.data.sense = .maximize := rfl
example : maximumForm.data.objective = maximum.objective := rfl
example : maximumForm.data.rowCount = 1 := rfl
example (x : ℝ) : maximumForm.data.toProblem.feasible x ↔ x ^ 2 ≤ x + 3 :=
  upper.holds_iff x
example : IsSmoothNLP maximum := maximumForm.isSmoothNLP

end

end MorewTest.NLP.RowData
