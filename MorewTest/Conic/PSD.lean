/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Symmetric-matrix and Schur-complement certificates

The semantic import provides the exact matrix carrier and both Schur pivot
orientations without installing the DSL. Rectangular off-diagonal blocks and
zero-dimensional blocks test the canonical indexing convention.
-/

assert_not_exists Morew.ExactConstraintLift Morew.Syntax.ProblemView

namespace MorewTest.Conic.PositiveSemidefinite

noncomputable section

open Morew.Conic

example (n : Nat) : NormedAddCommGroup (SymmetricMatrix n) := inferInstance
example (n : Nat) : NormedSpace ℝ (SymmetricMatrix n) := inferInstance
example (n : Nat) : FiniteDimensional ℝ (SymmetricMatrix n) := inferInstance
example (n : Nat) : (Cone.positiveSemidefinite n).Space = SymmetricMatrix n := rfl
example (n : Nat) : PSD n = (Cone.positiveSemidefinite n).carrier := rfl

example (n : Nat) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (SymmetricMatrix.ofMatrix M hM).toMatrix = M := rfl

example (n : Nat) (M : SymmetricMatrix n) :
    SymmetricMatrix.ofMatrix M.toMatrix M.isSymm = M := rfl

example (n : Nat) (M N : SymmetricMatrix n)
    (h : ∀ i j, M.toMatrix i j = N.toMatrix i j) : M = N := by
  ext i j
  exact h i j

example (n : Nat) (c : ℝ) (M N : SymmetricMatrix n) :
    (c • (M - N)).toMatrix = c • (M.toMatrix - N.toMatrix) := by simp

example (n : Nat) (M : SymmetricMatrix n) : M ∈ PSD n ↔ M.toMatrix.PosSemidef := by
  simp

example (n : Nat) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    SymmetricMatrix.ofMatrix M hM ∈ PSD n ↔ M.PosSemidef := by simp

example (n : Nat) : (0 : SymmetricMatrix n) ∈ PSD n := Matrix.PosSemidef.zero

example (n : Nat) (M N : SymmetricMatrix n) (hM : M ∈ PSD n) (hN : N ∈ PSD n) :
    M + N ∈ PSD n := (Cone.positiveSemidefinite n).carrier.add_mem hM hN

example (n : Nat) (M : SymmetricMatrix n) (hM : M ∈ PSD n) (c : ℝ) (hc : 0 < c) :
    c • M ∈ PSD n := (Cone.positiveSemidefinite n).carrier.smul_mem hc hM

example (n : Nat) :
    Convex ℝ (↑(Cone.positiveSemidefinite n).carrier : Set (Cone.positiveSemidefinite n).Space) :=
  (Cone.positiveSemidefinite n).carrier.convex

example (M : SymmetricMatrix 0) : M ∈ PSD 0 := by
  have hM : M = 0 := Subsingleton.elim _ _
  rw [hM]
  exact Matrix.PosSemidef.zero

example (a : ℝ) :
    SymmetricMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin 1 => a))
      (Matrix.isSymm_diagonal _) ∈ PSD 1 ↔ 0 ≤ a := by
  simp

example (a b c d : ℝ) :
    fromBlocksFin !![a] !![b] !![c] !![d] = !![a, b; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example (m n : Nat) (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n) (i : Fin m) (j : Fin n) :
    (SymmetricMatrix.fromBlocks A B D).toMatrix (Fin.castAdd n i) (Fin.natAdd m j) =
      B i j := by simp

example (m n : Nat) (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n) (i : Fin m) (j : Fin n) :
    (SymmetricMatrix.fromBlocks A B D).toMatrix (Fin.natAdd m j) (Fin.castAdd n i) =
      B i j := by simp

example (m n : Nat) (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n) (hA : A.toMatrix.PosDef) :
    (D.toMatrix - B.transpose * A.toMatrix⁻¹ * B).PosSemidef ↔
      SymmetricMatrix.fromBlocks A B D ∈ PSD (m + n) :=
  schurComplement_mem_iff A B D hA

example (m n : Nat) (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n) (hD : D.toMatrix.PosDef) :
    (A.toMatrix - B * D.toMatrix⁻¹ * B.transpose).PosSemidef ↔
      (fromBlocksFin A.toMatrix B B.transpose D.toMatrix).PosSemidef := by
  simpa using schurComplement_mem_iff_right A B D hD

private def identity (n : Nat) : SymmetricMatrix n :=
  SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one

private def scalar (a : ℝ) : SymmetricMatrix 1 :=
  SymmetricMatrix.ofMatrix !![a] (by ext i j; fin_cases i; fin_cases j; rfl)

/-! The `2 × 1` block `[1;2]` has squared length `5`. The two pivot
orientations produce different `3 × 3` block arrangements. -/

example : SymmetricMatrix.fromBlocks (identity 2) !![1; 2] (scalar 5) ∈ PSD 3 := by
  apply (schurComplement_mem_iff (identity 2) !![1; 2] (scalar 5) Matrix.PosDef.one).mp
  have h : (scalar 5).toMatrix - (!![1; 2] : Matrix (Fin 2) (Fin 1) ℝ).transpose *
      (identity 2).toMatrix⁻¹ * (!![1; 2] : Matrix (Fin 2) (Fin 1) ℝ) = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [identity, scalar, SymmetricMatrix.toMatrix, SymmetricMatrix.ofMatrix,
      Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_succ]
  rw [h]
  exact Matrix.PosSemidef.zero

example : SymmetricMatrix.fromBlocks (scalar 5) !![1, 2] (identity 2) ∈ PSD 3 := by
  apply (schurComplement_mem_iff_right (scalar 5) !![1, 2] (identity 2) Matrix.PosDef.one).mp
  have h : (scalar 5).toMatrix - (!![1, 2] : Matrix (Fin 1) (Fin 2) ℝ) *
      (identity 2).toMatrix⁻¹ * (!![1, 2] : Matrix (Fin 1) (Fin 2) ℝ).transpose = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [identity, scalar, SymmetricMatrix.toMatrix, SymmetricMatrix.ofMatrix,
      Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_succ]
  rw [h]
  exact Matrix.PosSemidef.zero

example : SymmetricMatrix.fromBlocks (identity 2) !![1; 2] (scalar 4) ∉ PSD 3 := by
  intro h
  have h' := (schurComplement_mem_iff (identity 2) !![1; 2] (scalar 4) Matrix.PosDef.one).mpr h
  have hd := h'.diag_nonneg (i := 0)
  norm_num [identity, scalar, SymmetricMatrix.toMatrix, SymmetricMatrix.ofMatrix,
    Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_succ] at hd

/-! Empty pivot and complementary blocks require no extra nonemptiness
assumptions. Positive definiteness of the empty identity is vacuous. -/

example (D : SymmetricMatrix 2) :
    SymmetricMatrix.fromBlocks (identity 0) (0 : Matrix (Fin 0) (Fin 2) ℝ) D ∈ PSD 2 ↔
      D ∈ PSD 2 := by
  rw [← schurComplement_mem_iff (identity 0) 0 D Matrix.PosDef.one]
  simp

example (A : SymmetricMatrix 2) :
    SymmetricMatrix.fromBlocks A (0 : Matrix (Fin 2) (Fin 0) ℝ) (identity 0) ∈ PSD 2 ↔
      A ∈ PSD 2 := by
  rw [← schurComplement_mem_iff_right A 0 (identity 0) Matrix.PosDef.one]
  simp

/-! A zero pivot cannot replace positive-definite evidence: totalized inversion
makes the complement zero, while the original block is indefinite. -/

example : ((0 : Matrix (Fin 1) (Fin 1) ℝ) - !![1].transpose *
    (0 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * !![1]).PosSemidef := by
  simpa using (Matrix.PosSemidef.zero (n := Fin 1) (R := ℝ))

example : SymmetricMatrix.fromBlocks (0 : SymmetricMatrix 1) !![1]
    (0 : SymmetricMatrix 1) ∉ PSD 2 := by
  intro h
  have h' := (Cone.mem_positiveSemidefinite _).mp h
  have heq : (SymmetricMatrix.fromBlocks (0 : SymmetricMatrix 1) !![1] 0).toMatrix =
      !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [heq] at h'
  have hquad := h'.dotProduct_mulVec_nonneg ![1, -1]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hquad

end
end MorewTest.Conic.PositiveSemidefinite
