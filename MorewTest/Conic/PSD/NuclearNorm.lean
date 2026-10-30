/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.NuclearNorm
import Morew.Conic.PSD.Representations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Nuclear-norm semantics and exact completion certificates

The tests exercise the standard singular-value definition, both directions of
the lift, half-trace normalization, and degenerate dimensions.
-/

namespace MorewTest.Conic.Nuclear

noncomputable section

open Morew Morew.Conic Morew.Conic.Spectral

private theorem completion_entry_bound {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (hB : (Matrix.fromBlocks W A A.transpose V).PosSemidef) (i : Fin m) (j : Fin n) :
    2 * A i j ≤ W i i + V j j := by
  have h := hB.dotProduct_mulVec_nonneg (Sum.elim (Pi.single i 1) (Pi.single j (-1)))
  simp [Matrix.fromBlocks_mulVec, Function.comp_def, sumElim_dotProduct_sumElim,
    dotProduct_add] at h
  linarith

example : Fn.nuclearNorm (!![-3] : Matrix (Fin 1) (Fin 1) ℝ) = 3 := by
  rw [nuclearNorm_singleton]
  norm_num

example : Fn.nuclearNorm (!![3] : Matrix (Fin 1) (Fin 1) ℝ) = 3 := by
  rw [nuclearNorm_singleton]
  norm_num

-- Two nonzero singular values distinguish the nuclear norm from both the
-- Euclidean operator norm (four) and the Frobenius norm (five).
example : Fn.nuclearNorm (Matrix.diagonal ![3, 4]) = 7 := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![3, 4]
  let w₀ : Fin 2 ⊕ Fin 2 → ℝ := Sum.elim ![1, 0] ![1, 0]
  let w₁ : Fin 2 ⊕ Fin 2 → ℝ := Sum.elim ![0, 1] ![0, 1]
  have h₀ : (Matrix.vecMulVec w₀ w₀).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star w₀
  have h₁ : (Matrix.vecMulVec w₁ w₁).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star w₁
  have hb : (Matrix.fromBlocks A A A.transpose A).PosSemidef := by
    convert (h₀.smul (by norm_num : (0 : ℝ) ≤ 3)).add
      (h₁.smul (by norm_num : (0 : ℝ) ≤ 4)) using 1
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> norm_num [A, w₀, w₁, Matrix.vecMulVec]
  have upper := nuclearNorm_le_half_trace A hb
  norm_num [A, Matrix.trace, Fin.sum_univ_succ] at upper
  have lower₀ := completion_entry_bound A _ _ (nuclearWitness_block_posSemidef A) 0 0
  have lower₁ := completion_entry_bound A _ _ (nuclearWitness_block_posSemidef A) 1 1
  have hw := trace_nuclearLeftWitness A
  have hv := trace_nuclearRightWitness A
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] at hw hv
  norm_num [A] at lower₀ lower₁
  change Fn.nuclearNorm A = 7
  linarith

-- This 2 × 3 matrix has a zero row and two zero columns. The lift must admit
-- rank deficiency while retaining its nonzero singular value.
example : Fn.nuclearNorm (!![3, 0, 0; 0, 0, 0] : Matrix (Fin 2) (Fin 3) ℝ) = 3 := by
  let A : Matrix (Fin 2) (Fin 3) ℝ := !![3, 0, 0; 0, 0, 0]
  let W : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![3, 0]
  let V : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![3, 0, 0]
  let w : Fin 2 ⊕ Fin 3 → ℝ := Sum.elim ![1, 0] ![1, 0, 0]
  have hw : (Matrix.vecMulVec w w).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star w
  have hb : (Matrix.fromBlocks W A A.transpose V).PosSemidef := by
    convert hw.smul (by norm_num : (0 : ℝ) ≤ 3) using 1
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> norm_num [A, W, V, w, Matrix.vecMulVec]
  have upper := nuclearNorm_le_half_trace A hb
  norm_num [W, V, Matrix.trace, Fin.sum_univ_succ] at upper
  have witness := nuclearWitness_block_posSemidef A
  have lower := completion_entry_bound A _ _ witness 0 0
  have hw₁ := witness.diag_nonneg (i := Sum.inl 1)
  have hv₁ := witness.diag_nonneg (i := Sum.inr 1)
  have hv₂ := witness.diag_nonneg (i := Sum.inr 2)
  have htW := trace_nuclearLeftWitness A
  have htV := trace_nuclearRightWitness A
  simp [Matrix.trace, Fin.sum_univ_succ] at htW htV
  simp only [Matrix.fromBlocks_apply₁₁] at hw₁
  simp only [Matrix.fromBlocks_apply₂₂] at hv₁ hv₂
  norm_num [A] at lower
  change Fn.nuclearNorm A = 3
  linarith

example {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    (nuclearLeftWitness A).toMatrix.trace + (nuclearRightWitness A).toMatrix.trace =
      2 * Fn.nuclearNorm A := by
  rw [trace_nuclearLeftWitness, trace_nuclearRightWitness]
  ring

example (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ) :
    Fn.nuclearNorm A ≤ t ↔ ∃ W : SymmetricMatrix 2, ∃ V : SymmetricMatrix 3,
      SymmetricMatrix.fromBlocks W A V ∈ PSD 5 ∧
        (W.toMatrix.trace + V.toMatrix.trace) / 2 ≤ t :=
  nuclearNorm_le_iff A t

example (A : Matrix (Fin 3) (Fin 2) ℝ) (W : SymmetricMatrix 3) (V : SymmetricMatrix 2)
    (h : SymmetricMatrix.fromBlocks W A V ∈ PSD 5) :
    2 * Fn.nuclearNorm A ≤ W.toMatrix.trace + V.toMatrix.trace := by
  have hc : (Matrix.fromBlocks W.toMatrix A A.transpose V.toMatrix).PosSemidef := by
    rw [Cone.mem_positiveSemidefinite, SymmetricMatrix.toMatrix_fromBlocks,
      posSemidef_fromBlocksFin_iff] at h
    exact h
  have hb := nuclearNorm_le_half_trace A hc
  linarith

example (n : Nat) (A : Matrix (Fin 0) (Fin n) ℝ) (t : ℝ) :
    (∃ aux, (nuclearNormEpigraph (m := 0) (n := n)).target A t aux) ↔ 0 ≤ t := by
  rw [← nuclearNormEpigraph.source_iff_exists]
  simp

example (m : Nat) (A : Matrix (Fin m) (Fin 0) ℝ) (t : ℝ) :
    (∃ aux, (nuclearNormEpigraph (m := m) (n := 0)).target A t aux) ↔ 0 ≤ t := by
  rw [← nuclearNormEpigraph.source_iff_exists]
  simp

example (A : Matrix (Fin 0) (Fin 0) ℝ) :
    ¬ ∃ aux, (nuclearNormEpigraph (m := 0) (n := 0)).target A (-1) aux := by
  rw [← nuclearNormEpigraph.source_iff_exists]
  simp

example (m n : Nat) :
    ∃ aux, (nuclearNormEpigraph (m := m) (n := n)).target 0 0 aux := by
  rw [← nuclearNormEpigraph.source_iff_exists]
  simp

example (A : Matrix (Fin 2) (Fin 3) ℝ) :
    ¬ ∃ aux, (nuclearNormEpigraph (m := 2) (n := 3)).target A (-1) aux := by
  rw [← nuclearNormEpigraph.source_iff_exists]
  have h := Fn.nuclearNorm_nonneg A
  linarith

end

end MorewTest.Conic.Nuclear
