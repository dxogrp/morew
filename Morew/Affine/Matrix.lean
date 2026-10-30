/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Affine
import Mathlib.Data.Matrix.Block

/-! Certified affine constructions for ordinary real matrices. -/

namespace Morew.Affine.Certified

variable {X : Type*} [AddCommGroup X] [Module ℝ X]
variable {l m n o : Type*}

/-- Retain the ordinary matrix constructor without exposing arbitrary coercions. -/
noncomputable def matrixOf {f : X → m → n → ℝ} (a : Certified f) :
    Certified (fun x => Matrix.of (f x)) where
  map := (Matrix.ofLinearEquiv ℝ : (m → n → ℝ) ≃ₗ[ℝ] Matrix m n ℝ).toAffineEquiv.toAffineMap.comp a.map
  correct x := congrArg Matrix.of (a.correct x)

/-- Transpose an affine matrix. -/
noncomputable def transpose {f : X → Matrix m n ℝ} (a : Certified f) :
    Certified (fun x => (f x).transpose) where
  map := (Matrix.transposeLinearEquiv m n ℝ ℝ).toAffineEquiv.toAffineMap.comp a.map
  correct x := congrArg Matrix.transpose (a.correct x)

/-- Put an affine vector on the diagonal. -/
noncomputable def diagonal [DecidableEq n] {f : X → n → ℝ} (a : Certified f) :
    Certified (fun x => Matrix.diagonal (f x)) where
  map := (Matrix.diagonalLinearMap n ℝ ℝ).toAffineMap.comp a.map
  correct x := congrArg Matrix.diagonal (a.correct x)

/-- Reindex an affine matrix by fixed row and column functions. -/
noncomputable def submatrix {f : X → Matrix m n ℝ} (a : Certified f)
    (rows : l → m) (cols : o → n) :
    Certified (fun x => (f x).submatrix rows cols) where
  map := (show Matrix m n ℝ →ₗ[ℝ] Matrix l o ℝ from
    { toFun := fun M => M.submatrix rows cols
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toAffineMap.comp a.map
  correct x := congrArg (fun M => M.submatrix rows cols) (a.correct x)

/-- Reindex an affine matrix by fixed equivalences. -/
noncomputable def reindex {f : X → Matrix m n ℝ} (rows : m ≃ l) (cols : n ≃ o)
    (a : Certified f) : Certified (fun x => Matrix.reindex rows cols (f x)) :=
  submatrix a rows.symm cols.symm

/-- Assemble four affine blocks without enumerating any matrix dimension. -/
noncomputable def fromBlocks {f : X → Matrix n l ℝ} {g : X → Matrix n m ℝ}
    {h : X → Matrix o l ℝ} {k : X → Matrix o m ℝ}
    (a : Certified f) (b : Certified g) (c : Certified h) (d : Certified k) :
    Certified (fun x => Matrix.fromBlocks (f x) (g x) (h x) (k x)) where
  map := AffineMap.pi fun i => AffineMap.pi fun j =>
    Sum.elim
      (fun i => Sum.elim (fun j => (eval (eval a i) j).map)
        (fun j => (eval (eval b i) j).map) j)
      (fun i => Sum.elim (fun j => (eval (eval c i) j).map)
        (fun j => (eval (eval d i) j).map) j) i
  correct x := by
    funext i j
    cases i <;> cases j
    · exact congrFun (congrFun (a.correct x) _) _
    · exact congrFun (congrFun (b.correct x) _) _
    · exact congrFun (congrFun (c.correct x) _) _
    · exact congrFun (congrFun (d.correct x) _) _

/-- Left multiplication by a fixed, possibly rectangular matrix. -/
noncomputable def matrixMulConstLeft [Fintype m] {f : X → Matrix m n ℝ}
    (A : Matrix l m ℝ) (a : Certified f) : Certified (fun x => A * f x) where
  map := (show Matrix m n ℝ →ₗ[ℝ] Matrix l n ℝ from
    { toFun := (A * ·)
      map_add' := Matrix.mul_add A
      map_smul' := Matrix.mul_smul A }).toAffineMap.comp a.map
  correct x := congrArg (A * ·) (a.correct x)

/-- Right multiplication by a fixed, possibly rectangular matrix. -/
noncomputable def matrixMulConstRight [Fintype m] {f : X → Matrix l m ℝ}
    (a : Certified f) (A : Matrix m n ℝ) : Certified (fun x => f x * A) where
  map := (show Matrix l m ℝ →ₗ[ℝ] Matrix l n ℝ from
    { toFun := (· * A)
      map_add' := fun _ _ => Matrix.add_mul _ _ A
      map_smul' := fun _ _ => Matrix.smul_mul _ _ A }).toAffineMap.comp a.map
  correct x := congrArg (· * A) (a.correct x)

end Morew.Affine.Certified
