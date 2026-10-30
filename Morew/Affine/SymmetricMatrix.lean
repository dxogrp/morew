/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Affine.Matrix
import Morew.Conic.PSD

/-! Exact restriction of affine matrix maps to the symmetric-matrix space. -/

namespace Morew.Affine

open Morew.Conic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {n : Nat}

/-- Restrict an affine matrix map using a symmetry proof valid at every point. -/
noncomputable def restrictSymmetricMatrix
    (f : X →ᵃ[ℝ] Matrix (Fin n) (Fin n) ℝ) (h : ∀ x, (f x).IsSymm) :
    X →ᵃ[ℝ] SymmetricMatrix n where
  toFun x := SymmetricMatrix.ofMatrix (f x) (h x)
  linear := f.linear.codRestrict (symmetricMatrixSubmodule n) fun v => by
    change (f.linear v).IsSymm
    have hv : f.linear v = f v - f 0 := by
      simpa using f.linearMap_vsub v 0
    rw [hv]
    exact (h v).sub (h 0)
  map_vadd' p v := by
    apply Subtype.ext
    exact f.map_vadd p v

/-- Restriction preserves every ordinary matrix entry exactly. -/
@[simp]
theorem toMatrix_restrictSymmetricMatrix
    (f : X →ᵃ[ℝ] Matrix (Fin n) (Fin n) ℝ) (h : ∀ x, (f x).IsSymm) (x : X) :
    (restrictSymmetricMatrix f h x).toMatrix = f x := rfl

namespace Certified

/-- Convert a certified ordinary matrix using a universal symmetry witness. -/
noncomputable def toSymmetricMatrix {f : X → Matrix (Fin n) (Fin n) ℝ}
    (a : Certified f) (h : ∀ x, (f x).IsSymm) :
    Certified (fun x => SymmetricMatrix.ofMatrix (f x) (h x)) where
  map := restrictSymmetricMatrix a.map fun x => (a.correct x).symm ▸ h x
  correct x := SymmetricMatrix.toMatrix_injective (a.correct x)

/-- Forget a symmetry witness while retaining the certified ordinary entries. -/
noncomputable def fromSymmetricMatrix {f : X → SymmetricMatrix n} (a : Certified f) :
    Certified (fun x => (f x).toMatrix) where
  map := (SymmetricMatrix.toMatrixLinearMap n).toAffineMap.comp a.map
  correct x := congrArg SymmetricMatrix.toMatrix (a.correct x)

/-- Assemble finite-indexed blocks with their original affine entries. -/
noncomputable def fromBlocksFin {m n : Nat}
    {f : X → Matrix (Fin m) (Fin m) ℝ} {g : X → Matrix (Fin m) (Fin n) ℝ}
    {h : X → Matrix (Fin n) (Fin m) ℝ} {k : X → Matrix (Fin n) (Fin n) ℝ}
    (a : Certified f) (b : Certified g) (c : Certified h) (d : Certified k) :
    Certified (fun x => Morew.Conic.fromBlocksFin (f x) (g x) (h x) (k x)) :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks a b c d)

end Certified
end Morew.Affine
