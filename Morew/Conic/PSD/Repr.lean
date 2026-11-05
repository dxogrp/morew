/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.PosDef
import Morew.Conic.PSD.MatrixFraction
import Morew.Conic.PSD.LambdaMax
import Morew.Conic.PSD.SpectralNorm
import Morew.Conic.PSD.NuclearNorm
import Morew.Conic.PSD.LogDet
import Morew.Rewrite.Basic

/-!
# Exact positive-semidefinite representation records

Rewrite records for spectral bounds, matrix-fractional functions,
log-determinants, and positive definiteness using semidefinite and exponential
cones and scalar inequalities.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace Morew.Conic

/-- Exact closed-cone representation of the open positive-definite domain. -/
noncomputable def posDefRepr {n : Nat} :
    ConstraintRepr (fun P : Matrix (Fin n) (Fin n) ℝ => P.PosDef) where
  Auxiliary := SymmetricMatrix n
  target P W := (fromBlocksFin P 1 1 W.toMatrix).PosSemidef
  source_iff_exists := posDef_iff_exists_identity_block

end Morew.Conic

namespace Morew.Conic.MatrixFraction

/-- Matrix-fractional epigraph on positive-definite inputs. -/
noncomputable def epigraph {n : Nat} :
    EpigraphRepr (fun p : (Fin n → ℝ) ×
      {P : Matrix (Fin n) (Fin n) ℝ // P.PosDef} => Fn.matFrac p.1 p.2.1) where
  Auxiliary := Unit
  target p t _ :=
    (fromBlocksFin p.2.1 (fun (i : Fin n) (_ : Fin 1) => p.1 i) (fun _ : Fin 1 => p.1)
      (Matrix.diagonal (fun _ : Fin 1 => t))).PosSemidef
  source_iff_exists p t := by
    simpa only [exists_const] using matFrac_le_iff p.1 p.2.1 p.2.2 t

/-- The matrix-fractional epigraph for `x ⬝ᵥ (P⁻¹ *ᵥ x)`. -/
noncomputable def nativeEpigraph {n : Nat} :
    EpigraphRepr (fun p : (Fin n → ℝ) ×
      {P : Matrix (Fin n) (Fin n) ℝ // P.PosDef} => p.1 ⬝ᵥ (p.2.1⁻¹ *ᵥ p.1)) :=
  epigraph

end Morew.Conic.MatrixFraction

namespace Morew.Conic.Spectral

/-- Exact PSD representation with explicit symmetry and nonempty dimension. -/
noncomputable def lambdaMaxEpigraph {n : Nat} (hn : 0 < n) :
    EpigraphRepr (fun A : {A : Matrix (Fin n) (Fin n) ℝ // A.IsSymm} =>
      Fn.lambdaMax A.1) where
  Auxiliary := Unit
  target A t _ := (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A.1).PosSemidef
  source_iff_exists A t := by
    simpa only [exists_const] using lambdaMax_le_iff A.1 A.2 hn t

/-- A semidefinite representation of the Euclidean operator-norm epigraph. -/
noncomputable def spectralNormEpigraph {m n : Nat} :
    EpigraphRepr (fun A : Matrix (Fin m) (Fin n) ℝ => ‖A‖) where
  Auxiliary := Unit
  target A t _ := 0 ≤ t ∧
    (fromBlocksFin (t • 1) A A.transpose (t • 1)).PosSemidef
  source_iff_exists A t := by
    simpa only [exists_const] using spectralNorm_le_iff A t

/-- A semidefinite representation of the nuclear-norm epigraph. -/
noncomputable def normNucEpigraph {m n : Nat} :
    EpigraphRepr (Fn.normNuc (m := m) (n := n)) where
  Auxiliary := SymmetricMatrix m × SymmetricMatrix n
  target A t aux := SymmetricMatrix.fromBlocks aux.1 A aux.2 ∈ PSD (m + n) ∧
    (aux.1.toMatrix.trace + aux.2.toMatrix.trace) / 2 ≤ t
  source_iff_exists A t := by
    simpa only [Prod.exists] using normNuc_le_iff A t

end Morew.Conic.Spectral

namespace Morew.Conic.LogDet

/-- Exact PSD/exponential hypograph of log-determinant on its positive-definite
domain, with auxiliary coordinates on and below the diagonal. -/
noncomputable def hypograph {n : Nat} (hn : 0 < n) :
    HypographRepr (fun X : {X : Matrix (Fin n) (Fin n) ℝ // X.PosDef} =>
      Fn.logDet X.1) where
  Auxiliary := LowerTriangularEntries n × (Fin n → ℝ)
  target X t aux :=
    (fromBlocksFin X.1 (lowerTriangularMatrix aux.1) (lowerTriangularMatrix aux.1).transpose
      (Matrix.diagonal (fun i => lowerTriangularMatrix aux.1 i i))).PosSemidef ∧
    (∀ i, (aux.2 i, 1, lowerTriangularMatrix aux.1 i i) ∈ EXP) ∧ t ≤ ∑ i, aux.2 i
  source_iff_exists X t := by
    simpa only [Prod.exists] using le_logDet_iff X.1 X.2 t hn

/-- The ordinary logarithm-of-determinant expression has the same domain and representation. -/
noncomputable def nativeHypograph {n : Nat} (hn : 0 < n) :
    HypographRepr (fun X : {X : Matrix (Fin n) (Fin n) ℝ // X.PosDef} =>
      Real.log (Matrix.det X.1)) :=
  hypograph hn

end Morew.Conic.LogDet
