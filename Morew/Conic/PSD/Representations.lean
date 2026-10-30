/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.PositiveDefinite
import Morew.Conic.PSD.MatrixFraction
import Morew.Conic.PSD.LambdaMax
import Morew.Conic.PSD.SpectralNorm
import Morew.Conic.PSD.NuclearNorm
import Morew.Rewrite.Basic

/-!
# Exact positive-semidefinite representation records

These records express spectral bounds, matrix fractions, and positive-definite
domains using the existing PSD cone and scalar inequalities, and connect their
mathematical equivalences to the public rewrite API.
The narrower mathematical imports remain independent of rewrite certificates
and do not install the modeling language or any global matrix norm instance.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace Morew.Conic

/-- Exact closed-cone representation of the open positive-definite domain. -/
noncomputable def positiveDefiniteLift {n : Nat} :
    ExactConstraintLift (fun P : Matrix (Fin n) (Fin n) ℝ => P.PosDef) where
  Auxiliary := SymmetricMatrix n
  target P W := (fromBlocksFin P 1 1 W.toMatrix).PosSemidef
  source_iff_exists := posDef_iff_exists_identity_block

end Morew.Conic

namespace Morew.Conic.MatrixFraction

/-- Matrix-fraction epigraph with an explicit positive-definite input domain. -/
noncomputable def epigraph {n : Nat} :
    EpigraphRepresentation (fun p : (Fin n → ℝ) ×
      {P : Matrix (Fin n) (Fin n) ℝ // P.PosDef} => Fn.matrixFrac p.1 p.2.1) where
  Auxiliary := Unit
  target p t _ :=
    (fromBlocksFin p.2.1 (fun (i : Fin n) (_ : Fin 1) => p.1 i) (fun _ : Fin 1 => p.1)
      (Matrix.diagonal (fun _ : Fin 1 => t))).PosSemidef
  source_iff_exists p t := by
    simpa only [exists_const] using matrixFrac_le_iff p.1 p.2.1 p.2.2 t

/-- Native dot-product/inverse spelling of the same exact epigraph. -/
noncomputable def nativeEpigraph {n : Nat} :
    EpigraphRepresentation (fun p : (Fin n → ℝ) ×
      {P : Matrix (Fin n) (Fin n) ℝ // P.PosDef} => p.1 ⬝ᵥ (p.2.1⁻¹ *ᵥ p.1)) :=
  epigraph

end Morew.Conic.MatrixFraction

namespace Morew.Conic.Spectral

/-- Exact PSD representation with explicit symmetry and nonempty dimension. -/
noncomputable def lambdaMaxEpigraph {n : Nat} (hn : 0 < n) :
    EpigraphRepresentation (fun A : {A : Matrix (Fin n) (Fin n) ℝ // A.IsSymm} =>
      Fn.lambdaMax A.1) where
  Auxiliary := Unit
  target A t _ := (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A.1).PosSemidef
  source_iff_exists A t := by
    simpa only [exists_const] using lambdaMax_le_iff A.1 A.2 hn t

/-- Exact PSD epigraph of the native matrix L2 operator norm. -/
noncomputable def spectralNormEpigraph {m n : Nat} :
    EpigraphRepresentation (fun A : Matrix (Fin m) (Fin n) ℝ => ‖A‖) where
  Auxiliary := Unit
  target A t _ := 0 ≤ t ∧
    (fromBlocksFin (t • 1) A A.transpose (t • 1)).PosSemidef
  source_iff_exists A t := by
    simpa only [exists_const] using spectralNorm_le_iff A t

/-- A proof-bearing nuclear-norm epigraph representation. -/
noncomputable def nuclearNormEpigraph {m n : Nat} :
    EpigraphRepresentation (Fn.nuclearNorm (m := m) (n := n)) where
  Auxiliary := SymmetricMatrix m × SymmetricMatrix n
  target A t aux := SymmetricMatrix.fromBlocks aux.1 A aux.2 ∈ PSD (m + n) ∧
    (aux.1.toMatrix.trace + aux.2.toMatrix.trace) / 2 ≤ t
  source_iff_exists A t := by
    simpa only [Prod.exists] using nuclearNorm_le_iff A t

end Morew.Conic.Spectral
