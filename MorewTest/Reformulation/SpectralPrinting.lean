/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.MatrixFraction
import MorewTest.Reformulation.Spectral

/-! Stable source spelling, scalar rows, block dimensions, and auxiliary order. -/

namespace MorewTest.Reformulation.SpectralPrinting

open Morew Morew.Conic
open MorewTest.Reformulation.Spectral MorewTest.Reformulation.MatrixFraction

/--
info: problem (A : SymmetricMatrix n) (t : ℝ)
  minimize t
  subject to
    bound : Fn.lambdaMax A.toMatrix ≤ t
-/
#guard_msgs in
#printp largestSource

/--
info: problem (A : SymmetricMatrix n) (t : ℝ)
  minimize t
  subject to
    bound_conic_1 : t • 1 - A.toMatrix ∈ PSD n
-/
#guard_msgs in
#printp largestTarget

/--
info: problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
  minimize t
  subject to
    bound : ‖A‖ ≤ t
-/
#guard_msgs in
#printp normSource

/--
info: problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
  minimize t
  subject to
    bound_conic_1 : t ∈ ℝ₊
    bound_conic_2 : fromBlocksFin (t • 1) A A.transpose (t • 1) ∈ PSD (m + n)
-/
#guard_msgs in
#printp normTarget

/--
info: problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ) (bound_aux : SymmetricMatrix m × SymmetricMatrix n)
  minimize t
  subject to
    bound_conic_1 : bound_aux.1.fromBlocks A bound_aux.2 ∈ PSD (m + n)
    bound_conic_2 : t - (bound_aux.1.toMatrix.trace + bound_aux.2.toMatrix.trace) / 2 ∈ ℝ₊
-/
#guard_msgs in
#printp nuclearTarget

/--
info: problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ) (domain_aux : ↥(symmetricMatrixSubmodule n))
  minimize t
  subject to
    domain_conic_1 : (fromBlocksFin P.toMatrix 1 1 (SymmetricMatrix.toMatrix domain_aux)).PosSemidef
    bound : Fn.matrixFrac x P.toMatrix ≤ t
-/
#guard_msgs in
#printp domainIntermediate

/--
info: problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ) (domain_aux : ↥(symmetricMatrixSubmodule n))
  minimize t
  subject to
    domain_conic_1 : fromBlocksFin P.toMatrix 1 1 (SymmetricMatrix.toMatrix domain_aux) ∈ PSD (n + n)
    bound_conic_1 : fromBlocksFin P.toMatrix (fun i x_1 => x i) (fun x_1 => x) (Matrix.diagonal fun _ => t) ∈
      PSD (n + 1)
-/
#guard_msgs in
#printp terminal

end MorewTest.Reformulation.SpectralPrinting
