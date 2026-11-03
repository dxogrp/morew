/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Native matrix norms and spectral certificates for imported replay -/

namespace MorewTest.Reformulation.Spectral

open Morew Morew.Conic

noncomputable section

variable (n : Nat)

open scoped Matrix.Norms.L2Operator in
def normSource (m n : Nat) :=
  problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    minimize t
    subject to
      bound : ‖A‖ ≤ t

variable (m : Nat)

reformulation normTarget : (normSource m n) := by conic
open scoped Matrix.Norms.L2Operator in
def normObjective :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    minimize ‖A‖
    subject to
      anchor : A 0 0 = 1

def nuclearSource (m n : Nat) :=
  problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    minimize t
    subject to
      bound : Fn.nuclearNorm A ≤ t

reformulation nuclearTarget : (nuclearSource m n) := by conic
reformulation nuclearIntermediate : (nuclearSource m n) := by conic at bound

end
end MorewTest.Reformulation.Spectral
