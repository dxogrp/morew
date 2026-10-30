/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Exported finite-coordinate presentations with recoverable proof detail -/

namespace MorewTest.ImportCompatibility.PrintDetails.Defined

open Morew
noncomputable section

theorem firstIndexBound : 0 < 3 := by decide

def source :=
  problem (x : Fin 3 → ℝ) (t : ℝ)
    let index : Fin (4 - 1) := ⟨0, firstIndexBound⟩
    let offset : ℝ := @Nat.cast ℝ Real.instNatCast index.val
    minimize t + offset
    subject to
      coordinate : x ⟨0, firstIndexBound⟩ ≤ t
      shifted : ∀ j : Fin 2, x ⟨j.val + 1, by omega⟩ ≤ t
      bound : |t| ≤ 3
      remaining : |t| ≤ 5

set_option pp.coercions false in
reformulation lowered : source := by conic at bound

set_option pp.coercions false in
set_option pp.proofs true in
reformulation registeredDetailed : source := by conic at bound

namespace BinderTypes

abbrev Indexed (_ : Fin 2) := ℝ

def source (offset : ℝ) :=
  problem (entry : Indexed ⟨0, Nat.zero_lt_two⟩) (x : ℝ)
    minimize (entry : ℝ) + x + offset
    subject to
      bound : |x| ≤ 1
      remaining : |(entry : ℝ)| ≤ 2

reformulation lowered : (source 0) := by conic at bound

set_option pp.proofs true in
reformulation registeredDetailed : (source 0) := by conic at bound

end BinderTypes

end
end MorewTest.ImportCompatibility.PrintDetails.Defined
