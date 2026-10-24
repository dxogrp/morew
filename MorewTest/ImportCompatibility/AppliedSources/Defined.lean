/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Exported applied-source families

Both original and generated presentations cross a compiled-module boundary.
-/

namespace MorewTest.ImportCompatibility.AppliedSources.Defined

open Morew
noncomputable section

namespace Source

abbrev Coordinate := ℝ

def score (x : Coordinate) : ℝ := x + 1

def within (x bound : Coordinate) : Prop := x ≤ bound

end Source

open Source

def family (bound : ℝ) :=
  problem (x : Coordinate)
    minimize score x
    subject to
      upper : within x bound

def naturalFamily (offset : Nat) :=
  problem (x : Nat)
    minimize x + offset

section

variable (limit : ℝ)

reformulation generated : (family limit) := by
  epigraph t as objectiveBound

end

def logarithmic (offset : ℝ) :=
  problem (x : ℝ)
    minimize Real.log x + offset
    subject to
      positive : 0 < x

section

variable (offset : ℝ)

reformulation substituted : (logarithmic offset) := by
  substitute x := Real.exp u

end

def absoluteBound (bound : ℝ) :=
  problem (x : ℝ)
    maximize x
    subject to
      magnitude : |x| ≤ bound

section

variable (limit : ℝ)

reformulation terminal : (absoluteBound limit) := by
  conic

end

end
end MorewTest.ImportCompatibility.AppliedSources.Defined
