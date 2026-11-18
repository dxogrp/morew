/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import Morew.Affine
import Morew.Substitution
import Morew.Rewrite.Polyhedral
import Morew.Fn.Norm

/-! Ordinary runtime consumers of mathematical constructors and recovery maps. -/

namespace MorewTest.Runtime

open Morew

def translation (offset : ℝ) : Affine.Certified (fun x : ℝ => x + offset) :=
  Affine.Certified.add (Affine.Certified.id ℝ) (Affine.Certified.const ℝ offset)

example (offset x : ℝ) : (translation offset).map x = x + offset := rfl

def recoverShift (offset value : ℝ) : ℝ :=
  (Substitution.addRight (fun _ : Unit => offset)).preimage () ⟨value, True.intro⟩

example (offset value : ℝ) : recoverShift offset value + offset = value :=
  sub_add_cancel value offset

def absoluteRepresentation : EpigraphRepr (fun x : ℝ => |x|) :=
  Rewrite.absEpigraph

example (x bound : ℝ) :
    |x| ≤ bound ↔ ∃ auxiliary, absoluteRepresentation.target x bound auxiliary :=
  absoluteRepresentation.source_iff_exists x bound

def distanceInf {n : Nat} (x y : Fin n → ℝ) : ℝ :=
  Fn.normInf (x - y)

example {n : Nat} (x y : Fin n → ℝ) : 0 ≤ distanceInf x y :=
  Fn.normInf_nonneg (x - y)

end MorewTest.Runtime
