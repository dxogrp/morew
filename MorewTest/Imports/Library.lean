/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

namespace MorewTest.Imports.Library
open Morew

/-! These consumers must compile without `noncomputable`. Keep the returned maps,
recovery functions, and representation records in compiled code, where theorem-only
checks would not detect a loss of compiled usability. -/

private def affineTranslation (offset : ℝ) :
    Affine.Certified (fun x : ℝ => x + offset) :=
  Affine.Certified.add (Affine.Certified.id ℝ) (Affine.Certified.const ℝ offset)

private def recoverShiftedCoordinate {R : Type*} (offset : R → ℝ) (r : R) (x : ℝ) : ℝ :=
  (Substitution.addRight offset).preimage r ⟨x, trivial⟩

private def absoluteValueConstraint {X : Type*} (input bound : X → ℝ) :
    ConstraintRepr (fun x => |input x| ≤ bound x) :=
  Rewrite.absEpigraph.toConstraintRepr input bound

private def infinityDistance {n : Nat} (x y : Fin n → ℝ) : ℝ :=
  Fn.normInf (x - y)

noncomputable section

def source := problem (x : ℝ) minimize x subject to
    first : |x| ≤ 2
    second : |x| ≤ 3
reformulation targeted : source := by
  conic at first
  nlp at second
reformulation asConic : targeted := by conic
reformulation asNLP : targeted := by nlp
example : IsConic asConic := asConic.isConic
example : IsSmoothNLP asNLP := asNLP.isSmoothNLP
example : GlobalEquiv source asConic := targeted.equiv.trans asConic.equiv
example : GlobalEquiv source asNLP := targeted.equiv.trans asNLP.equiv
end
end MorewTest.Imports.Library
