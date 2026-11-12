/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.SubstitutionRules
import MorewTest.Reformulation.ReplaySupport

/-! # Imported substitution descriptors and continued certified reformulations -/

namespace MorewTest.ImportCompatibility.Substitution

open Morew MorewTest.Reformulation.SubstitutionRules
noncomputable section

-- The custom descriptor is discovered from the imported persistent registry.
reformulation custom : positiveMargin := by substitute x := shiftedSquare u
example : GlobalEquiv positiveMargin custom := custom.equiv
example (u : ℝ) : custom.objective u = Real.log (shiftedSquare u) := rfl
example (u : ℝ) : custom.feasible u ↔ 1 ≤ shiftedSquare u := Iff.rfl

reformulation customSelected : positiveMargin := by
  substitute x := shiftedSquare u via shiftedSquareRule
example : GlobalEquiv positiveMargin customSelected := customSelected.equiv

reformulation continued : squared := by
  epigraph t
  conic
example : GlobalEquiv nonneg continued :=
  squared.equiv.trans continued.equiv
example : IsConic continued := continued.isConic

reformulation continuedMaximum : MiddleCoordinate.maximumTarget := by
  substitute u := v + 1
example : GlobalEquiv MiddleCoordinate.maximum continuedMaximum :=
  MiddleCoordinate.maximumTarget.equiv.trans continuedMaximum.equiv

-- Imported operations and certificates survive a caller-local spelling shadow.
namespace Shadow

def shiftedSquare (_ : ℝ) : ℝ := 37
reformulation renamedCustom : custom := by substitute u := v
example (v : ℝ) : renamedCustom.objective v =
    Real.log (MorewTest.Reformulation.SubstitutionRules.shiftedSquare v) := rfl
example : GlobalEquiv positiveMargin renamedCustom :=
  custom.equiv.trans renamedCustom.equiv

run_cmd do
  for (original, copied) in #[
      (``custom, `customCopy), (``continued, `continuedCopy),
      (``MorewTest.Reformulation.SubstitutionRules.squared, `squareCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported substitution lost presentation metadata"
    MorewTest.Reformulation.replayView view copied
      "substitution replay contains incomplete evidence"

example : customCopy = custom := rfl
example : continuedCopy = continued := rfl
example : squareCopy = squared := rfl

end Shadow

end
end MorewTest.ImportCompatibility.Substitution
