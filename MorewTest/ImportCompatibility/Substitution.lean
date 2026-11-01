/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.SubstitutionRules

/-! # Imported substitution descriptors and continued certified reformulations -/

namespace MorewTest.ImportCompatibility.Substitution

open Morew MorewTest.Reformulation.SubstitutionRules
noncomputable section

-- The custom descriptor is discovered from the imported persistent registry.
reformulation custom : positiveMargin := by substitute x := shiftedSquare u
example : GlobalEquivalence positiveMargin custom := custom.equivalence
example (u : ℝ) : custom.objective u = Real.log (shiftedSquare u) := rfl
example (u : ℝ) : custom.feasible u ↔ 1 ≤ shiftedSquare u := Iff.rfl

reformulation customSelected : positiveMargin := by
  substitute x := shiftedSquare u via shiftedSquareRule
example : GlobalEquivalence positiveMargin customSelected := customSelected.equivalence

reformulation continued : squared := by
  epigraph t
  conic
example : GlobalEquivalence nonnegative continued :=
  squared.equivalence.trans continued.equivalence
example : IsConic continued := continued.isConic

reformulation continuedMaximum : MiddleCoordinate.maximumTarget := by
  substitute u := v + 1
example : GlobalEquivalence MiddleCoordinate.maximum continuedMaximum :=
  MiddleCoordinate.maximumTarget.equivalence.trans continuedMaximum.equivalence

-- Imported operations and certificates survive a caller-local spelling shadow.
namespace Shadow

def shiftedSquare (_ : ℝ) : ℝ := 37
reformulation renamedCustom : custom := by substitute u := v
example (v : ℝ) : renamedCustom.objective v =
    Real.log (MorewTest.Reformulation.SubstitutionRules.shiftedSquare v) := rfl
example : GlobalEquivalence positiveMargin renamedCustom :=
  custom.equivalence.trans renamedCustom.equivalence

run_cmd do
  for (original, copied) in #[
      (``custom, `customCopy), (``continued, `continuedCopy),
      (``MorewTest.Reformulation.SubstitutionRules.squared, `squareCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported substitution lost presentation metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "substitution replay contains incomplete evidence"

example : customCopy = custom := rfl
example : continuedCopy = continued := rfl
example : squareCopy = squared := rfl

end Shadow

end
end MorewTest.ImportCompatibility.Substitution
