/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.PSD

/-!
# Imported PSD proof replay and continued reformulations
-/

namespace MorewTest.ImportCompatibility.PositiveSemidefinite

open Morew Morew.Conic
open MorewTest.Reformulation.PositiveSemidefinite
noncomputable section

reformulation continued : diagonalTarget := by conic

example : GlobalEquivalence diagonalSource continued :=
  diagonalTarget.equivalence.trans continued.equivalence
example : continued.conicForm.data.toProblem = continued := continued.conicForm.represents

variable (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef)

reformulation importedSchur : (schurSelected A) := by conic

example : GlobalEquivalence (schurSource A) (importedSchur A) :=
  (schurSelected.equivalence A hA).trans (importedSchur.equivalence A)
example : (importedSchur.conicForm A).data.rowCount = 3 := rfl

namespace Shadow
def Matrix.diagonal (x : ℝ) : ℝ := x + 100
def SymmetricMatrix.ofMatrix (x : ℝ) : ℝ := x + 200

run_cmd do
  for (original, copied) in #[(``diagonalTarget, `diagonalCopy),
      (``auxiliaryTarget, `auxiliaryCopy), (``continued, `continuedCopy),
      (``substituted, `substitutedCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported PSD declaration lost its replay metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "imported PSD replay contains incomplete evidence"

example : diagonalCopy = diagonalTarget := rfl
example : auxiliaryCopy = auxiliaryTarget := rfl
example : continuedCopy = continued := rfl
example : substitutedCopy = substituted := rfl
end Shadow

run_cmd do
  let original ← MorewTest.Reformulation.PrintDetails.printed ``diagonalTarget false
  let imported ← MorewTest.Reformulation.PrintDetails.printed ``continued false
  unless original == imported do
    Lean.throwError "continued PSD certification changed the printed matrix or labels"

end
end MorewTest.ImportCompatibility.PositiveSemidefinite
