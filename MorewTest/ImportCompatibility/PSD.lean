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
      (``diagonalRegisteredDetailed, `registeredDetailedCopy),
      (``auxiliaryTarget, `auxiliaryCopy), (``continued, `continuedCopy),
      (``substituted, `substitutedCopy), (``blockSchur, `blockSchurCopy),
      (``nestedBlocks, `nestedBlocksCopy), (``lambdaDiagonals, `lambdaDiagonalsCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported PSD declaration lost its replay metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "imported PSD replay contains incomplete evidence"

example : diagonalCopy = diagonalTarget := rfl
example : registeredDetailedCopy = diagonalRegisteredDetailed := rfl
example : auxiliaryCopy = auxiliaryTarget := rfl
example : continuedCopy = continued := rfl
example : substitutedCopy = substituted := rfl
example : blockSchurCopy A = blockSchur A := rfl
example : nestedBlocksCopy = nestedBlocks := rfl
example : lambdaDiagonalsCopy A = lambdaDiagonals A := rfl
end Shadow

namespace DimensionInstances

section CustomNumeral
local instance : OfNat Nat 2 := ⟨3⟩

-- This source really has dimension three, although its local spelling is `2`.
def source :=
  problem (M : SymmetricMatrix 2)
    minimize (0 : ℝ)
    subject to
      semidefinite : M ∈ PSD 2

reformulation target : source := by conic

example : Problem (SymmetricMatrix 3) ℝ := target

-- Imported ordinary dimensions must also survive a different numeral instance.
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``diagonalTarget
    | Lean.throwError "missing ordinary PSD replay metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand
    (← `(noncomputable def $(Lean.mkIdent `ordinaryReplay) := $term))

example : ordinaryReplay = diagonalTarget := rfl

-- Ordinary detailed display syntax also reconstructs the checked dimension.
-- Its proof-bearing matrix still has dimension two in this numeral context.
set_option pp.proofs true in
reformulation ordinaryDetailed : diagonalTarget := by conic

run_cmd do
  let some view := Syntax.getProblemDisplayView? (← Lean.getEnv) ``ordinaryDetailed
    | Lean.throwError "missing ordinary detailed PSD display metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand
    (← `(noncomputable def $(Lean.mkIdent `ordinaryDetailedReplay) := $term))

example : ordinaryDetailedReplay = ordinaryDetailed := rfl
end CustomNumeral

-- Leaving the section must not replace the stored dimension-three instance.
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing custom-dimension PSD replay metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand
    (← `(noncomputable def $(Lean.mkIdent `customReplay) := $term))

example : customReplay = target := rfl

end DimensionInstances

run_cmd do
  checkPSDDetails ``diagonalTarget "diagonalTarget._proof_1"
    #["semidefinite", "matrix", "PSD 2"]
  checkPSDDetails ``diagonalRegisteredDetailed "_proof_1"
    #["semidefinite", "matrix", "PSD 2"]
  checkPSDDetails ``blockSchur "_proof_" #["A.fromBlocks B", "PSD (1 + 1)"]
  checkPSDDetails ``nestedBlocks "_proof_"
    #["Matrix.diagonal ![x]", "Matrix.diagonal ![y]", "Matrix.diagonal ![z]", "fromBlocks"]
  checkPSDDetails ``lambdaDiagonals "_proof_" #["constant", "indexed", "fun i => d i + t"]
  let original ← MorewTest.Reformulation.PrintDetails.printed ``diagonalTarget false
  let imported ← MorewTest.Reformulation.PrintDetails.printed ``continued false
  unless original == imported do
    Lean.throwError "continued PSD certification changed the printed matrix or labels"

end
end MorewTest.ImportCompatibility.PositiveSemidefinite
