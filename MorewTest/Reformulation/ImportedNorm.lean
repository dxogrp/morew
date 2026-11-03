/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.Norm

/-! # Named vector-norm certificates and source views survive imports -/

namespace MorewTest.Reformulation.ImportedNorm

open Morew MorewTest.Reformulation.Norm

noncomputable section

variable (n : Nat)

reformulation continuedConic : (selected n) := by conic
reformulation continuedNLP : (selectedNLP n) := by nlp

example : GlobalEquivalence (source n) (continuedConic n) :=
  (selected.equivalence n).trans (continuedConic.equivalence n)
example : GlobalEquivalence (source n) (continuedNLP n) :=
  (selectedNLP.equivalence n).trans (continuedNLP.equivalence n)
example : IsConic (continuedConic n) := continuedConic.isConic n
example : IsSmoothNLP (continuedNLP n) := continuedNLP.isSmoothNLP n
example : (continuedConic.conicForm n).data.toProblem = continuedConic n :=
  (continuedConic.conicForm n).represents
example : (continuedNLP.nlpForm n).data.toProblem = continuedNLP n :=
  (continuedNLP.nlpForm n).represents

-- Replay under unrelated caller norms must keep the imported mathematical
-- functions and certificates intact.
section Shadow
local instance : Norm (Fin 2 → ℝ) := ⟨fun _ => 101⟩
local instance : Norm (WithLp 1 (Fin 2 → ℝ)) := ⟨fun _ => 103⟩
local instance : Norm (EuclideanSpace ℝ (Fin 2)) := ⟨fun _ => 107⟩

run_cmd do
  for (original, copied) in #[(``negativeObjective, `objectiveReplay),
      (``shadowed, `sourceReplay), (``shadowedConic, `conicReplay),
      (``shadowedNLP, `nlpReplay)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "named-norm import lost its presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let info ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if info.type.hasMVar || info.type.hasSorry || info.value!.hasMVar || info.value!.hasSorry then
      Lean.throwError "named-norm replay contains incomplete evidence"

example : objectiveReplay = negativeObjective := rfl
example : sourceReplay = source 2 := rfl
example : conicReplay = shadowedConic := rfl
example : nlpReplay = shadowedNLP := rfl

reformulation continuedShadow : shadowed := by conic
example : IsConic continuedShadow := continuedShadow.isConic
end Shadow

end
end MorewTest.Reformulation.ImportedNorm
