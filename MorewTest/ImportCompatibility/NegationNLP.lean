/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.NegationNLP

/-! # Imported signed NLP bounds and graph certificates. -/

namespace MorewTest.ImportCompatibility.NegationNLP

open Morew MorewTest.Reformulation.NegationNLP
open scoped MorewTest.Reformulation.NegationNLP.Graph

noncomputable section

reformulation continuedAbsolute : absoluteTarget := by nlp

example : GlobalEquivalence absoluteSource continuedAbsolute :=
  absoluteBound.equivalence.trans (absoluteTarget.equivalence.trans continuedAbsolute.equivalence)
example : IsSmoothNLP continuedAbsolute := continuedAbsolute.isSmoothNLP
example : continuedAbsolute.nlpForm.data.toProblem = continuedAbsolute :=
  continuedAbsolute.nlpForm.represents

reformulation continuedGraph : Graph.target := by nlp
reformulation importedGraph : Graph.source := by nlp at bound

example : GlobalEquivalence Graph.source continuedGraph :=
  Graph.target.equivalence.trans continuedGraph.equivalence
example : IsSmoothNLP continuedGraph := continuedGraph.isSmoothNLP
example : continuedGraph.nlpForm.data.toProblem = continuedGraph := continuedGraph.nlpForm.represents
example : importedGraph = Graph.target := rfl

/--
info: problem (x y : ℝ)
  minimize y
  subject to
    bound_nlp_1 : 0 ≤ -y
    bound_nlp_2 : (-y) ^ 2 = (x ^ 2 - 1) ^ 2
-/
#guard_msgs in
#printp continuedGraph

namespace Shadow

def abs (x : ℝ) : ℝ := x + 100
def Real.log (x : ℝ) : ℝ := x + 200

run_cmd do
  for (original, copied) in #[
      (``MorewTest.Reformulation.NegationNLP.logSource, `logCopy),
      (``MorewTest.Reformulation.NegationNLP.absoluteBound, `boundCopy),
      (``MorewTest.Reformulation.NegationNLP.absoluteTarget, `absoluteCopy),
      (``MorewTest.Reformulation.NegationNLP.Graph.source, `graphSourceCopy),
      (``MorewTest.Reformulation.NegationNLP.Graph.target, `graphCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported signed NLP declaration lost its presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "signed NLP replay contains incomplete evidence"

example : logCopy = logSource := rfl
example : boundCopy = absoluteBound := rfl
example : absoluteCopy = absoluteTarget := rfl
example : graphSourceCopy = Graph.source := rfl
example : graphCopy = Graph.target := rfl

end Shadow

end
end MorewTest.ImportCompatibility.NegationNLP
