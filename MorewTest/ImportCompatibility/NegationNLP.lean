/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.NLP
import MorewTest.Reformulation.NegationNLP
import MorewTest.Reformulation.ReplaySupport

/-! # Imported signed NLP bounds and graph certificates. -/

namespace MorewTest.ImportCompatibility.NegationNLP

open Morew MorewTest.Reformulation.NegationNLP
open scoped MorewTest.Reformulation.NegationNLP.Graph

noncomputable section

reformulation continuedAbsolute : absoluteTarget := by nlp

example : GlobalEquiv absoluteSource continuedAbsolute :=
  absoluteBound.equiv.trans (absoluteTarget.equiv.trans continuedAbsolute.equiv)
example : IsSmoothNLP continuedAbsolute := continuedAbsolute.isSmoothNLP
example : continuedAbsolute.nlpForm.data.toProblem = continuedAbsolute :=
  continuedAbsolute.nlpForm.represents

reformulation continuedGraph : Graph.target := by nlp
reformulation importedGraph : Graph.source := by nlp at bound

example : GlobalEquiv Graph.source continuedGraph :=
  Graph.target.equiv.trans continuedGraph.equiv
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
    MorewTest.Reformulation.replayView view copied
      "signed NLP replay contains incomplete evidence"

example : logCopy = logSource := rfl
example : boundCopy = absoluteBound := rfl
example : absoluteCopy = absoluteTarget := rfl
example : graphSourceCopy = Graph.source := rfl
example : graphCopy = Graph.target := rfl

end Shadow

end
end MorewTest.ImportCompatibility.NegationNLP
