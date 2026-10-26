/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.NLPImportedSource

/-! # Applied imported sources preserve definitions, parameters, and presentation -/

namespace MorewTest.Reformulation.NLPImported

open Morew
noncomputable section

variable (radius : ℝ) (positive : 0 < radius)

reformulation target : (NLPImportedSource.family radius) := by
  nlp at magnitude

example : GlobalEquivalence (NLPImportedSource.family radius) (target radius) :=
  target.equivalence radius

reformulation continued : (target radius) := by
  epigraph t at first as square_bound

example : GlobalEquivalence (target radius) (continued radius) := continued.equivalence radius

/--
info: problem (x : ℝ)
  let first := x ^ 2
  let second := x ^ 2
  minimize first + second
  subject to
    lower : radius ≤ x
    magnitude_nlp_1 : Real.log x ≤ 5
    magnitude_nlp_2 : -Real.log x ≤ 5
    untouched : first ≤ second + 1
-/
#guard_msgs in
#printp target

/--
info: problem (x t : ℝ)
  let first := x ^ 2
  let second := x ^ 2
  minimize t + second
  subject to
    lower : radius ≤ x
    magnitude_nlp_1 : Real.log x ≤ 5
    magnitude_nlp_2 : -Real.log x ≤ 5
    untouched : first ≤ second + 1
    square_bound : first ≤ t
-/
#guard_msgs in
#printp continued

run_cmd do
  let environment ← Lean.getEnv
  for target in #[`target, `continued] do
    for artifact in #[`nlpForm, `isSmoothNLP] do
      let name := `MorewTest.Reformulation.NLPImported ++ target ++ artifact
      if environment.contains name then
        Lean.throwError "targeted rewriting emitted a whole-model NLP artifact {name}"

end
end MorewTest.Reformulation.NLPImported
