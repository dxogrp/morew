/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Rewrite.Registry.Second
import MorewTest.Rewrite.Registry.First

open Lean Lean.Meta Lean.Elab.Term

-- Both import orders produce the same fully qualified candidate list.
run_elab do
  unless (← Morew.Elab.Rewrite.Registry.entries .nlp).any
      (·.declaration == ``MorewTest.Rewrite.Registry.Source.shiftedGraph) do
    throwError "an importing module exported an attribute deletion"
  let source ← elabTerm
    (← `(fun p : ℝ × ℝ => MorewTest.Rewrite.Registry.Source.shifted 3 p.1 ≤ p.2)) none
  synthesizeSyntheticMVarsNoPostponing
  let actual ← Morew.Elab.Rewrite.Registry.candidates .nlp (← instantiateMVars source)
  unless actual == #[``MorewTest.Rewrite.Registry.First.first,
      ``MorewTest.Rewrite.Registry.Second.second] do
    throwError "registry candidates depend on import order: {actual}"
