/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Rewrite.RegistrySecond
import MorewTest.Rewrite.RegistryFirst
import Mathlib.Tactic

open Lean Lean.Meta Lean.Elab.Term

-- Both import orders produce the same fully qualified candidate list.
run_elab do
  unless (← Morew.Elab.Rewrite.Registry.entries .nlp).any
      (·.declaration == ``MorewTest.Rewrite.RegistrySource.shiftedGraph) do
    throwError "an importing module exported an attribute deletion"
  let source ← elabTerm
    (← `(fun p : ℝ × ℝ => MorewTest.Rewrite.RegistrySource.shifted 3 p.1 ≤ p.2)) none
  synthesizeSyntheticMVarsNoPostponing
  let actual ← Morew.Elab.Rewrite.Registry.candidates .nlp (← instantiateMVars source)
  unless actual == #[``MorewTest.Rewrite.RegistryFirst.first,
      ``MorewTest.Rewrite.RegistrySecond.second] do
    throwError "registry candidates depend on import order: {actual}"
