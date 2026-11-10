/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 1 do
    Lean.throwError "unexpected selective-import presentation providers"
  for backend in #[Morew.Elab.Rewrite.Registry.Target.conic, .nlp] do
    let rules ← Lean.Elab.Command.liftCoreM <| Morew.Elab.Rewrite.Registry.entries backend
    unless (rules.filter (·.declaration == ``Morew.Rewrite.absEpigraph)).size == 1 do
      Lean.throwError "selective imports did not install the default exact rule exactly once"

namespace MorewTest.Imports.ConicNLP
open Morew
noncomputable section

def source := problem (x : ℝ) minimize x subject to
    first : |x| ≤ 2
    second : |x| ≤ 3
reformulation targeted : source := by
  conic at first
  nlp at second
reformulation asConic : targeted := by conic
reformulation asNLP : targeted := by nlp
example : IsConic asConic := asConic.isConic
example : IsSmoothNLP asNLP := asNLP.isSmoothNLP
example : GlobalEquiv source asConic := targeted.equiv.trans asConic.equiv
example : GlobalEquiv source asNLP := targeted.equiv.trans asNLP.equiv
def quadraticSource := problem (x : ℝ) minimize (x - 1) ^ 2 subject to bound : |x| ≤ 2
reformulation quadratic : quadraticSource := by qconic
reformulation smoothQuadratic : quadraticSource := by nlp
example : IsQuadConic quadratic := quadratic.isQuadConic
example : IsSmoothNLP smoothQuadratic := smoothQuadratic.isSmoothNLP
example : GlobalEquiv quadraticSource quadratic := quadratic.equiv
example : GlobalEquiv quadraticSource smoothQuadratic := smoothQuadratic.equiv
end
end MorewTest.Imports.ConicNLP
