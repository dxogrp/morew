/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.NLPFailures

/-! Backend integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.NLPFailures

open Morew
noncomputable section

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
reformulation afterTerminal : source := by
  conic
  nlp at bound

run_cmd do
  let env ← Lean.getEnv
  for target in #[`unknown, `stale, `reverse, `equality, `nested, `remaining,
      `missingDomain, `noIdentity, `ambiguous, `wrongRecord, `wrongPredicate,
      `unresolvedRule, `invalidGeneratedDomain, `strict, `afterAuxiliary, `afterTerminal] do
    let name := `MorewTest.Reformulation.NLPFailures ++ target
    for declaration in #[name, name ++ `equivalence] do
      if env.contains declaration then
        Lean.throwError "failed NLP reformulation emitted {declaration}"
    if (Morew.Syntax.getProblemView? env name).isSome then
      Lean.throwError "failed NLP reformulation registered presentation metadata"
  if env.contains `MorewTest.Reformulation.NLPFailures.failedAlias then
    Lean.throwError "failed NLP reformulation emitted its certificate alias"

end
end MorewTest.Reformulation.NLPFailures
