/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.RenameFailures

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.RenameFailures

open Morew
noncomputable section

#guard_error_fragments ["constraint name `cap_conic_1` already exists"] in
assert_rename_atomic% generatedCollision generatedCollisionAlias in
reformulation generatedCollision : bounded certificate generatedCollisionAlias := by
  conic at cap
  rename lower to cap_conic_1

-- Renaming creates no selector alias for the former name.
#guard_error_fragments ["unknown or stale constraint label `cap`"] in
assert_rename_atomic% staleConic staleConicAlias in
reformulation staleConic : bounded certificate staleConicAlias := by
  rename cap to bound
  conic at cap

#guard_error_fragments ["unknown or stale constraint label `cap`"] in
assert_rename_atomic% staleNLP staleNLPAlias in
reformulation staleNLP : bounded certificate staleNLPAlias := by
  rename cap to bound
  nlp at cap

-- A late error also discards the helper stored by the completed conic step.
#guard_error_fragments ["constraint name `upper` already exists"] in
assert_rename_atomic% atomicTarget atomicAlias in
reformulation atomicTarget : bounded certificate atomicAlias := by
  conic at cap
  rename lower to fresh
  rename fresh to upper

reformulation atomicTarget : bounded certificate atomicAlias := by
  rename lower to lower

example : GlobalEquiv bounded atomicTarget := atomicAlias
example : atomicTarget = bounded := rfl

#guard_error_fragments ["cannot apply a reformulation step after a terminal step"] in
assert_rename_atomic% afterConic afterConicAlias in
reformulation afterConic : affine certificate afterConicAlias := by
  conic
  rename cap to bound

#guard_error_fragments ["cannot apply a reformulation step after a terminal step"] in
assert_rename_atomic% afterNLP afterNLPAlias in
reformulation afterNLP : affine certificate afterNLPAlias := by
  nlp
  rename cap to bound

end
end MorewTest.Reformulation.RenameFailures
