/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/
module

import MorewTest.ModuleSystem.Registry.Defined

/-! Ordinary imports retain public opaque rules and exclude private registrations. -/

open MorewTest.ModuleSystem.Registry.Defined

run_cmd do
  Lean.Elab.Command.liftCoreM do
    let env ← Lean.getEnv
    let rules ← Morew.Elab.Rewrite.Registry.entries .conic
    for name in #[``visibleRule, ``opaqueRule] do
      unless rules.any (·.declaration == name) do
        throwError "import lost public rewrite registration: {name}"
    for entry in rules do
      if Lean.isPrivateName entry.declaration || !env.contains entry.declaration then
        throwError "import retained unavailable rewrite registration: {entry.declaration}"
    let substitutions ← Morew.Elab.Substitution.Registry.entries
    for name in #[``visibleSubstitution, ``opaqueSubstitution] do
      unless substitutions.any (·.declaration == name) do
        throwError "import lost public substitution registration: {name}"
    for entry in substitutions do
      if Lean.isPrivateName entry.declaration || !env.contains entry.declaration then
        throwError "import retained unavailable substitution registration: {entry.declaration}"
    for name in #[``opaqueRule, ``opaqueSubstitution] do
      if (env.find? name).any (·.hasValue (allowOpaque := true)) then
        throwError "opaque registry fixture unexpectedly exposes its body: {name}"
    for name in #[``visibleRule, ``visibleSubstitution] do
      unless (env.find? name).any (·.hasValue) do
        throwError "exposed registry fixture lost its imported body: {name}"
