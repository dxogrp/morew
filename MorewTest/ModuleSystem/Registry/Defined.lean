/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/
module

public import Morew.Elab.Rewrite.Registry
public import Morew.Elab.Substitution.Registry
public import Morew.Rewrite.Polyhedral
public import Morew.Substitution

/-! Rule exports follow declaration visibility, independently of body exposure. -/

namespace MorewTest.ModuleSystem.Registry.Defined

@[expose, morew_conic]
public def visibleRule := Morew.Rewrite.absEpigraph

@[morew_conic]
public opaque opaqueRule : Morew.EpigraphRepr (fun x : ℝ => |x|) :=
  Morew.Rewrite.absEpigraph

@[morew_conic]
private def hiddenRule := Morew.Rewrite.absEpigraph

@[expose, morew_substitute]
public def visibleSubstitution := Morew.Substitution.identity (R := ℝ) (X := ℝ)

@[morew_substitute]
public opaque opaqueSubstitution :
    Morew.CoordinateParameterization (fun (_ : ℝ) (x : ℝ) => x) :=
  Morew.Substitution.identity

@[morew_substitute]
private def hiddenSubstitution := Morew.Substitution.identity (R := ℝ) (X := ℝ)

run_cmd do
  Lean.Elab.Command.liftCoreM do
    let rules ← Morew.Elab.Rewrite.Registry.entries .conic
    for name in #[``visibleRule, ``opaqueRule, ``hiddenRule] do
      unless rules.any (·.declaration == name) do
        throwError "local rewrite registration is unavailable: {name}"
    let substitutions ← Morew.Elab.Substitution.Registry.entries
    for name in #[``visibleSubstitution, ``opaqueSubstitution, ``hiddenSubstitution] do
      unless substitutions.any (·.declaration == name) do
        throwError "local substitution registration is unavailable: {name}"

end MorewTest.ModuleSystem.Registry.Defined
