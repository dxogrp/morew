/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.ImportCompatibility.LocalDefinitions.Defined

/-! Imported and generated model bindings retain their reference identities. -/

namespace MorewTest.ImportCompatibility.LocalDefinitions

open Morew
noncomputable section

-- This different global spelling must not capture the source's function.
def score (offset x : ℝ) : ℝ := x + offset

reformulation applied : (Defined.family 2) := by
  epigraph t

example (x t : ℝ) : applied.feasible (x, t) ↔
    Defined.External.score 2 x ≤ 10 ∧
      Defined.External.score 2 x + Defined.External.score 2 x ≤ t := Iff.rfl

reformulation continued : (Defined.generated 3) := by
  epigraph s

example : GlobalEquivalence (Defined.generated 3) continued := continued.equivalence

section

variable (loss : ℝ)

/-- error: source parameter `loss` conflicts with a model-local definition; rename the outer parameter -/
#guard_msgs in
reformulation parameterCollision : (Defined.family loss) := by
  epigraph t

end

section

variable (data : ℝ)
local notation "outerData" => data

section

variable (data : ℝ)

reformulation shadowedUnchanged : (Defined.shadowedFamily outerData data) := by

reformulation shadowedLifted : (Defined.shadowedFamily outerData data) := by
  epigraph t

end
end

example (left right x t : ℝ) : (shadowedLifted left right).feasible (x, t) ↔
    left - right + x ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  let loss := data - data_1 + x
  minimize t
  subject to
    epigraph_t : loss ≤ t
-/
#guard_msgs in
#printp shadowedLifted

section

variable (data other : Nat)

reformulation proofLifted : (Defined.proofFamily data) := by
  epigraph t

end

example (data : Nat) (x t : ℝ) : (proofLifted data).feasible (x, t) ↔
    Defined.proofCoefficient ⟨data, rfl⟩ + x ≤ t := Iff.rfl

universe u

section

variable (α : Type u) [Preorder α] (witness : True)

reformulation genericLifted : (Defined.generic α witness) := by
  epigraph a at label using (by
    refine { atValue := ?_, backward := ?_ }
    · intro point
      rfl
    · intro point _ auxiliary bound
      exact bound)

example (x a : α) : (genericLifted α witness).objective (x, a) = a := rfl

end

/--
info: problem (x a : α)
  let label : α := x
  let evidence := witness
  minimize a
  subject to
    epigraph_a : label ≤ a
-/
#guard_msgs in
#printp genericLifted

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo ``genericLifted
  unless info.levelParams.length == 1 do
    Lean.throwError "generic local-definition carrier lost its universe parameter"
  Lean.Meta.forallTelescope info.type fun parameters _ => do
    unless parameters.size == 3 do
      Lean.throwError "generic local-definition carrier lost its proof or instance parameter"
    unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType parameters[2]!) (Lean.mkConst ``True) do
      Lean.throwError "generic local-definition carrier changed its proof parameter"

open Lean in
run_cmd do
  for name in #[``applied, ``continued] do
    let some view := Syntax.getProblemView? (← getEnv) name
      | throwError "local-definition presentation missing"
    unless view.definitions.map (·.name.eraseMacroScopes) == #[`loss, `same, `total, `unused] do
      throwError "local-definition identity or order changed across import"
    unless view.definitions[2]!.value.reprint == some "loss + same" do
      -- Pretty-printer syntax often has synthetic source ranges; inspect the
      -- identifiers structurally instead of relying on source text below.
      let names := view.definitions[2]!.value.getArgs
      unless names.any (fun stx => stx.isIdent && stx.getId.eraseMacroScopes == `loss) do
        throwError "chained local definition lost its first binding reference"
  let some terminal := Syntax.getProblemView? (← getEnv) ``Defined.terminal
    | throwError "terminal conic target lost its presentation"
  unless terminal.definitions.map (·.name.eraseMacroScopes) == #[`score, `magnitude] do
    throwError "terminal conic target lost model-local definitions"

end
end MorewTest.ImportCompatibility.LocalDefinitions
