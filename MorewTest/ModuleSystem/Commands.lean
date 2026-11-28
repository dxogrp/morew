/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import MorewTest.ModuleSystem.Defined
meta import Lean.Elab.GuardMsgs

/-! Native import visibility, exposed computational certificates, and hygienic command names. -/

namespace MorewTest.ModuleSystem

open Morew
noncomputable section

run_cmd do
  let env ← Lean.getEnv
  for name in privateDeclarations do
    if env.contains name then
      Lean.throwError m!"ordinary import exposed private declaration {name}"
    if (Syntax.getProblemView? env name).isSome ||
        (Syntax.getProblemDisplayView? env name).isSome ||
        (Syntax.getProblemPrintPresentation? env name).isSome then
      Lean.throwError m!"ordinary import exposed private presentation {name}"
  for name in #[``printable, ``opaqueSource, ``opaqueTarget, ``opaqueTarget.equiv,
      ``opaqueTarget.conicForm, ``opaqueTarget.isConic] do
    unless env.contains name do
      Lean.throwError m!"ordinary import lost public declaration {name}"
    if (env.find? name).any (·.hasValue (allowOpaque := true)) then
      Lean.throwError m!"a public declaration acquired an exposed body: {name}"
  for name in #[``printable, ``opaqueNorm, ``opaqueSource, ``opaqueTarget] do
    unless (Syntax.getProblemDisplayView? env name).isSome do
      Lean.throwError m!"a public opaque model lost its display: {name}"
  for name in #[``exposedSource, ``exposedTarget, ``exposedTarget.equiv,
      ``exposedTarget.conicForm, ``exposedCertificate, ``opaqueCertificate,
      ``exposedFromOpaque, ``exposedFromOpaque.equiv, ``exposedFromOpaque.conicForm,
      ``exposedFromOpaqueCertificate] do
    unless (env.find? name).any (·.hasValue (allowOpaque := true)) do
      Lean.throwError m!"an exposed command artifact lost its body: {name}"
  let first := Lean.addMacroScope `MorewTest `generated 13
  let second := Lean.addMacroScope `MorewTest `generated 17
  match Elab.Reformulation.preflightDeclarationNames env #[
      { name := first }, { name := second }] with
  | .ok _ => pure ()
  | .error _ => Lean.throwError "global-name preflight erased distinct macro scopes"
  match Elab.Reformulation.preflightDeclarationNames env #[
      { name := first }, { name := Lean.mkPrivateName env first }] with
  | .error (.duplicate _) => pure ()
  | _ => Lean.throwError "global-name preflight missed a native private-name collision"

/--
info: problem (x : Nat)
  minimize x + 1
  subject to
    upper : x ≤ 7
-/
#guard_msgs in
#printp printable

private meta def checkOpaquePrinted (declaration : Lean.Name)
    (expected : Lean.TSyntax `term) : Lean.Elab.Command.CommandElabM Unit := do
  for proofs in #[false, true] do
    let saved ← get
    modify fun state => { state with messages := {}, snapshotTasks := #[] }
    let messages ← try
      let command ← if proofs then
        `(set_option pp.proofs true in #printp $(Lean.mkIdent declaration))
        else `(set_option pp.proofs false in #printp $(Lean.mkIdent declaration))
      Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages command
    finally
      modify fun state => { state with
        messages := saved.messages, snapshotTasks := saved.snapshotTasks }
    let [message] := messages.toList.filter (!·.isSilent)
      | Lean.throwError "expected a single printed problem"
    unless message.severity == .information && !message.isTrace do
      Lean.throwError m!"unexpected print diagnostic: {message.data}"
    let printed ← message.data.toString
    let .ok visible := Lean.Parser.runParserCategory (← Lean.getEnv) `term printed
      | Lean.throwError "printed opaque problem does not parse"
    Lean.Elab.Command.liftTermElabM do
      let expected ← Lean.Elab.Term.elabTerm expected none
      let actual ← Lean.Elab.Term.elabTermEnsuringType visible (← Lean.Meta.inferType expected)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let actual ← Lean.instantiateMVars actual
      if actual.hasMVar || actual.hasLevelMVar || actual.hasSorry then
        Lean.throwError "printed opaque problem contains unresolved terms"
      unless ← Lean.Meta.isDefEq actual expected do
        Lean.throwError m!"printing changed an opaque problem's meaning:\n{printed}"

-- An inaccessible source body still retains its original checked local instance.
run_cmd checkOpaquePrinted ``opaqueNorm (← `(problem (x : ℝ) minimize (7 : ℝ)))

section

local instance : HAdd Nat Nat Nat := ⟨fun _ _ => 0⟩
local instance : LE ℝ := ⟨fun _ _ => True⟩

-- The independently checked anchor must not be reinterpreted by ambient instances.
run_cmd do
  checkOpaquePrinted ``printable
    (← `(problem (x : Nat) minimize Nat.add x 1 subject to upper : x ≤ 7))

run_cmd do
  checkOpaquePrinted ``opaqueSource
    (← `(problem (x : ℝ) minimize x subject to lower : @LE.le ℝ Real.instLE 0 x))

end

example : GlobalEquiv opaqueSource opaqueTarget := opaqueCertificate
example : Conic.Form opaqueTarget := opaqueTarget.conicForm
example : IsConic opaqueTarget := opaqueTarget.isConic

example : GlobalEquiv opaqueSource exposedFromOpaque := exposedFromOpaqueCertificate
example : IsConic exposedFromOpaque := exposedFromOpaque.isConic
example (x : ℝ) : exposedFromOpaque.objective x = x := rfl
example (x : ℝ) : exposedFromOpaque.feasible x ↔ 0 ≤ x := Iff.rfl

example (point : FeasiblePoint opaqueSource) :
    (exposedFromOpaque.equiv.forward.map point).val = point.val := rfl

example (point : FeasiblePoint exposedFromOpaque) :
    (exposedFromOpaque.equiv.backward.map point).val = point.val := rfl

variable (offset : ℝ)

-- Exact reconstruction retains the exported source instance under a different norm.
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``normSource
    | Lean.throwError "an exposed norm model lost its exact reconstruction"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let term ← `(letI : Norm ℝ := ⟨fun _ => 91⟩; $term)
  let name := Lean.mkIdent `replayedNorm
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : (replayedNorm offset).objective x = offset := rfl

example : GlobalEquiv (exposedSource offset) (exposedTarget offset) :=
  exposedCertificate offset

example (point : FeasiblePoint (exposedSource offset)) :
    ((exposedTarget.equiv offset).forward.map point).val =
      (point.val, |point.val - offset|) := rfl

example (point : FeasiblePoint (exposedTarget offset)) :
    ((exposedTarget.equiv offset).backward.map point).val = point.val.1 := rfl

example : (exposedTarget.conicForm offset).data.rowCount = 2 := rfl

reformulation continued : (exposedTarget offset) := by
  epigraph value as newBound
  conic

example : GlobalEquiv (exposedSource offset) (continued offset) :=
  (exposedCertificate offset).trans (continued.equiv offset)

-- Macro-generated declaration names retain their scopes through native emission.
run_cmd do
  let target ← `(ident| hygienicTarget)
  let aliasIdent ← `(ident| hygienicCertificate)
  Lean.Elab.Command.elabCommand (← `(command|
    reformulation $target : (exposedSource (0 : ℝ)) certificate $aliasIdent := by
      epigraph bound))
  let targetName ← Lean.resolveGlobalConstNoOverload target
  let aliasName ← Lean.resolveGlobalConstNoOverload aliasIdent
  unless targetName.hasMacroScopes && aliasName.hasMacroScopes &&
      Lean.isPrivateName targetName && Lean.isPrivateName aliasName do
    Lean.throwError "generated declaration names lost native privacy or macro scopes"
  Lean.Elab.Command.liftTermElabM do
    let source ← Lean.Elab.Term.elabTerm (← `(exposedSource (0 : ℝ))) none
    let expected ← Lean.Meta.mkAppM ``GlobalEquiv #[source, Lean.mkConst targetName]
    for name in #[targetName ++ `equiv, aliasName] do
      let proof := Lean.mkConst name
      Lean.Meta.check proof
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType proof) expected do
        Lean.throwError "a hygienic certificate names the wrong source or target"

end
end MorewTest.ModuleSystem
