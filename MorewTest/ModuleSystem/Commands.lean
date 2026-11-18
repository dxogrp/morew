/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import MorewTest.ModuleSystem.Defined
import MorewTest.CommandSupport
import MorewTest.DiagnosticsSupport

/-! Native import visibility, exposed computational certificates, and command rollback. -/

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
      ``exposedTarget.conicForm, ``exposedCertificate, ``opaqueCertificate] do
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

/--
info: problem (x : ℝ)
  minimize ‖x‖
-/
#guard_msgs in
#printp opaqueNorm

example : GlobalEquiv opaqueSource opaqueTarget := opaqueCertificate
example : Conic.Form opaqueTarget := opaqueTarget.conicForm
example : IsConic opaqueTarget := opaqueTarget.isConic

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

-- A native private collision must fail before any target or alias is emitted.
def collision.conicForm : Nat := 19

#guard_error_fragments ["collision.conicForm", "has already been declared"] in
run_cmd do
  let before ← Lean.getEnv
  let targetIdent := Lean.mkIdent `collision
  let aliasIdent := Lean.mkIdent `collisionAlias
  let nested ← `(command|
    reformulation $targetIdent : (exposedTarget offset) certificate $aliasIdent := by
      conic)
  MorewTest.elabNoNewDeclarations nested fun name =>
    m!"failed native-module command leaked declaration {name}"
  let after ← Lean.getEnv
  let target := Lean.mkPrivateName after `MorewTest.ModuleSystem.collision
  if (Syntax.getProblemView? before target).isNone &&
      (Syntax.getProblemView? after target).isSome then
    Lean.throwError "failed native-module command leaked presentation metadata"

example : collision.conicForm = 19 := rfl

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
