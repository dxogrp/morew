import PTran.Elab.Reformulation
import Mathlib.Data.Nat.Basic

/-!
# Typed-runner entry-point compatibility

The established narrow import must expose name preflight, typed presentations,
and certificate operations without importing the surface command.
-/

namespace PTranTest.ImportCompatibility.Runner

open Lean Lean.Meta
open PTran.Elab.Reformulation

run_cmd do
  let env ← getEnv
  for name in #[``NameInventory, ``PresentationState, ``PresentationDelta,
      ``StepPlan.run, ``RunnerState.commit, ``RunnerState.finalCertificate] do
    unless env.contains name do
      throwError "the typed-runner entry point did not retain {name}"
  let requests : Array NameRequest := #[
    { id := 0, kind := .generatedBinderFamily, requested := `point }
  ]
  let .ok allocation :=
      preflightNameRequests { decisionBinders := #[`point] } requests
    | throwError "name preflight failed through the typed-runner entry point"
  unless allocation.findName? 0 == some `point_1 do
    throwError "name preflight did not retain generated-name freshening"

run_cmd Lean.Elab.Command.liftTermElabM do
  let nat := mkConst ``Nat
  let objective ← withLocalDeclD `point nat fun point =>
    mkLambdaFVars #[point] point
  let presentation : PresentationState := {
    sense := .minimize
    domainType := nat
    valueType := nat
    binders := #[{ name := `point, type := nat }]
    objective
  }
  let canonical ← presentation.canonicalProblem
  let certificate ← globalEquivalenceRunner.reflexivity canonical
  let composed ← globalEquivalenceRunner.compose certificate certificate
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let composed ← instantiateMVars composed
  check composed
  let expected ← globalEquivalenceRunner.relationType canonical canonical
  unless ← isDefEq (← inferType composed) expected do
    throwError "the typed-runner entry point changed the certificate relation"

end PTranTest.ImportCompatibility.Runner
