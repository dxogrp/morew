/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Reformulation.Rows

/-! Add a consequence of the current constraints and retain the result for normalization. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def deriveStyle : Rows.Append.Style := {
  description := "derived constraint"
  certificateKind := `derivedConstraint
  family := "derived"
}

private def materializeDerive (state : ReformState) (label : TSyntax `ident)
    (proposition provided : TSyntax `term)
    (allocation : Morew.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let some name := allocation.findName? 0
    | throwErrorAt label "internal error: missing derived constraint label allocation"
  runTermElabM fun sectionFVars => withoutErrToSorry do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let (predicate, propositionSyntax) ←
      Rows.Append.elaboratePredicate deriveStyle state typed proposition
    -- Decision-dependent facts come only from the source point quantified in the proof type.
    let expected ← withLocalDeclD `point typed.semanticDomainType fun point => do
      let feasible ← mkAppM ``Morew.Problem.feasible #[typed.semantic, point]
      mkForallFVars #[point] (← mkArrow feasible (mkApp predicate point))
    let implied ← Rows.Append.elaborateProof provided expected "derived constraint proof"
    let addition ← mkAppM ``Morew.addConstraintEquiv
      #[typed.semantic, predicate, implied]
    Rows.Append.finish deriveStyle state typed name proposition predicate propositionSyntax addition

/-- Check the requested label before elaborating a derived constraint or its proof. -/
def prepareDerive (state : ReformState) (label : TSyntax `ident)
    (proposition provided : TSyntax `term) : CommandElabM SurfaceStepDraft :=
  pure {
    nameRequests := #[{
      id := 0, kind := .explicitConstraintLabel
      requested := label.getId.eraseMacroScopes, ref := label.raw }]
    materialize := materializeDerive state label proposition provided
  }

@[morew_reformulation_step Morew.deriveStep]
private def elabDerive : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| derive $label:ident : $proposition:term using $provided:term) =>
      prepareDerive state label proposition provided
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
