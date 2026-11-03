/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Reformulation.Remove
import Morew.Elab.Reformulation.Rows

/-!
# User-selected constraint removal

Remove one current row after checking its implication from the remaining rows.
The shared replacement materializer establishes a fresh canonical checkpoint;
context-dependent redundancy is not an unconditional simplification lemma.
-/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def removalStyle : Rows.Style := {
  family := "removed"
  diagnostic := "remove"
  certificateKind := `removedConstraint
}

private def materializeRemove (state : ReformState) (selector : TSyntax `ident)
    (index : Nat) (provided? : Option (TSyntax `term))
    (allocation : Morew.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => withoutErrToSorry do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let expected ← Morew.Elab.Reformulation.Remove.implicationType typed.presentation index
    -- The proof quantifies over current semantic coordinates. Displayed
    -- decision names and constraint labels are not added as local hypotheses.
    let implied ← match provided? with
      | some provided => withRef provided do
          let proof ← elabTermEnsuringType provided expected
          synthesizeSyntheticMVarsNoPostponing
          if (← getThe Core.State).messages.hasErrors then throwAbortTerm
          let proof ← instantiateMVars proof
          if (← Morew.Elab.Expr.hasUnresolved proof) ||
              (← Morew.Elab.Evidence.hasPlaceholders proof) then
            throwError "constraint removal proof contains unresolved metavariables or placeholders"
          withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
            checkWithKernel proof
          pure proof
      | none =>
          let some proof ← Morew.Elab.Reformulation.Remove.prove? typed.presentation index
            | throwErrorAt selector
                "cannot automatically remove constraint `{selector.getId.eraseMacroScopes}`; \
                provide `using` with a proof of {expected}"
          pure proof
    withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
      let replacement ← Morew.Elab.Reformulation.Remove.applyRemoval
        typed.presentation index implied
      Rows.finish removalStyle state typed index {
        auxiliary? := none
        nextDomain := typed.semanticDomainType
        rowPredicates := #[]
        «certificate» := implied
        replacement
      } allocation

/-- Select exactly one current constraint. No names or auxiliaries are allocated. -/
def prepareRemove (state : ReformState) (selector : TSyntax `ident)
    (provided? : Option (TSyntax `term)) : CommandElabM SurfaceStepDraft := do
  let index ← Rows.findConstraint state selector
  return {
    nameRequests := #[]
    materialize := materializeRemove state selector index provided?
  }

@[morew_reformulation_step Morew.removeStep]
private def elabRemove : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| remove at $selector:ident $[using $provided:term]?) =>
      prepareRemove state selector provided
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
