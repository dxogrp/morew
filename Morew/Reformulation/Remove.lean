/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Remove
import Morew.Reformulation.Replace

/-!
# User-selected constraint removal

Remove one current row after checking its implication from the remaining rows.
The shared replacement materializer establishes a fresh canonical checkpoint;
context-dependent redundancy is not an unconditional simplification lemma.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def removalStyle : Replace.Style := {
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
              (← Morew.Elab.Conic.Evidence.hasPlaceholders proof) then
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
      Replace.finish removalStyle state typed index {
        auxiliary? := none
        nextDomain := typed.semanticDomainType
        rowPredicates := #[]
        certificate := implied
        replacement
      } allocation

/-- Select exactly one current constraint. No names or auxiliaries are allocated. -/
def prepareRemove (state : ReformState) (selector : TSyntax `ident)
    (provided? : Option (TSyntax `term)) : CommandElabM SurfaceStepDraft := do
  let index ← Replace.findConstraint state selector
  return {
    nameRequests := #[]
    materialize := materializeRemove state selector index provided?
  }

end Morew.Reformulation.Internal
