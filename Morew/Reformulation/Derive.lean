/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Append

/-!
# Derived constraints

Append a user-proved consequence of current feasibility. The supplied proof is
checked against the complete current semantic problem before the new row is
introduced. A fresh canonical checkpoint retains every displayed row and its
label across subsequent reformulations.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def deriveStyle : Append.Style := {
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
      Append.elaboratePredicate deriveStyle state typed proposition
    -- The temporary model binders are no longer in scope: only the source
    -- point quantified by this contract may supply decision-dependent facts.
    let expected ← withLocalDeclD `point typed.semanticDomainType fun point => do
      let feasible ← mkAppM ``Morew.Problem.feasible #[typed.semantic, point]
      mkForallFVars #[point] (← mkArrow feasible (mkApp predicate point))
    let implied ← withRef provided do
      let proof ← elabTermEnsuringType provided expected
      synthesizeSyntheticMVarsNoPostponing
      if (← getThe Core.State).messages.hasErrors then throwAbortTerm
      let proof ← instantiateMVars proof
      if proof.hasMVar || proof.hasSorry then
        throwError "derived constraint proof contains unresolved metavariables or placeholders"
      withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
        checkWithKernel proof
      pure proof
    let addition ← mkAppM ``Morew.addConstraintEquivalence
      #[typed.semantic, predicate, implied]
    Append.finish deriveStyle state typed name proposition predicate propositionSyntax addition

/-- Preflight the explicit label before elaborating a derived row or its proof. -/
def prepareDerive (state : ReformState) (label : TSyntax `ident)
    (proposition provided : TSyntax `term) : CommandElabM SurfaceStepDraft :=
  pure {
    nameRequests := #[{
      id := 0, kind := .explicitConstraintLabel
      requested := label.getId.eraseMacroScopes, ref := label.raw }]
    materialize := materializeDerive state label proposition provided
  }

end Morew.Reformulation.Internal
