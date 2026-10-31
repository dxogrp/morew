/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Rewrite.Match
import MorewTest.Affine.Support
import MorewTest.Environment
import Lean.Meta.Tactic.AuxLemma

/-! # Checked signed graph comparisons and isolated orientation retries -/

namespace MorewTest.Rewrite.Negation

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew MorewTest.Affine

private def hasView (term expected : TSyntax `term) : TermElabM Unit := do
  let source ← elaborate term
  let expected ← elaborate expected
  lambdaTelescope source fun points body => do
    let views ← Morew.Elab.Rewrite.Comparison.signedViews body
      (fun e => Morew.Elab.Rewrite.Registry.structural e)
    let mut found := false
    for view in views do
      checkWithKernel view.sourceIff
      unless ← isDefEq (← inferType view.sourceIff)
          (mkApp2 (mkConst ``Iff) body view.predicate) do
        throwError "signed view changed the selected source"
      found := found || (← isDefEq view.predicate (mkAppN expected points))
    unless found do throwError "missing signed graph comparison"

run_cmd liftTermElabM do
  hasView (← `(fun x y : ℝ => y = -|x|))
    (← `(fun x y : ℝ => |x| = -y))
  hasView (← `(fun x y : ℝ => -|x| = y))
    (← `(fun x y : ℝ => -y = |x|))
  hasView (← `(fun x y : ℝ => -(-(-|x|)) = -(-y)))
    (← `(fun x y : ℝ => -y = |x|))
  hasView (← `(fun x y : ℝ => -y = -|x|))
    (← `(fun x y : ℝ => |x| = y))

-- An altered negation can agree at these operands without being the checked
-- real operation. Such a graph equation must retain only its direct view.
run_cmd liftTermElabM do
  let source ← elaborate (← `(fun x y : ℝ =>
    y = @Neg.neg ℝ ⟨fun _ => -|x|⟩ |x|))
  lambdaTelescope source fun _ body => do
    let views ← Morew.Elab.Rewrite.Comparison.signedViews body
      (fun e => Morew.Elab.Rewrite.Registry.structural e)
    unless views.size == 1 do throwError "adapted an altered graph negation"

noncomputable def negativeIdentity : GraphRepresentation (fun x : ℝ => -x) where
  Auxiliary := Unit
  target x y _ := y = -x
  source_iff_exists _ _ := by simp only [exists_const]

-- Both direct orientations and the first signed orientation match but fail
-- consumer certification. The reversed signed view must get a fresh attempt,
-- and only that attempt's generated declaration may survive.
run_cmd liftTermElabM do
  let source ← elaborate (← `(fun z : ℝ × ℝ => -(-(-z.1)) = -(-(-z.2))))
  withLocalDeclD `point (← Morew.Elab.Rewrite.Plan.predicateDomain source) fun point => do
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let assigned ← mkFreshExprMVar (mkConst ``Nat)
    assigned.mvarId!.assign (mkNatLit 7)
    let before ← getMCtx
    let generated ← IO.mkRef (#[] : Array Name)
    let matched ← Morew.Elab.Rewrite.Match.declaration point (mkApp source point)
      ``negativeIdentity (fun matched => do
        let proof ← mkLambdaFVars #[point] matched.sourceIff
        let name ← mkAuxLemma [] (← inferType proof) proof (cache := false)
        generated.modify (·.push name)
        sentinel.mvarId!.assign (mkNatLit 19)
        if (← generated.get).size < 4 then
          throwError "reject this graph orientation during target certification"
        pure { matched with sourceIff := mkApp (mkConst name) point })
    let after ← getMCtx
    unless before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
      throwError "signed graph retry leaked scratch metavariables"
    if ← sentinel.mvarId!.isAssigned then
      throwError "signed graph retry changed a caller metavariable"
    unless (← instantiateMVars assigned) == mkNatLit 7 do
      throwError "signed graph retry changed a caller assignment"
    let names ← generated.get
    unless names.size == 4 do throwError "expected four isolated graph orientations: {names}"
    for name in names[:3] do
      if (← getEnv).contains name then
        throwError "signed graph retry retained a failed declaration"
    unless (← getEnv).contains names[3]! do
      throwError "signed graph retry discarded its successful declaration"
    checkWithKernel matched.sourceIff
    unless (matched.sourceIff.find? (·.isConstOf names[3]!)).isSome do
      throwError "signed graph retry lost its successful proof dependency"

end MorewTest.Rewrite.Negation
