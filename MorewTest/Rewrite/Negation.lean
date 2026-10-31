/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Rewrite.Match
import Morew.Elab.Conic.Rewrite
import Morew.Elab.NLP.Rewrite
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

namespace FixedParameters

noncomputable def squareEpigraph : EpigraphRepresentation (fun x : ℝ => x ^ 2) where
  Auxiliary := Unit
  target x t _ := x ^ 2 ≤ t
  source_iff_exists _ _ := by simp only [exists_const]

noncomputable def indexedAbs (n : Nat) (x : ℝ) : ℝ := |x - n|

noncomputable def indexedAbsEpigraph (n : Nat) :
    EpigraphRepresentation (indexedAbs n) where
  Auxiliary := Unit
  target x t _ := x - n ≤ t ∧ -(x - n) ≤ t
  source_iff_exists x t := Rewrite.absEpigraph.source_iff_exists (x - n) t

noncomputable def finAbs (i : Fin 3) (x : ℝ) : ℝ := indexedAbs i.val x

noncomputable def finAbsEpigraph (i : Fin 3) : EpigraphRepresentation (finAbs i) :=
  indexedAbsEpigraph i.val

noncomputable def flaggedAbs (flag : Bool) (x : ℝ) : ℝ :=
  indexedAbs (if flag then 0 else 1) x

noncomputable def flaggedAbsEpigraph (flag : Bool) : EpigraphRepresentation (flaggedAbs flag) :=
  indexedAbsEpigraph (if flag then 0 else 1)

structure Parameters where
  count : Nat
  flag : Bool

noncomputable def parameterAbs (parameters : Parameters) (x : ℝ) : ℝ :=
  indexedAbs (parameters.count + if parameters.flag then 0 else 1) x

noncomputable def parameterAbsEpigraph (parameters : Parameters) :
    EpigraphRepresentation (parameterAbs parameters) :=
  indexedAbsEpigraph (parameters.count + if parameters.flag then 0 else 1)

private def checkApplied (term conicRule nlpRule : TSyntax `term) (rows : Nat) :
    TermElabM Unit := do
  let source ← elaborate term
  let conic ← Morew.Elab.Conic.Rewrite.planExplicit source (← elaborate conicRule)
  let .ok conic := conic
    | match conic with
      | .error error => throwError "fixed conic parameter failed: {error.reason}"
      | .ok _ => throwError "unreachable"
  conic.toResult.check source #[]
  unless conic.rowPredicates.size == rows do throwError "wrong fixed conic row count"
  let nlp ← Morew.Elab.NLP.Rewrite.plan source #[] (some (← elaborate nlpRule))
  let .ok nlp := nlp
    | match nlp with
      | .error error => throwError "fixed NLP parameter failed: {error.reason}"
      | .ok _ => throwError "unreachable"
  nlp.toResult.check source #[]
  unless nlp.rowPredicates.size == rows do throwError "wrong fixed NLP row count"

-- Applied records still accept definitionally equal discrete parameters. Both
-- literal and signed comparisons retain the original source in their proofs.
run_cmd liftTermElabM do
  checkApplied (← `(fun p : ℝ × ℝ => p.1 ^ (1 + 1 : Nat) ≤ p.2))
    (← `(Conic.SecondOrder.squareEpigraph)) (← `(squareEpigraph)) 1
  checkApplied (← `(fun p : ℝ × ℝ => p.2 ≤ -(p.1 ^ (1 + 1 : Nat))))
    (← `(Conic.SecondOrder.squareEpigraph)) (← `(squareEpigraph)) 1
  checkApplied (← `(fun p : ℝ × ℝ => indexedAbs 2 p.1 ≤ p.2))
    (← `(indexedAbsEpigraph (1 + 1))) (← `(indexedAbsEpigraph (1 + 1))) 2
  checkApplied (← `(fun p : ℝ × ℝ => p.2 ≤ -indexedAbs 2 p.1))
    (← `(indexedAbsEpigraph (1 + 1))) (← `(indexedAbsEpigraph (1 + 1))) 2
  checkApplied (← `(fun p : ℝ × ℝ => finAbs ⟨2, by decide⟩ p.1 ≤ p.2))
    (← `(finAbsEpigraph ⟨1 + 1, by decide⟩))
    (← `(finAbsEpigraph ⟨1 + 1, by decide⟩)) 2
  checkApplied (← `(fun p : ℝ × ℝ => p.2 ≤ -flaggedAbs true p.1))
    (← `(flaggedAbsEpigraph (!false))) (← `(flaggedAbsEpigraph (!false))) 2
  checkApplied (← `(fun p : ℝ × ℝ => parameterAbs ⟨2, true⟩ p.1 ≤ p.2))
    (← `(parameterAbsEpigraph ⟨1 + 1, !false⟩))
    (← `(parameterAbsEpigraph ⟨1 + 1, !false⟩)) 2

-- Section-fixed parameters may compute, but may not change. Failed applied
-- records leave the caller's metavariable state and declarations untouched.
run_cmd liftTermElabM do
  let expression ← elaborate (← `(fun (n : Nat) (p : ℝ × ℝ) =>
    p.2 ≤ -indexedAbs (n + 1) p.1))
  lambdaTelescope expression fun arguments body => do
    let source ← mkLambdaFVars #[arguments[1]!] body
    let rule ← mkAppM ``indexedAbsEpigraph #[arguments[0]!]
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let environment ← getEnv
    if let .ok _ ← Morew.Elab.Conic.Rewrite.planExplicit source rule then
      throwError "symbolic conic parameter changed its value"
    if let .ok _ ← Morew.Elab.NLP.Rewrite.plan source #[] (some rule) then
      throwError "symbolic NLP parameter changed its value"
    let after ← getMCtx
    unless before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
      throwError "failed symbolic parameter matching leaked scratch metavariables"
    if ← sentinel.mvarId!.isAssigned then
      throwError "failed symbolic parameter matching changed a caller metavariable"
    unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
      throwError "failed symbolic parameter matching changed caller declarations"

-- Computing discrete parameters must neither change their values nor erase
-- the actual real power instance, even when it agrees at the selected exponent.
run_cmd liftTermElabM do
  for term in #[
      (← `(fun p : ℝ × ℝ => p.1 ^ (1 + 2 : Nat) ≤ p.2)),
      (← `(fun p : ℝ × ℝ =>
        @HPow.hPow ℝ Nat ℝ ⟨fun x _ => x ^ 2⟩ p.1 (1 + 1) ≤ p.2))] do
    let source ← elaborate term
    if let .ok _ ← Morew.Elab.Conic.Rewrite.planExplicit source
        (← elaborate (← `(Conic.SecondOrder.squareEpigraph))) then
      throwError "fixed parameter comparison accepted an altered conic power"
    if let .ok _ ← Morew.Elab.NLP.Rewrite.plan source #[]
        (some (← elaborate (← `(squareEpigraph)))) then
      throwError "fixed parameter comparison accepted an altered NLP power"

def natHelper (n : Nat) : Nat := n + 1

def natHelperLift : ExactConstraintLift (fun n : Nat => n = natHelper 1) :=
  .ofIff (fun n => n = 2) (fun _ => Iff.rfl)

-- Even a closed, definitionally equal endpoint must preserve its represented
-- mathematical head. Discrete-value comparison is confined to its arguments.
run_cmd liftTermElabM do
  let source ← elaborate (← `(fun n : Nat => n = 2))
  withLocalDeclD `point (mkConst ``Nat) fun point => do
    let succeeded ← try
        discard <| Morew.Elab.Rewrite.Match.declaration point (mkApp source point)
          ``natHelperLift pure
        pure true
      catch _ => pure false
    if succeeded then throwError "discrete parameter comparison unfolded an endpoint"

end FixedParameters

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
