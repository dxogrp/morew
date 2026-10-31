/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.Support
import MorewTest.Environment
import Lean.Meta.Tactic.AuxLemma

/-!
# Checked operations and state isolation for negated comparisons

Sign adaptation must check the actual real operations and preserve the typed
underlying operation. Failed attempts leave caller metavariables and declarations
unchanged, including when the derived representation matches but its target is
not affine.
-/

namespace MorewTest.Conic.Negation

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew MorewTest.Affine

private def reject (term : TSyntax `term) (rule? : Option Name := none) :
    TermElabM Unit := do
  let source ← elaborate term
  let sentinel ← mkFreshExprMVar (mkConst ``Real)
  let assigned ← mkFreshExprMVar (mkConst ``Nat)
  assigned.mvarId!.assign (mkNatLit 7)
  let before ← getMCtx
  let environment ← getEnv
  let outcome ← match rule? with
    | some name => Morew.Elab.Conic.Rewrite.planDeclaration source name
    | none => Morew.Elab.Conic.Rewrite.planUnique source
  let .error _ := outcome | throwError "expected negated comparison rejection"
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "negation matching leaked scratch metavariables"
  if ← sentinel.mvarId!.isAssigned then
    throwError "negation matching assigned a caller metavariable"
  unless (← instantiateMVars assigned) == mkNatLit 7 do
    throwError "negation matching changed an existing caller assignment"
  unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "negation matching changed caller declarations"

-- Negation-looking syntax alone is insufficient: these operations are not
-- the canonical real negation or order used by the comparison equivalences.
run_cmd liftTermElabM do
  let badNeg ← `(fun z : ℝ × ℝ =>
    z.2 ≤ @Neg.neg ℝ ⟨fun x => x⟩ |z.1|)
  reject badNeg
  reject badNeg (some ``Morew.Rewrite.absEpigraph)
  let badOrder ← `(fun z : ℝ × ℝ =>
    @LE.le ℝ ⟨fun _ _ => True⟩ z.2 (-|z.1|))
  reject badOrder
  reject badOrder (some ``Morew.Rewrite.absEpigraph)
  let nestedBadNeg ← `(fun z : ℝ × ℝ =>
    z.2 ≤ -(@Neg.neg ℝ ⟨fun x => x⟩ (-|z.1|)))
  reject nestedBadNeg
  reject nestedBadNeg (some ``Morew.Rewrite.absEpigraph)
  -- Even agreement at these operands cannot replace checking the instance.
  let coincidentNeg ← `(fun z : ℝ × ℝ =>
    z.2 ≤ @Neg.neg ℝ ⟨fun _ => -|z.1|⟩ |z.1|)
  reject coincidentNeg
  reject coincidentNeg (some ``Morew.Rewrite.absEpigraph)
  let coincidentOrder ← `(fun z : ℝ × ℝ =>
    @LE.le ℝ ⟨fun _ _ => z.2 ≤ -|z.1|⟩ z.2 (-|z.1|))
  reject coincidentOrder
  reject coincidentOrder (some ``Morew.Rewrite.absEpigraph)

-- A canonical outer negation does not license replacing the norm instance.
run_cmd liftTermElabM do
  let badNorm ← `(fun z : EuclideanSpace ℝ (Fin 2) × ℝ =>
    z.2 ≤ -(@Norm.norm (EuclideanSpace ℝ (Fin 2)) ⟨fun _ => 0⟩ z.1))
  reject badNorm
  reject badNorm (some ``Morew.Conic.SecondOrder.normEpigraph)

section Elementwise
open scoped Matrix.Norms.Elementwise

run_cmd liftTermElabM do
  let source ← `(fun z : Matrix (Fin 2) (Fin 3) ℝ × ℝ => z.2 ≤ -‖z.1‖)
  reject source
  reject source (some ``Morew.Conic.Spectral.spectralNormEpigraph)
end Elementwise

section Frobenius
open scoped Matrix.Norms.Frobenius

run_cmd liftTermElabM do
  let source ← `(fun z : Matrix (Fin 2) (Fin 3) ℝ × ℝ => z.2 ≤ -‖z.1‖)
  reject source
  reject source (some ``Morew.Conic.Spectral.spectralNormEpigraph)
end Frobenius

run_cmd liftTermElabM do
  reject (← `(fun z : ℝ × ℝ => z.2 ^ 2 ≤ -|z.1|))
  reject (← `(fun z : ℝ × ℝ => z.2 ≤ -|z.1 ^ 2|))
  reject (← `(fun z : ℝ × ℝ => -|z.1| ≤ z.2))

noncomputable def negativeIdentity : EpigraphRepresentation (fun x : ℝ => -x) where
  Auxiliary := Unit
  target x t _ := -x ≤ t
  source_iff_exists _ _ := by simp only [exists_const]

-- Reject a matching view during consumer certification, then accept another
-- view of the same declaration. Only the successful attempt's declarations
-- may survive; neither callback may assign a caller's metavariable.
run_cmd liftTermElabM do
  let source ← elaborate (← `(fun z : ℝ × ℝ => -(-(-z.1)) ≤ z.2))
  withLocalDeclD `point (← Morew.Elab.Rewrite.Plan.predicateDomain source) fun point => do
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let generated ← IO.mkRef (#[] : Array Name)
    let matched ← Morew.Elab.Rewrite.Match.declaration point (mkApp source point)
      ``negativeIdentity (fun matched => do
        let proof ← mkLambdaFVars #[point] matched.sourceIff
        let name ← mkAuxLemma [] (← inferType proof) proof (cache := false)
        generated.modify (·.push name)
        sentinel.mvarId!.assign (mkNatLit 19)
        if (← generated.get).size == 1 then
          throwError "reject this view during target certification"
        pure { matched with sourceIff := mkApp (mkConst name) point })
      (conicNegation := true)
    let after ← getMCtx
    unless before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
      throwError "comparison retry leaked scratch metavariables"
    if ← sentinel.mvarId!.isAssigned then
      throwError "comparison retry changed a caller metavariable"
    let names ← generated.get
    unless names.size == 2 do throwError "expected two isolated matching views: {names}"
    unless !(← getEnv).contains names[0]! && (← getEnv).contains names[1]! do
      throwError "comparison retry retained declarations from the rejected view"
    checkWithKernel matched.sourceIff
    unless (matched.sourceIff.find? (·.isConstOf names[1]!)).isSome do
      throwError "accepted comparison lost its successful proof dependency"

end MorewTest.Conic.Negation
