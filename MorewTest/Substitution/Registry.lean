/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.ElabSupport
import MorewTest.Substitution.Registry.Source
import Morew.Elab.Substitution.Match
import MorewTest.Environment

/-!
# Coordinate registry and typed matching regressions

These checks exercise parameterizations independently of the substitution DSL.
Imported, scoped, removed, and explicit rules all pass through the same matcher.
-/

namespace MorewTest.Substitution.Registry

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Substitution
open Source

private def selected (map : TSyntax `term) (expected : Array Name) : TermElabM Unit := do
  let actual ← Registry.candidates (← elaborateUnchecked map)
  unless actual == expected do throwError "unexpected coordinate candidates {actual}"

run_elab do
  selected (← `(fun (_ : ℝ) (u : ℝ) => u)) #[``Morew.Substitution.identity]
  selected (← `(fun (r : ℝ) (u : ℝ) => shift r u)) #[``shiftRule]

section
attribute [local morew_substitute] shiftAlias
attribute [local morew_substitute] shiftAlias
run_elab do
  selected (← `(fun (r : ℝ) (u : ℝ) => shift r u)) #[``shiftAlias, ``shiftRule]
end

section
open scoped MorewTest.Substitution.Registry.Source.Scoped
run_elab do
  selected (← `(fun (_ : ℝ) (u : ℝ) => u ^ 2))
    #[``Morew.Substitution.square, ``Scoped.squareRule]
end

section
attribute [-morew_substitute] shiftRule
run_elab do
  selected (← `(fun (r : ℝ) (u : ℝ) => shift r u)) #[]
end

run_elab do
  selected (← `(fun (r : ℝ) (u : ℝ) => shift r u)) #[``shiftRule]
  selected (← `(fun (_ : ℝ) (u : ℝ) => u ^ 2)) #[``Morew.Substitution.square]

private def withSource {α : Type} (map feasible : TSyntax `term)
    (action : Expr → Expr → Expr → Expr → Expr → TermElabM α) : TermElabM α := do
  let map ← elaborateUnchecked map
  let feasible ← elaborateUnchecked feasible
  let .forallE _ domain _ _ ← whnf (← inferType feasible)
    | throwError "expected feasibility predicate"
  withLocalDeclD `point domain fun point =>
    withLocalDeclD `feasible (mkApp feasible point) fun evidence =>
      action map point (.proj ``Prod 0 point) (.proj ``Prod 1 point) evidence

private def matched (map feasible : TSyntax `term) (name? : Option Name := none) :
    TermElabM Unit := withSource map feasible fun map point retained selected evidence => do
  let before ← getMCtx
  let result ← match name? with
    | some name => Match.declaration map point retained selected evidence name pure
    | none => Match.discover map point retained selected evidence pure
  checkWithKernel result.rule
  checkWithKernel result.rangeProof
  assertMVarCountersUnchanged before "successful matching leaked scratch metavariables"

private def rejected (map feasible : TSyntax `term) (fragment : String)
    (name? : Option Name := none) : TermElabM Unit :=
  withSource map feasible fun map point retained selected evidence => do
    let before ← getMCtx
    let environment ← getEnv
    let error? ← try
        let _ ← match name? with
          | some name => Match.declaration map point retained selected evidence name pure
          | none => Match.discover map point retained selected evidence pure
        pure (none : Option String)
      catch error => pure (some (← error.toMessageData.toString))
    let some error := error? | throwError "coordinate matching unexpectedly succeeded"
    unless error.contains fragment do throwError "unexpected coordinate diagnostic: {error}"
    assertMVarCountersUnchanged before "failed matching leaked scratch metavariables"
    unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
      throwError "failed matching changed declarations"

run_elab do
  let unconstrained ← `(fun _ : ℝ × ℝ => True)
  matched (← `(fun (_ : ℝ) (u : ℝ) => u)) unconstrained
  matched (← `(fun (_ : ℝ) (u : ℝ) => -u)) unconstrained
  matched (← `(fun (r : ℝ) (u : ℝ) => u + r)) unconstrained
  matched (← `(fun (r : ℝ) (u : ℝ) => r + u)) unconstrained
  matched (← `(fun (r : ℝ) (u : ℝ) => u - r)) unconstrained
  matched (← `(fun (r : ℝ) (u : ℝ) => r - u)) unconstrained
  matched (← `(fun (r : ℝ) (u : ℝ) => shift (r + 1) u)) unconstrained
  matched (← `(fun (r : ℝ) (u : ℝ) => shift r u)) unconstrained (some ``shiftAlias)
  matched (← `(fun (r : ℝ) (u : ℝ) => r * u)) (← `(fun p : ℝ × ℝ => p.1 ≠ 0))
  matched (← `(fun (r : ℝ) (u : ℝ) => u * r)) (← `(fun p : ℝ × ℝ => 0 < p.1))
  matched (← `(fun (r : ℝ) (u : ℝ) => r * u + (r + 1)))
    (← `(fun p : ℝ × ℝ => p.1 < 0))
  matched (← `(fun (_ : ℝ) (u : ℝ) => Real.exp u)) (← `(fun p : ℝ × ℝ => 1 ≤ p.2))
  matched (← `(fun (_ : ℝ) (u : ℝ) => u ^ 2)) (← `(fun p : ℝ × ℝ => 0 ≤ p.2))
  rejected (← `(fun (_ : ℝ) (u : ℝ) => u + u)) unconstrained "fully certified"
  rejected (← `(fun (_ : ℝ) (u : ℝ) => 2 * (u + 1))) unconstrained "fully certified"
  rejected (← `(fun (_ : ℝ) (u : ℝ) => u ^ 2)) unconstrained "coverage"
  rejected (← `(fun (_ : ℝ) (u : ℝ) => 0 * u)) unconstrained "coverage"

section
attribute [local morew_substitute] shiftAlias
run_elab do
  let map ← `(fun (r : ℝ) (u : ℝ) => shift r u)
  let feasible ← `(fun _ : ℝ × ℝ => True)
  rejected map feasible "ambiguous coordinate parameterizations"
  matched map feasible (some ``shiftRule)
  matched map feasible (some ``shiftAlias)
end

private noncomputable def hiddenSquare (u : ℝ) : ℝ := u ^ 2
private noncomputable def hiddenConstant (_u : ℝ) : ℝ := 1

run_elab do
  rejected (← `(fun (_ : ℝ) (u : ℝ) => hiddenSquare u))
    (← `(fun p : ℝ × ℝ => 0 ≤ p.2)) "does not match" (some ``Morew.Substitution.square)

-- Higher-order coefficient inference must not unfold a named helper to erase
-- its fresh-coordinate dependency. Structural beta/let/projection reduction
-- can discard that coordinate without changing mathematical function heads.
run_elab do
  let unconstrained ← `(fun _ : ℝ × ℝ => True)
  rejected (← `(fun (_ : ℝ) (u : ℝ) => u + hiddenConstant u))
    unconstrained "rigid binder"
  rejected (← `(fun (r : ℝ) (u : ℝ) => u + (r + hiddenConstant u)))
    unconstrained "rigid binder" (some ``Morew.Substitution.addRight)
  matched (← `(fun (r : ℝ) (u : ℝ) => u + ((fun (_ : ℝ) => r) u))) unconstrained
  matched (← `(fun (r : ℝ) (u : ℝ) => u + (let _discarded := u; r))) unconstrained
  matched (← `(fun (r : ℝ) (u : ℝ) => u + (r, hiddenConstant u).1)) unconstrained

private def wrapped (x : ℝ) : ℝ := x

private def wildcardRule (h : ℝ → ℝ → ℝ) (inverse : ∀ r x, h r (x - r) = x) :
    Morew.CoordinateParameterization (fun r u => wrapped (h r u)) where
  range _ _ := True
  preimage r x := x.1 - r
  rightInverse r x := inverse r x.1

-- A custom schema can explicitly pass both rigid coordinates to a wildcard.
-- Its independently checked inverse then justifies the more general map.
run_elab do
  let inverse ← elaborateUnchecked (← `(show ∀ r x : ℝ, (x - r) + r = x from
    fun r x => sub_add_cancel x r))
  withLetDecl `inverse (← inferType inverse) inverse fun _ => do
    matched (← `(fun (r : ℝ) (u : ℝ) => wrapped (u + r)))
      (← `(fun _ : ℝ × ℝ => True)) (some ``wildcardRule)

private noncomputable abbrev alteredNeg : Neg ℝ := ⟨fun u => u + 1⟩

run_elab do
  rejected (← `(fun (_ : ℝ) (u : ℝ) => @Neg.neg ℝ alteredNeg u))
    (← `(fun _ : ℝ × ℝ => True)) "unsupported coordinate type or operation instance"
    (some ``Morew.Substitution.neg)

-- Applied records need neither an attribute nor declaration-style inference.
run_elab do
  withSource (← `(fun (r : ℝ) (u : ℝ) => shift (r + 1) u))
      (← `(fun _ : ℝ × ℝ => True)) fun map point retained selected evidence => do
    let expression ← elaborateUnchecked (← `(shiftAlias (fun r : ℝ => r + 1)))
    let result ← Match.rule map point retained selected evidence expression pure
    checkWithKernel result.rangeProof

-- An unresolved caller metavariable must not become an inferred coefficient.
run_elab do
  withSource (← `(fun (_ : ℝ) (u : ℝ) => u))
      (← `(fun _ : ℝ × ℝ => True)) fun _ point retained selected evidence => do
    let real ← elaborateUnchecked (← `(ℝ))
    let coefficient ← mkFreshExprMVar real
    let map ← withLocalDeclD `retained real fun r =>
      withLocalDeclD `coordinate real fun u => do
        mkLambdaFVars #[r, u] (← mkAppM ``HMul.hMul #[coefficient, u])
    let before ← getMCtx
    let rejected ← try
        discard <| Match.declaration map point retained selected evidence
          ``Morew.Substitution.mulLeft pure
        pure false
      catch _ => pure true
    unless rejected && !(← coefficient.mvarId!.isAssigned) do
      throwError "coordinate matcher assigned a caller coefficient metavariable"
    unless before.mvarCounter == (← getMCtx).mvarCounter do
      throwError "caller-metavariable rejection leaked scratch state"

section
attribute [local morew_substitute] shiftAlias

-- Certification failures discard declarations before trying the next rule.
-- A successful callback's checked proof dependencies remain available.
run_elab do
  withSource (← `(fun (r : ℝ) (u : ℝ) => shift r u))
      (← `(fun _ : ℝ × ℝ => True)) fun map point retained selected evidence => do
    let discarded ← IO.mkRef (none : Option Name)
    let accepted ← IO.mkRef (none : Option Name)
    let result ← Match.discover map point retained selected evidence fun result => do
      if result.rule.getAppFn.isConstOf ``shiftAlias then
        let proof ← mkEqRefl (mkNatLit 0)
        let name ← mkAuxLemma [] (← inferType proof) proof
          (kind? := some `discardedParameterization) (cache := false)
        discarded.set (some name)
        throwError "consumer rejects this candidate after allocating proof state"
      let some discardedName ← discarded.get
        | throwError "regression did not exercise the rejected candidate"
      if (← getEnv).contains discardedName then
        throwError "failed parameterization left an auxiliary declaration"
      let proof ← mkLambdaFVars #[point, evidence] result.rangeProof
      let name ← mkAuxLemma [] (← inferType proof) proof
        (kind? := some `acceptedParameterization) (cache := false)
      accepted.set (some name)
      return { result with rangeProof := mkApp2 (mkConst name) point evidence }
    checkWithKernel result.rangeProof
    let some discardedName ← discarded.get | throwError "missing rejected candidate"
    let some acceptedName ← accepted.get | throwError "missing accepted candidate"
    if (← getEnv).contains discardedName then throwError "discarded declaration escaped"
    unless (← getEnv).contains acceptedName do throwError "accepted proof dependency lost"

end

private noncomputable def positiveShift {R : Type*} (c : ℝ) (_positive : 0 < c) :
    Morew.CoordinateParameterization (fun (_ : R) (u : ℝ) => shift c u) :=
  shiftRule (fun _ => c)

-- Conditions on declaration parameters must be established independently of
-- source feasibility, even when the feasible predicate ignores its point.
run_elab do
  let real ← elaborateUnchecked (← `(ℝ))
  withLocalDeclD `coefficient real fun coefficient => do
    let map ← withLocalDeclD `retained real fun r =>
      withLocalDeclD `coordinate real fun u => do
        mkLambdaFVars #[r, u] (← mkAppM ``shift #[coefficient, u])
    let zero ← elaborateUnchecked (← `((0 : ℝ)))
    let condition ← mkAppM ``LT.lt #[zero, coefficient]
    let domain ← elaborateUnchecked (← `(ℝ × ℝ))
    let feasible ← withLocalDeclD `source domain fun source =>
      mkLambdaFVars #[source] condition
    withLocalDeclD `point domain fun point =>
      withLocalDeclD `sourceFeasible (mkApp feasible point) fun evidence => do
        let failed ← try
            discard <| Match.declaration map point (.proj ``Prod 0 point)
              (.proj ``Prod 1 point) evidence ``positiveShift pure
            pure false
          catch _ => pure true
        unless failed do throwError "declaration premise consumed source-feasibility evidence"
    withLocalDeclD `independent condition fun _ =>
      withLocalDeclD `point domain fun point =>
        withLocalDeclD `sourceFeasible (mkApp feasible point) fun evidence => do
          let result ← Match.declaration map point (.proj ``Prod 0 point)
            (.proj ``Prod 1 point) evidence ``positiveShift pure
          checkWithKernel result.rule

private def variableHead (f : ℝ → ℝ → ℝ) (rule : Morew.CoordinateParameterization f) :
    Morew.CoordinateParameterization f := rule

run_elab do
  let .ok implementation := Lean.getAttributeImpl (← getEnv) `morew_substitute
    | throwError "missing parameterization attribute"
  for name in #[``Nat.add, ``variableHead] do
    let saved ← saveState
    let failed ← try
        implementation.add name (← `(attr| morew_substitute)) .local
        pure false
      catch _ => pure true
    saved.restore
    unless failed do throwError "registered malformed parameterization {name}"

end MorewTest.Substitution.Registry
