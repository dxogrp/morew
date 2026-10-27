/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Rewrite.Registry.Source
import Morew.Elab.Rewrite.Match
import Mathlib.Tactic

/-!
# Scoped registry and structural matching regressions

The imported custom declarations exercise persistence without sharing a head
with built-in rules. Candidate matching is checked independently of either
target's analytic certification policy.
-/

namespace MorewTest.Rewrite.Registry

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Rewrite
open MorewTest.Rewrite.Registry.Source

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let value ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

private def selected (target : Registry.Target) (source : TSyntax `term)
    (expected : Array Name) : TermElabM Unit := do
  let source ← elaborate source
  let actual ← Registry.candidates target source
  unless actual == expected do throwError "unexpected registry candidates {actual}"

run_elab do
  selected .conic (← `(fun p : ℝ × ℝ => p.2 = shifted 3 p.1)) #[``shiftedGraph]
  selected .nlp (← `(fun p : ℝ × ℝ => p.2 = shifted 3 p.1)) #[``shiftedGraph]
  selected .nlp (← `(fun p : ℝ × ℝ => shifted 3 p.1 ≤ p.2)) #[]

section
attribute [local morew_nlp] Scoped.shiftedEpigraph
attribute [local morew_nlp] Scoped.shiftedEpigraph
run_elab do
  selected .nlp (← `(fun p : ℝ × ℝ => shifted 3 p.1 ≤ p.2))
    #[``Scoped.shiftedEpigraph]
  selected .nlp (← `(fun p : ℝ × ℝ => p.2 ≤ shifted 3 p.1)) #[]
end

section
open scoped MorewTest.Rewrite.Registry.Source.Scoped
run_elab do
  selected .nlp (← `(fun p : ℝ × ℝ => shifted 3 p.1 ≤ p.2))
    #[``Scoped.shiftedEpigraph]
end

section
attribute [-morew_nlp] shiftedGraph
run_elab do
  selected .nlp (← `(fun p : ℝ × ℝ => p.2 = shifted 3 p.1)) #[]
  selected .conic (← `(fun p : ℝ × ℝ => p.2 = shifted 3 p.1)) #[``shiftedGraph]
end

run_elab do
  selected .nlp (← `(fun p : ℝ × ℝ => p.2 = shifted 3 p.1)) #[``shiftedGraph]
  selected .nlp (← `(fun p : ℝ × ℝ => shifted 3 p.1 ≤ p.2)) #[]

private def matched (source : TSyntax `term) (name : Name) : TermElabM Unit := do
  let source ← elaborate source
  let domain ← Plan.predicateDomain source
  withLocalDeclD `point domain fun point => do
    let result ← try Match.declaration point (mkApp source point) name pure
      catch error => throwError "matching {name} on {source}: {error.toMessageData}"
    checkWithKernel result.sourceIff
    let expected ← mkAppM ``Exists #[result.target]
    unless ← isDefEq (← inferType result.sourceIff)
        (mkApp2 (mkConst ``Iff) (mkApp source point) expected) do
      throwError "matched certificate changed the selected predicate"

-- Product inputs: reconstructing operands must also accept intact products,
-- including nested values and projections from a larger decision domain.
private noncomputable def pairAbs (p : ℝ × ℝ) : ℝ := |p.1 - p.2|

private noncomputable def pairAbsRule : Morew.EpigraphRepresentation pairAbs where
  Auxiliary := Unit
  target p t _ := p.1 - p.2 ≤ t ∧ -(p.1 - p.2) ≤ t
  source_iff_exists p t := by
    simpa only [pairAbs, exists_const] using
      Morew.Rewrite.Polyhedral.abs_le_iff (p.1 - p.2) t

private noncomputable def nestedPairAbs (p : (ℝ × ℝ) × ℝ) : ℝ :=
  |p.1.1 - p.1.2 + p.2|

private noncomputable def nestedPairAbsRule :
    Morew.EpigraphRepresentation nestedPairAbs where
  Auxiliary := Unit
  target p t _ := p.1.1 - p.1.2 + p.2 ≤ t ∧ -(p.1.1 - p.1.2 + p.2) ≤ t
  source_iff_exists p t := by
    simpa only [nestedPairAbs, exists_const] using
      Morew.Rewrite.Polyhedral.abs_le_iff (p.1.1 - p.1.2 + p.2) t

run_elab do
  matched (← `(fun p : ℝ × ℝ => pairAbs p ≤ 3)) ``pairAbsRule
  matched (← `(fun p : ℝ × ℝ => pairAbs (p.1, p.2) ≤ 3)) ``pairAbsRule
  matched (← `(fun p : (ℝ × ℝ) × ℝ => pairAbs p.1 ≤ p.2)) ``pairAbsRule
  matched (← `(fun p : (ℝ × ℝ) × ℝ => nestedPairAbs p ≤ 3)) ``nestedPairAbsRule

private def nonnegativeValue (x : {x : ℝ // 0 ≤ x}) : ℝ := x.val

private def nonnegativeValueRule : Morew.EpigraphRepresentation nonnegativeValue where
  Auxiliary := Unit
  target x t _ := x.val ≤ t
  source_iff_exists _ _ := by simp only [nonnegativeValue, exists_const]

-- An intact subtype supplies its own property proof; no external evidence
-- callback is needed when reconstructing the representation input.
run_elab do
  matched (← `(fun x : {x : ℝ // 0 ≤ x} => nonnegativeValue x ≤ 3))
    ``nonnegativeValueRule

-- Exact inputs: infer the operand even when its type is the decision type.
private noncomputable def bounded (x : ℝ) : Prop := |x| ≤ 3

private noncomputable def boundedRule : Morew.ExactConstraintLift bounded :=
  .ofIff (fun x => x ≤ 3 ∧ -x ≤ 3)
    (fun x => Morew.Rewrite.Polyhedral.abs_le_iff x 3)

run_elab do
  matched (← `(fun x : ℝ => bounded x)) ``boundedRule
  matched (← `(fun x : ℝ => bounded (x + 1))) ``boundedRule
  matched (← `(fun p : ℝ × ℝ => bounded (p.1 + 1))) ``boundedRule

run_elab do
  matched (← `(fun p : ℝ × ℝ => p.2 = shifted 3 p.1)) ``shiftedGraph
  matched (← `(fun p : ℝ × ℝ => shifted 3 p.1 = p.2)) ``shiftedGraph
  matched (← `(fun p : ℝ × ℝ => shifted 3 p.1 ≤ p.2)) ``Scoped.shiftedEpigraph
  matched (← `(fun p : ℝ × ℝ => p.2 ≥ shifted 3 p.1)) ``Scoped.shiftedEpigraph
  matched (← `(fun p : ℝ × ℝ => shifted p.1 p.2 ≤ 0)) ``Scoped.shiftedEpigraph
  matched (← `(fun p : ℝ × ℝ => shifted p.1 p.2 = 0)) ``shiftedGraph
  matched (← `(fun p : ℝ × ℝ => max p.1 p.2 ≤ 4)) ``Morew.Rewrite.maxEpigraph
  matched (← `(fun p : ℝ × ℝ => 4 ≤ min p.1 p.2)) ``Morew.Rewrite.minHypograph
  matched (← `(fun p : (Fin 0 → ℝ) × ℝ => ‖WithLp.toLp 1 p.1‖ ≤ p.2))
    ``Morew.Rewrite.norm1Epigraph

private noncomputable abbrev nativeLE : LE ℝ := inferInstance

run_elab do
  matched (← `(fun p : ℝ × ℝ => @LE.le ℝ nativeLE (shifted 3 p.1) p.2))
    ``Scoped.shiftedEpigraph

run_elab do
  let type ← elabTerm (← `(LE ℝ)) none
  withLocalDecl `altered .instImplicit type fun inst => do
    withLocalInstances [← inst.fvarId!.getDecl] do
      matched (← `(fun p : ℝ × ℝ => @LE.le ℝ nativeLE (shifted 3 p.1) p.2))
        ``Scoped.shiftedEpigraph

private def empty : Morew.ExactConstraintLift (fun _ : ℝ => True) :=
  .ofIff (fun _ => True) (fun _ => Iff.rfl)

run_elab do
  matched (← `(fun _ : ℝ => True)) ``empty

private def lowerSpelling : Morew.ExactConstraintLift (fun x : ℝ => x * x ≤ 4) :=
  .ofIff (fun x => x * x ≤ 4) (fun _ => Iff.rfl)

private def upperSpelling : Morew.ExactConstraintLift (fun x : ℝ => 4 ≥ x * x) :=
  .ofIff (fun x => x * x ≤ 4) (fun _ => Iff.rfl)

section
attribute [local morew_nlp] lowerSpelling
run_elab do
  selected .nlp (← `(fun x : ℝ => x * x ≤ 4)) #[``lowerSpelling]
  selected .nlp (← `(fun x : ℝ => 4 ≥ x * x)) #[``lowerSpelling]
  matched (← `(fun x : ℝ => 4 ≥ x * x)) ``lowerSpelling
end

section
attribute [local morew_nlp] upperSpelling
run_elab do
  selected .nlp (← `(fun x : ℝ => x * x ≤ 4)) #[``upperSpelling]
  selected .nlp (← `(fun x : ℝ => 4 ≥ x * x)) #[``upperSpelling]
  matched (← `(fun x : ℝ => x * x ≤ 4)) ``upperSpelling
end

private noncomputable def subtypeAbs :
    Morew.EpigraphRepresentation (fun x : { x : ℝ // 0 ≤ x } => |x.val|) where
  Auxiliary := Unit
  target x t _ := x.val ≤ t
  source_iff_exists x t := by simp [abs_of_nonneg x.property]

run_elab do
  let source ← elaborate (← `(fun p : ℝ × ℝ => |p.1| ≤ p.2))
  let domain ← Plan.predicateDomain source
  withLocalDeclD `point domain fun point => do
    let first := Expr.proj ``Prod 0 point
    let zero ← elaborate (← `((0 : ℝ)))
    let condition ← mkAppM ``LE.le #[zero, first]
    withLocalDeclD `retained condition fun retained => do
      let before ← getMCtx
      let rejected ← try
          discard <| Match.declaration point (mkApp source point) ``subtypeAbs pure
          pure false
        catch _ => pure true
      unless rejected do throwError "matching consumed unapproved retained evidence"
      unless before.mvarCounter == (← getMCtx).mvarCounter do
        throwError "failed matching leaked metavariables"
      let matched ← Match.declaration point (mkApp source point) ``subtypeAbs pure fun wanted => do
        if ← isDefEq wanted condition then pure (some retained) else pure none
      unless matched.usedEvidence do throwError "domain evidence was not recorded"
      unless !(matched.target.containsFVar retained.fvarId!) do
        throwError "irrelevant subtype evidence escaped into the target"
      checkWithKernel matched.sourceIff

private def badHead : Morew.GraphRepresentation (fun x : ℝ => x) where
  Auxiliary := Unit
  target x y _ := y = x
  source_iff_exists _ _ := by simp

private noncomputable def pairRule :
    Morew.EpigraphRepresentation (fun p : ℝ × ℝ => let (a, b) := p; max a b) :=
  Morew.Rewrite.maxEpigraph

section
attribute [local morew_nlp] pairRule
run_elab do
  selected .nlp (← `(fun p : ℝ × ℝ => max p.1 p.2 ≤ 3)) #[``pairRule]
  selected .nlp (← `(fun p : ℝ × ℝ => let (a, b) := p; max a b ≤ 3)) #[``pairRule]
  matched (← `(fun p : ℝ × ℝ => max p.1 p.2 ≤ 3)) ``pairRule
  matched (← `(fun p : ℝ × ℝ => let (a, b) := p; max a b ≤ 3)) ``pairRule
end

/-- A universe-polymorphic fixed head for checking actual universe inference. -/
def generic {α : Type u} (x : α) : α := x

def genericGraph {α : Type u} : Morew.GraphRepresentation (@generic α) where
  Auxiliary := Unit
  target x y _ := y = x
  source_iff_exists _ _ := by simp [generic]

section
attribute [local morew_nlp] genericGraph
run_elab do
  matched (← `(fun p : (ULift.{1} ℝ) × ULift.{1} ℝ => p.2 = generic p.1)) ``genericGraph
end

-- Graph orientation retries include the consumer's certification work. Failed
-- proof dependencies are discarded before retry, while accepted ones survive.
private def graphRetry (source expected : TSyntax `term) (name : Name) : TermElabM Unit := do
  let source ← elaborate source
  let expected ← elaborate expected
  let domain ← Plan.predicateDomain source
  let attempts ← IO.mkRef 0
  let discarded ← IO.mkRef (none : Option Name)
  let accepted ← IO.mkRef (none : Option Name)
  let before ← getMCtx
  withLocalDeclD `point domain fun point => do
    let result : Match.Result ← Match.declaration point (mkApp source point) name fun result => do
      let attempt ← attempts.get
      attempts.modify (· + 1)
      if attempt == 0 then
        let scratch ← mkFreshExprMVar (mkConst ``Nat)
        scratch.mvarId!.assign (mkNatLit 1)
        let proof ← mkEqRefl (mkNatLit 0)
        let name ← mkAuxLemma [] (← inferType proof) proof
          (kind? := some `discardedGraphOrientation) (cache := false)
        discarded.set (some name)
        throwError "reject the first graph orientation after allocating proof state"
      let some discardedName ← discarded.get
        | throwError "graph regression did not exercise the rejected orientation"
      if (← getEnv).contains discardedName then
        throwError "graph retry retained a discarded auxiliary declaration"
      let proof ← mkLambdaFVars #[point] result.sourceIff
      let name ← mkAuxLemma [] (← inferType proof) proof
        (kind? := some `acceptedGraphOrientation) (cache := false)
      accepted.set (some name)
      return { result with sourceIff := mkApp (mkConst name) point }
    unless before.mvarCounter == (← getMCtx).mvarCounter &&
        before.lmvarCounter == (← getMCtx).lmvarCounter do
      throwError "graph retry leaked scratch metavariables"
    unless ← isDefEq result.target (mkApp expected point) do
      throwError "graph retry did not use the accepted reverse orientation"
    let existsTarget ← mkAppM ``Exists #[result.target]
    unless ← isDefEq (← inferType result.sourceIff)
        (mkApp2 (mkConst ``Iff) (mkApp source point) existsTarget) do
      throwError "graph retry changed the selected source predicate"
    checkWithKernel result.sourceIff
  unless (← attempts.get) == 2 do
    throwError "graph regression did not check both orientations exactly once"
  let some discardedName ← discarded.get | throwError "missing rejected graph attempt"
  let some acceptedName ← accepted.get | throwError "missing accepted graph attempt"
  if (← getEnv).contains discardedName then
    throwError "graph retry leaked the rejected proof dependency"
  unless (← getEnv).contains acceptedName do
    throwError "graph retry dropped the accepted proof dependency"

run_elab do
  graphRetry (← `(fun x : ℝ => shifted 3 x = shifted 3 2))
    (← `(fun x : ℝ => fun _ : Unit => shifted 3 2 = x + 3)) ``shiftedGraph
  graphRetry (← `(fun x : ULift.{1} ℝ => generic x = generic (ULift.up (2 : ℝ))))
    (← `(fun x : ULift.{1} ℝ => fun _ : Unit => generic (ULift.up (2 : ℝ)) = x))
    ``genericGraph

run_elab do
  let .ok attributeImpl := Lean.getAttributeImpl (← getEnv) `morew_nlp
    | throwError "missing exact-rule attribute"
  for name in #[``Nat.add, ``badHead] do
    let saved ← saveState
    let rejected ← try
        attributeImpl.add name (← `(attr| morew_nlp)) .local
        pure false
      catch _ => pure true
    saved.restore
    unless rejected do throwError "malformed representation accepted: {name}"

end MorewTest.Rewrite.Registry
