/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Cone.Rewrite
import MorewTest.ElabSupport
import MorewTest.Rewrite.Registry.Source
import MorewTest.Environment

/-!
# Registered conic records and retained-domain boundaries

Built-in removal affects automatic selection, while explicit selection remains
available. User subtype-domain records exercise the same checked retained-margin
policy as native logarithm and quotient rules.
-/

namespace MorewTest.Conic.Registry

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Elab.Cone MorewTest.Affine

private def check (term : TSyntax `term) (rows : Nat) (retained : Array Expr := #[])
    (name? : Option Name := none) (expected : Array (TSyntax `term) := #[])
    (rule? : Option Expr := none) :
    TermElabM Unit := do
  let source ← elaborate term
  let before ← getMCtx
  let result ← match rule? with
    | some rule => Morew.Elab.Cone.Rewrite.planExplicit source rule retained
    | none => match name? with
      | some name => Morew.Elab.Cone.Rewrite.planDeclaration source name retained
      | none => Morew.Elab.Cone.Rewrite.planUnique source retained
  let result ← match result with
    | .ok result => pure result
    | .error error => throwError "registered conic rule failed: {error.reason}"
  assertMVarCountersUnchanged before "registered conic planning leaked scratch metavariables"
  result.toResult.check source retained
  let predicates := result.rowPredicates
  let certificates := result.certifiedRows
  unless predicates.size == rows && certificates.size == rows do
    throwError "wrong number of certified registered rows"
  unless expected.isEmpty do
    unless predicates.size == expected.size do
      throwError "wrong number of expected registered rows"
    for actual in predicates, expected in expected do
      unless ← isDefEq actual (← elaborate expected) do
        throwError "registered conic row changed its expression or position: {actual}"
  checkWithKernel result.certificate.expression
  for row in certificates do
    checkWithKernel row.constraint
    checkWithKernel row.pointwiseIff

private def reject (term : TSyntax `term) (fragment : String)
    (retained : Array Expr := #[]) (name? : Option Name := none)
    (rule? : Option Expr := none) : TermElabM Unit := do
  let source ← elaborate term
  let before ← getMCtx
  let environment ← getEnv
  let result ← match rule? with
    | some rule => Morew.Elab.Cone.Rewrite.planExplicit source rule retained
    | none => match name? with
      | some name => Morew.Elab.Cone.Rewrite.planDeclaration source name retained
      | none => Morew.Elab.Cone.Rewrite.planUnique source retained
  let .error error := result | throwError "unsupported registered conic rule was accepted"
  unless (← error.reason.toString).contains fragment do
    throwError "unexpected registered conic failure: {error.reason}"
  assertMVarCountersUnchanged before "failed registration use leaked scratch metavariables"
  if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
    throwError "failed registration use leaked {name}"

section
attribute [-morew_conic] Morew.Conic.Exponential.expEpigraph

run_cmd liftTermElabM do
  reject (← `(fun p : ℝ × ℝ => Real.exp p.1 ≤ p.2)) "no supported registered"
  check (← `(fun p : ℝ × ℝ => Real.exp p.1 ≤ p.2)) 1 #[]
    (some ``Morew.Conic.Exponential.expEpigraph)
end

run_cmd liftTermElabM do
  check (← `(fun p : ℝ × ℝ => Real.exp p.1 ≤ p.2)) 1

-- Source matching preserves the structural forms accepted by the conic
-- consumer, while certificates still refer to the unreduced predicate.
run_cmd liftTermElabM do
  check (← `(fun p : ℝ × ℝ => let (x, t) := p; Real.exp x ≤ t)) 1
  check (← `((Morew.Problem.mk (fun p : ℝ × ℝ => p.2)
    (fun p : ℝ × ℝ => Real.exp p.1 ≤ p.2)).feasible)) 1

-- Product inputs: intact values, projections, and nested products match the
-- same checked representation without requiring source-level eta expansion.
noncomputable def pairAbs (p : ℝ × ℝ) : ℝ := |p.1 - p.2|

@[morew_conic]
noncomputable def pairAbsRule : EpigraphRepr pairAbs where
  Auxiliary := Unit
  target p t _ := p.1 - p.2 ≤ t ∧ -(p.1 - p.2) ≤ t
  source_iff_exists p t := by
    simpa only [pairAbs, exists_const] using abs_le' (a := p.1 - p.2) (b := t)

noncomputable def nestedPairAbs (p : (ℝ × ℝ) × ℝ) : ℝ := |p.1.1 - p.1.2 + p.2|

@[morew_conic]
noncomputable def nestedPairAbsRule : EpigraphRepr nestedPairAbs where
  Auxiliary := Unit
  target p t _ := p.1.1 - p.1.2 + p.2 ≤ t ∧ -(p.1.1 - p.1.2 + p.2) ≤ t
  source_iff_exists p t := by
    simpa only [nestedPairAbs, exists_const] using
      abs_le' (a := p.1.1 - p.1.2 + p.2) (b := t)

run_cmd liftTermElabM do
  let pairRows := #[← `(fun p : ℝ × ℝ => p.1 - p.2 ≤ 3),
    ← `(fun p : ℝ × ℝ => -(p.1 - p.2) ≤ 3)]
  check (← `(fun p : ℝ × ℝ => pairAbs p ≤ 3)) 2 (expected := pairRows)
  check (← `(fun p : ℝ × ℝ => pairAbs (p.1, p.2) ≤ 3)) 2 (expected := pairRows)
  check (← `(fun p : (ℝ × ℝ) × ℝ => pairAbs p.1 ≤ p.2)) 2
    (expected := #[← `(fun p : (ℝ × ℝ) × ℝ => p.1.1 - p.1.2 ≤ p.2),
      ← `(fun p : (ℝ × ℝ) × ℝ => -(p.1.1 - p.1.2) ≤ p.2)])
  check (← `(fun p : (ℝ × ℝ) × ℝ => nestedPairAbs p ≤ 3)) 2
    (expected := #[← `(fun p : (ℝ × ℝ) × ℝ => p.1.1 - p.1.2 + p.2 ≤ 3),
      ← `(fun p : (ℝ × ℝ) × ℝ => -(p.1.1 - p.1.2 + p.2) ≤ 3)])

-- Exact inputs: composition does not depend on whether the operand and the
-- optimization variable have the same type.
noncomputable def bounded (x : ℝ) : Prop := |x| ≤ 3

@[morew_conic]
noncomputable def boundedRule : ConstraintRepr bounded :=
  .ofIff (fun x => x ≤ 3 ∧ -x ≤ 3) (fun x => abs_le' (a := x) (b := 3))

run_cmd liftTermElabM do
  check (← `(fun x : ℝ => bounded x)) 2
    (expected := #[← `(fun x : ℝ => x ≤ 3), ← `(fun x : ℝ => -x ≤ 3)])
  check (← `(fun x : ℝ => bounded (x + 1))) 2
    (expected := #[← `(fun x : ℝ => x + 1 ≤ 3), ← `(fun x : ℝ => -(x + 1) ≤ 3)])
  check (← `(fun p : ℝ × ℝ => bounded (p.1 + 1))) 2
    (expected := #[← `(fun p : ℝ × ℝ => p.1 + 1 ≤ 3),
      ← `(fun p : ℝ × ℝ => -(p.1 + 1) ≤ 3)])

-- Concrete exact representations certify the entire source. A named declaration
-- may infer an input map; a concrete record retains its decision space.
run_cmd liftTermElabM do
  let concreteRule ← elaborate (← `(boundedRule))
  check (← `(fun x : ℝ => bounded x)) 2
    (expected := #[← `(fun x : ℝ => x ≤ 3), ← `(fun x : ℝ => -x ≤ 3)])
    (rule? := some concreteRule)
  check (← `(fun x : ℝ => bounded (x + 1))) 2 (name? := some ``boundedRule)
    (expected := #[← `(fun x : ℝ => x + 1 ≤ 3), ← `(fun x : ℝ => -(x + 1) ≤ 3)])
  reject (← `(fun x : ℝ => bounded (x + 1))) "does not match"
    (rule? := some concreteRule)
  reject (← `(fun p : ℝ × ℝ => bounded (p.1 + 1)))
    "constraint representation's input type does not match the decision type" (rule? := some concreteRule)

section QuantifiedHelperOpacity

private noncomputable def hiddenAbs (x : ℝ) : ℝ := |x|

private noncomputable def quantifiedAbsRule :
    ConstraintRepr (fun x : ℝ => (∀ _ : Fin 1, |x| ≤ 3) ∧ True) :=
  .ofIff (fun x => x ≤ 3 ∧ -x ≤ 3) (by
    intro x
    simpa only [forall_const, and_true] using abs_le' (a := x) (b := 3))

attribute [local morew_conic] quantifiedAbsRule

-- Both sources have the same registered conjunction head. Matching beneath a
-- quantifier must preserve helper opacity instead of unfolding by definitional equality.
run_cmd liftTermElabM do
  check (← `(fun x : ℝ => (∀ _ : Fin 1, |x| ≤ 3) ∧ True)) 2
    (expected := #[← `(fun x : ℝ => x ≤ 3), ← `(fun x : ℝ => -x ≤ 3)])
  reject (← `(fun x : ℝ => (∀ _ : Fin 1, hiddenAbs x ≤ 3) ∧ True)) "does not match"

end QuantifiedHelperOpacity

section StructuralHelperOpacity

open MorewTest.Rewrite.Registry.Source.HelperOpacity

attribute [local morew_conic] projectedAbsRule appliedAbsRule implicationAbsRule

run_cmd liftTermElabM do
  let expected := #[← `(fun x : ℝ => x ≤ 3), ← `(fun x : ℝ => -x ≤ 3)]
  check (← `(fun x : ℝ => (projectedAbs x).1 ≤ 3)) 2 (expected := expected)
  reject (← `(fun x : ℝ => (hiddenProjectedAbs x).1 ≤ 3)) "does not match"
  check (← `(fun x : ℝ => applyFunction namedAbs x ≤ 3)) 2 (expected := expected)
  check (← `(fun x : ℝ => applyFunction (fun y => namedAbs y) x ≤ 3)) 2
    (expected := expected)
  reject (← `(fun x : ℝ => applyFunction aliasAbs x ≤ 3)) "does not match"
  check (← `(fun x : ℝ => (|x| ≤ 3 → |x| ≤ 3) ∧ x ≤ 3)) 1
    (expected := #[← `(fun x : ℝ => x ≤ 3)])
  reject (← `(fun x : ℝ => (namedAbs x ≤ 3 → |x| ≤ 3) ∧ x ≤ 3)) "does not match"

end StructuralHelperOpacity

private noncomputable def nonnegAbs (x : ℝ) : ℝ := |x|

private noncomputable def nonnegAbsGraph :
    GraphRepr (fun x : {x : ℝ // 0 ≤ x} => nonnegAbs x.val) where
  Auxiliary := ℝ
  target x y u := u = x.val ∧ y = u
  source_iff_exists x y := by simp [nonnegAbs, abs_of_nonneg x.property]

private noncomputable def nonnegAbsEpigraph :
    EpigraphRepr (fun x : {x : ℝ // 0 ≤ x} => nonnegAbs x.val) where
  Auxiliary := ℝ
  target x t u := u = x.val ∧ u ≤ t
  source_iff_exists x t := by simp [nonnegAbs, abs_of_nonneg x.property]

section
attribute [local morew_conic] nonnegAbsGraph nonnegAbsEpigraph

run_cmd liftTermElabM do
  let margin ← elaborate (← `(fun p : ℝ × ℝ => 0 ≤ p.1))
  let expected := #[← `(fun p : (ℝ × ℝ) × ℝ => p.2 = p.1.1),
    ← `(fun p : (ℝ × ℝ) × ℝ => p.1.2 = p.2)]
  check (← `(fun p : ℝ × ℝ => p.2 = nonnegAbs p.1)) 2 #[margin]
    (expected := expected)
  check (← `(fun p : ℝ × ℝ => nonnegAbs p.1 = p.2)) 2 #[margin]
    (some ``nonnegAbsGraph) (expected := expected)
  reject (← `(fun p : ℝ × ℝ => p.2 = nonnegAbs p.1))
    "nonnegative constant margin" #[] (some ``nonnegAbsGraph)
  check (← `(fun p : ℝ × ℝ => nonnegAbs p.1 ≤ p.2)) 2 #[margin]
    (expected := #[expected[0]!, ← `(fun p : (ℝ × ℝ) × ℝ => p.2 ≤ p.1.2)])
  reject (← `(fun p : ℝ × ℝ => nonnegAbs p.1 ≤ p.2))
    "nonnegative constant margin" #[] (some ``nonnegAbsEpigraph)
end

noncomputable def positiveLog (x : ℝ) : ℝ := Real.log x

/-- Domain restriction is checked through a subtype, with no trusted metadata. -/
noncomputable def positiveLogRule :
    HypographRepr (fun x : {x : ℝ // 0 < x} => positiveLog x.1) :=
  Conic.Exponential.logHypograph

run_cmd liftTermElabM do
  reject (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1)) "no supported registered"

attribute [morew_conic] positiveLogRule

run_cmd liftTermElabM do
  let margin ← elaborate (← `(fun p : ℝ × ℝ => 1 ≤ p.1))
  check (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1)) 1 #[margin]
  reject (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1)) "positive constant margin"
  check (← `(fun t : ℝ => t ≤ positiveLog 2)) 1

/-- Retained subtype evidence supports a uniform nontrivial auxiliary. -/
noncomputable def positiveLogWithAuxiliary :
    HypographRepr (fun x : {x : ℝ // 0 < x} => positiveLog x.1) where
  Auxiliary := ℝ
  target x t u := (t, 1, x.1) ∈ EXP ∧ u = 0
  source_iff_exists x t := by
    change t ≤ Real.log x.1 ↔ _
    rw [Conic.Exponential.le_log_iff x.1 t x.2]
    exact ⟨fun h => ⟨0, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

run_cmd liftTermElabM do
  let margin ← elaborate (← `(fun p : ℝ × ℝ => 1 ≤ p.1))
  check (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1)) 2 #[margin]
    (some ``positiveLogWithAuxiliary)
  reject (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1))
    "positive constant margin" #[] (some ``positiveLogWithAuxiliary)
  check (← `(fun t : ℝ => t ≤ positiveLog 2)) 2 #[]
    (some ``positiveLogWithAuxiliary)

private def hiddenPositive (c : ℝ) : Prop := 0 < c

-- A retained row about parameters still belongs to the controlled row policy;
-- it cannot become an independent local hypothesis merely by ignoring `x`.
run_cmd liftTermElabM do
  for row in #[← `(fun c : ℝ => fun _x : ℝ => 0 < c),
      ← `(fun c : ℝ => fun _x : ℝ => hiddenPositive c)] do
    let term ← elaborate (← `(fun c : ℝ => fun x : ℝ => x ≤ positiveLog c))
    let row ← elaborate row
    lambdaBoundedTelescope term 1 fun parameters source => do
      let before ← getMCtx
      let environment ← getEnv
      let retained := #[mkApp row parameters[0]!]
      let .error error ← Morew.Elab.Cone.Rewrite.planDeclaration source
          ``positiveLogWithAuxiliary retained
        | throwError "parameter-only retained rows bypassed the checked margin policy"
      unless (← error.reason.toString).contains "positive constant margin" do
        throwError "unexpected parameter-only margin diagnostic: {error.reason}"
      unless before.mvarCounter == (← getMCtx).mvarCounter do
        throwError "rejected parameter-only margin leaked metavariables"
      if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
        throwError "rejected parameter-only margin leaked declaration {name}"
  let term ← elaborate (← `(fun (c : ℝ) (_h : 0 < c) =>
    fun x : ℝ => x ≤ positiveLog c))
  lambdaBoundedTelescope term 2 fun _ source => do
    let .ok result ← Morew.Elab.Cone.Rewrite.planDeclaration source
        ``positiveLogWithAuxiliary
      | throwError "an independent parameter hypothesis was rejected"
    let .exact _ := result.certificate
      | throwError "an independent parameter hypothesis retained a row context"
    result.toResult.check source #[]

/-- Target-local proof lets must remain available to the affine consumer. -/
noncomputable def quotientWithProofLet (c : ℝ) (h : c = 1) :
    EpigraphRepr (fun x : ℝ => x / c) where
  Auxiliary := Unit
  target x t _ :=
    let _nonzero : c ≠ 0 := by simpa only [h] using (one_ne_zero : (1 : ℝ) ≠ 0)
    x / c ≤ t
  source_iff_exists _ _ := by simp only [exists_const]

run_cmd liftTermElabM do
  let term ← elaborate (← `(fun (c : ℝ) (_ : c = 1) => fun x : ℝ => x / c ≤ 1))
  lambdaBoundedTelescope term 2 fun _ source => do
    match ← Morew.Elab.Cone.Rewrite.planDeclaration source ``quotientWithProofLet with
    | .error error => throwError "target-local nonzero evidence was lost: {error.reason}"
    | .ok result =>
      let .exact repr := result.certificate
        | throwError "independent target proof unexpectedly used retained rows"
      checkWithKernel repr
      for row in result.certifiedRows do checkWithKernel row.pointwiseIff

noncomputable def positiveShift (c x : ℝ) : ℝ := Real.log c + x

/-- Scalar proof parameters use the same retained-margin policy as subtype inputs. -/
@[morew_conic]
noncomputable def positiveShiftRule (c : ℝ) (hc : 0 < c) :
    HypographRepr (positiveShift c) where
  Auxiliary := Unit
  target x t _ := (t - x, 1, c) ∈ EXP
  source_iff_exists x t := by
    simpa only [exists_const, positiveShift, sub_le_iff_le_add] using
      Conic.Exponential.le_log_iff c (t - x) hc

/-- Declaration proof parameters use the same contextual auxiliary support. -/
noncomputable def positiveShiftAuxiliary (c : ℝ) (hc : 0 < c) :
    HypographRepr (positiveShift c) where
  Auxiliary := ℝ
  target x t u := (t - x, 1, c) ∈ EXP ∧ u = 0
  source_iff_exists x t := by
    change t ≤ Real.log c + x ↔ _
    rw [← sub_le_iff_le_add, Conic.Exponential.le_log_iff c (t - x) hc]
    exact ⟨fun h => ⟨0, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

run_cmd liftTermElabM do
  let margin ← elaborate (← `(fun p : ℝ × ℝ × ℝ => 1 ≤ p.1))
  check (← `(fun p : ℝ × ℝ × ℝ => p.2.2 ≤ positiveShift p.1 p.2.1)) 1 #[margin]
  reject (← `(fun p : ℝ × ℝ × ℝ => p.2.2 ≤ positiveShift p.1 p.2.1))
    "positive constant margin"
  check (← `(fun p : ℝ × ℝ × ℝ => p.2.2 ≤ positiveShift p.1 p.2.1)) 2 #[margin]
    (some ``positiveShiftAuxiliary)
  reject (← `(fun p : ℝ × ℝ × ℝ => p.2.2 ≤ positiveShift p.1 p.2.1))
    "positive constant margin" #[] (some ``positiveShiftAuxiliary)
  check (← `(fun p : ℝ × ℝ => p.2 ≤ positiveShift 2 p.1)) 2 #[]
    (some ``positiveShiftAuxiliary)

-- Graph certification preserves both equation orientations, including cases
-- where either side can match the registered function head.
noncomputable def graphShift (x : ℝ) : ℝ := x + 1

@[morew_conic]
noncomputable def graphShiftRule : GraphRepr graphShift where
  Auxiliary := Unit
  target x y _ := y = x + 1
  source_iff_exists _ _ := by simp only [graphShift, exists_const]

run_cmd liftTermElabM do
  let ordinaryRows := #[← `(fun p : ℝ × ℝ => p.2 = p.1 + 1)]
  check (← `(fun p : ℝ × ℝ => p.2 = graphShift p.1)) 1 (expected := ordinaryRows)
  check (← `(fun p : ℝ × ℝ => graphShift p.1 = p.2)) 1 (expected := ordinaryRows)
  check (← `(fun x : ℝ => graphShift x = graphShift 3)) 1
    (expected := #[← `(fun x : ℝ => graphShift x = 3 + 1)])
  check (← `(fun x : ℝ => graphShift 3 = graphShift x)) 1
    (expected := #[← `(fun x : ℝ => graphShift 3 = x + 1)])

end MorewTest.Conic.Registry
