/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.NLPCustom

/-!
# Scoped evidence across smooth-NLP commands

Proof lets remain in semantic and replay expressions, including after importing
a targeted output. Their evidence stays under its original decision/index scope;
displaying a model does not require printing unused proof terms.
-/

namespace MorewTest.Reformulation.TerminalNLPEvidence

open Morew
open NLPCustom.TargetProofLet
noncomputable section

section Scalar
variable (c : ℝ)

-- This imported targeted output was certified using an otherwise unused proof let.
reformulation imported : (target c) := by
  nlp
example : NLP.Form (imported c) := imported.nlpForm c

reformulation together : (source c) := by
  nlp at graph using weightedGraph c
  nlp
example : GlobalEquivalence (source c) (together c) := together.equivalence c
example : (together.nlpForm c).data.toProblem = together c :=
  (together.nlpForm c).represents

reformulation continued : (together c) := by
  epigraph t
  nlp
example : NLP.Form (continued c) := continued.nlpForm c

def direct :=
  problem (x y : ℝ)
    let first := x ^ 2
    let second := x ^ 2
    minimize (let _h : 0 < coefficient c := coefficient_pos c
              Real.log (coefficient c) * first + second)
    subject to
      graph : let _h : 0 < coefficient c := coefficient_pos c
              y = Real.log (coefficient c) * x

reformulation directTarget : (direct c) := by
  nlp
example : (directTarget.nlpForm c).data.rowCount = 1 := rfl
example (x y : ℝ) : (directTarget c).feasible (x, y) ↔
    y = Real.log (coefficient c) * x := Iff.rfl

/--
info: problem (x y : ℝ)
  let first := x ^ 2
  let second := x ^ 2
  minimize Real.log (coefficient c) * first + second
  subject to
    graph : y = Real.log (coefficient c) * x
-/
#guard_msgs in
#printp directTarget

-- A `have` may depend on an earlier proof let; replay preserves both scopes.
def chained :=
  problem (x : ℝ)
    minimize (let hp := coefficient_pos c
              have _hn : coefficient c ≠ 0 := ne_of_gt hp
              Real.log (coefficient c) * x + x / coefficient c)
    subject to
      bound : let hp := coefficient_pos c
              have _hn : coefficient c ≠ 0 := ne_of_gt hp
              Real.log (coefficient c) * x + x / coefficient c ≤ 1

reformulation chainedTarget : (chained c) := by
  nlp
reformulation chainedAgain : (chainedTarget c) := by
  nlp
example : NLP.Form (chainedAgain c) := chainedAgain.nlpForm c

-- A conjunction's proof scope must survive both splitting and auxiliary insertion.
def grouped :=
  problem (x : ℝ) (v : Fin 1 → ℝ) (t : ℝ)
    minimize x ^ 2
    subject to
      bounds : let _h : 0 < coefficient c := coefficient_pos c
               |Real.log (coefficient c) * x| ≤ t ∧ ‖WithLp.toLp 1 v‖ ≤ t

reformulation groupedTarget : (grouped c) := by
  nlp
example : (groupedTarget.nlpForm c).data.rowCount = 5 := rfl
example : GlobalEquivalence (grouped c) (groupedTarget c) := groupedTarget.equivalence c

reformulation groupedAgain : (groupedTarget c) := by
  nlp
example : NLP.Form (groupedAgain c) := groupedAgain.nlpForm c

-- Structural projections retain the same proof scope as a head let, through
-- direct lowering, selected lowering, and replay of their generated predicates.
def projected :=
  problem (x : ℝ)
    minimize x ^ 2
    subject to
      bound : ((let _h : 0 < coefficient c := coefficient_pos c
                ((|Real.log (coefficient c) * x| ≤ 3, True), True)).1).1

reformulation projectedTarget : (projected c) := by
  nlp
example : (projectedTarget.nlpForm c).data.rowCount = 2 := rfl
example : GlobalEquivalence (projected c) (projectedTarget c) := projectedTarget.equivalence c

reformulation projectedSelected : (projected c) := by
  nlp at bound
reformulation projectedSelectedAgain : (projectedSelected c) := by
  nlp
example : NLP.Form (projectedSelectedAgain c) := projectedSelectedAgain.nlpForm c

-- Projected groups must expose their conjunction before deciding which leaves
-- need lowering; the later norm auxiliary also transports the accepted evidence.
def projectedGroup :=
  problem (x : ℝ) (v : Fin 1 → ℝ) (t : ℝ)
    minimize x ^ 2
    subject to
      bounds : (let _h : 0 < coefficient c := coefficient_pos c
                (|Real.log (coefficient c) * x| ≤ t ∧ ‖WithLp.toLp 1 v‖ ≤ t, True)).1

reformulation projectedGroupTarget : (projectedGroup c) := by
  nlp
example : (projectedGroupTarget.nlpForm c).data.rowCount = 5 := rfl
example : GlobalEquivalence (projectedGroup c) (projectedGroupTarget c) :=
  projectedGroupTarget.equivalence c
reformulation projectedGroupAgain : (projectedGroupTarget c) := by
  nlp
example : NLP.Form (projectedGroupAgain c) := projectedGroupAgain.nlpForm c

-- Explicit exact records may also place their target's evidence beneath a
-- projection; both the selected result and a later terminal command retain it.
def projectedGraph : GraphRepresentation (weighted c) where
  Auxiliary := Unit
  target x y _ :=
    (let _h : 0 < coefficient c := coefficient_pos c
     (y = Real.log (coefficient c) * x, True)).1
  source_iff_exists x y := by simp [weighted]

reformulation projectedGraphTarget : (source c) := by
  nlp at graph using projectedGraph c
reformulation projectedGraphAgain : (projectedGraphTarget c) := by
  nlp
example : NLP.Form (projectedGraphAgain c) := projectedGraphAgain.nlpForm c

private theorem decisionEvidence (_x : ℝ) : 0 < coefficient c := coefficient_pos c

-- An independent proposition is insufficient when its proof depends on a decision.
def dependentEvidence :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : let _h : 0 < coefficient c := decisionEvidence c x
              Real.log (coefficient c) * x ≤ 1

/-- error: constraint `bound` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
reformulation dependentEvidenceTarget : (dependentEvidence c) := by
  nlp

def projectedDependentEvidence :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : (let _h : 0 < coefficient c := decisionEvidence c x
               (|Real.log (coefficient c) * x| ≤ 1, True)).1

/-- error: constraint `bound` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
reformulation projectedDependentEvidenceTarget : (projectedDependentEvidence c) := by
  nlp
end Scalar

section Indexed
variable (n : Nat) (c : Fin n → ℝ)

def indexed :=
  problem (x : Fin n → ℝ)
    minimize ∑ i, (x i) ^ 2
    subject to
      bounds : ∀ i : Fin n,
        let _h : 0 < coefficient (c i) := coefficient_pos (c i)
        x i ≤ Real.log (coefficient (c i))

reformulation indexedTarget : (indexed n c) := by
  nlp
example : (indexedTarget.nlpForm n c).data.rowCount = n := by
  change (∑ _ : Fin n, (1 : Nat)) + 0 = n
  simp
example : NLP.Form (indexedTarget n c) := indexedTarget.nlpForm n c

reformulation indexedAgain : (indexedTarget n c) := by
  nlp
example : NLP.Form (indexedAgain n c) := indexedAgain.nlpForm n c
end Indexed

section IndexScope
variable (c : Fin 2 → ℝ)

-- Evidence for the active index cannot justify a different coordinate.
def unrelatedIndex :=
  problem (x : Fin 2 → ℝ)
    minimize ∑ i, (x i) ^ 2
    subject to
      indexed : ∀ i : Fin 2,
        have _h : 0 < coefficient (c i) := coefficient_pos (c i)
        Real.log (coefficient (c 0)) * x i ≤ 2

/-- error: constraint `indexed` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
reformulation unrelatedIndexTarget : (unrelatedIndex c) := by
  nlp
end IndexScope

-- The helper expands to x² + 1, whose positivity can be proved independently
-- of the decision-dependent proof let. Disabling expansion retains opacity.
def helperSource :=
  problem (x : ℝ)
    minimize x
    subject to
      hidden : let _h : 0 < coefficient x := coefficient_pos x
               Real.log (coefficient x) ≤ 3

/-- error: constraint `hidden` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
set_option morew.smooth.maxExpansionDepth 0 in
reformulation opaqueHelperTarget : helperSource := by
  nlp

reformulation helperTarget : helperSource := by
  nlp

example : GlobalEquivalence helperSource helperTarget := helperTarget.equivalence
example : NLP.Form helperTarget := helperTarget.nlpForm

end
end MorewTest.Reformulation.TerminalNLPEvidence
