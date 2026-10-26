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

-- Retaining evidence is not permission to unfold a decision-dependent helper.
def helperSource :=
  problem (x : ℝ)
    minimize x
    subject to
      hidden : let _h : 0 < coefficient x := coefficient_pos x
               Real.log (coefficient x) ≤ 3

/-- error: constraint `hidden` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
reformulation helperTarget : helperSource := by
  nlp

end
end MorewTest.Reformulation.TerminalNLPEvidence
