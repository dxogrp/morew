/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Rewrite
import MorewTest.NLP.DomainSupport

/-!
# Registered NLP rules

Declarations from user namespaces enter the same exactness and generated-domain
checks as built-ins. Scoped activation, explicit selection, and removal exercise
observable planning behavior rather than registry implementation details.
-/

namespace MorewTest.NLP.Registry

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew

private def input {X : Type} (source : X → Prop) (retained : Array (X → Prop)) :=
  (source, retained)

private def check (term : TSyntax `term) (rows : Nat)
    (declaration? : Option Name := none) (parameters : Nat := 0) : TermElabM Unit :=
  Domain.withInput term parameters fun source retained => do
    let before ← getMCtx
    let result ← match ← Morew.Elab.NLP.Rewrite.plan source retained
        (declaration? := declaration?) with
      | .ok result => pure result
      | .error error => throwError "registered NLP plan failed: {error.reason}"
    unless result.rowPredicates.size == rows do
      throwError "registered NLP plan has the wrong replacement shape"
    discard <| Morew.Elab.Rewrite.Plan.checkLift source result.lift
    for proof in #[result.lift, result.targetIff, result.certified.domainIsOpen,
        result.certified.feasibleMemDomain] ++ result.certified.rowCertificates do
      if proof.hasMVar || proof.hasSorry then throwError "incomplete registered NLP evidence"
      checkWithKernel proof
    unless before.mvarCounter == (← getMCtx).mvarCounter &&
        before.lmvarCounter == (← getMCtx).lmvarCounter do
      throwError "registered NLP planning leaked scratch metavariables"

private def exactRows (term : TSyntax `term) (parameters : Nat := 0)
    (rule? : Option Expr := none) (declaration? : Option Name := none) : TermElabM Unit :=
  Domain.withInput term parameters fun source expected => do
    let before ← getMCtx
    let environment ← getEnv
    let result ← match ← Morew.Elab.NLP.Rewrite.plan source #[]
        (rule? := rule?) (declaration? := declaration?) with
      | .ok result => pure result
      | .error error => throwError "registered NLP rows failed: {error.reason}"
    unless before.mvarCounter == (← getMCtx).mvarCounter &&
        before.lmvarCounter == (← getMCtx).lmvarCounter do
      throwError "registered NLP planning leaked scratch metavariables"
    for (name, _) in (← getEnv).constants.toList do
      unless environment.contains name do
        throwError "registered NLP planning leaked declaration {name}"
    unless result.rowPredicates.size == expected.size do
      throwError "registered NLP row count changed"
    for actual in result.rowPredicates, expected in expected do
      unless ← isDefEq actual expected do
        throwError "registered NLP row changed its expression or position: {actual}"
    discard <| Morew.Elab.Rewrite.Plan.checkLift source result.lift
    for proof in #[result.lift, result.targetIff, result.certified.domainIsOpen,
        result.certified.feasibleMemDomain] ++ result.certified.rowCertificates do
      if proof.hasMVar || proof.hasSorry then throwError "incomplete registered NLP evidence"
      checkWithKernel proof

private def reject (term : TSyntax `term) (message : String)
    (declaration? : Option Name := none) (parameters : Nat := 0)
    (rule? : Option Expr := none) : TermElabM Unit :=
  Domain.withInput term parameters fun source retained => do
    let before ← getMCtx
    let environment ← getEnv
    let .error error ← Morew.Elab.NLP.Rewrite.plan source retained
        (declaration? := declaration?) (rule? := rule?)
      | throwError "invalid registered NLP plan was accepted"
    unless (← error.reason.toString).contains message do
      throwError "wrong registered NLP diagnostic: {error.reason}"
    unless before.mvarCounter == (← getMCtx).mvarCounter &&
        before.lmvarCounter == (← getMCtx).lmvarCounter do
      throwError "failed registered NLP planning leaked scratch metavariables"
    for (name, _) in (← getEnv).constants.toList do
      unless environment.contains name do
        throwError "failed registered NLP planning leaked declaration {name}"

noncomputable def userAbs (x : ℝ) : ℝ := |x|

noncomputable def userAbsRule : EpigraphRepresentation userAbs := Rewrite.absEpigraph

-- A namespace and a suitable type alone do not activate a rule. Explicit names
-- may select an unregistered record, and inference is performed at its use site.
run_cmd liftTermElabM do
  reject (← `(input (fun x : ℝ => userAbs x ≤ 3) #[])) "no supported exact NLP rule"
  check (← `(input (fun x : ℝ => userAbs x ≤ 3) #[])) 2 (some ``userAbsRule)

attribute [morew_nlp] userAbsRule
attribute [morew_nlp] userAbsRule

run_cmd liftTermElabM do
  check (← `(input (fun x : ℝ => userAbs (x * x) ≤ 3) #[])) 2
  reject (← `(input (fun x : ℝ => userAbs (Real.log x) ≤ 3) #[])) "domain"
  check (← `(input (fun x : ℝ => userAbs (Real.log x) ≤ 3)
    #[(fun x : ℝ => 1 ≤ x)])) 2

noncomputable def alternateUserAbsRule : EpigraphRepresentation userAbs := userAbsRule

section
attribute [local morew_nlp] alternateUserAbsRule

run_cmd liftTermElabM do
  reject (← `(input (fun x : ℝ => userAbs x ≤ 3) #[]))
    "ambiguous exact NLP rules: MorewTest.NLP.Registry.alternateUserAbsRule, MorewTest.NLP.Registry.userAbsRule"
  check (← `(input (fun x : ℝ => userAbs x ≤ 3) #[])) 2 (some ``userAbsRule)
  check (← `(input (fun x : ℝ => userAbs x ≤ 3) #[])) 2 (some ``alternateUserAbsRule)
end

run_cmd liftTermElabM do
  check (← `(input (fun x : ℝ => userAbs x ≤ 3) #[])) 2

section
attribute [-morew_nlp] Morew.Rewrite.absEpigraph

run_cmd liftTermElabM do
  reject (← `(input (fun x : ℝ => |x| ≤ 3) #[])) "no supported exact NLP rule"
  check (← `(input (fun x : ℝ => |x| ≤ 3) #[])) 2 (some ``Morew.Rewrite.absEpigraph)
  check (← `(input (fun x : ℝ => userAbs x ≤ 3) #[])) 2
end

run_cmd liftTermElabM do
  check (← `(input (fun x : ℝ => |x| ≤ 3) #[])) 2

noncomputable def shiftedAbs (c x : ℝ) : ℝ := |x - c|

noncomputable def shiftedRule (c : ℝ) : EpigraphRepresentation (shiftedAbs c) where
  Auxiliary := Unit
  target x t _ := x - c ≤ t ∧ -(x - c) ≤ t
  source_iff_exists x t := by
    simpa only [shiftedAbs, exists_const] using Rewrite.Polyhedral.abs_le_iff (x - c) t

run_cmd liftTermElabM do
  check (← `(fun c : ℝ => input (fun x : ℝ => shiftedAbs c x ≤ 3) #[])) 2
    (some ``shiftedRule) 1

noncomputable def guardedShiftedRule (c : ℝ) (_hc : 0 < c) :
    EpigraphRepresentation (shiftedAbs c) := shiftedRule c

-- Declaration premises may use independent local hypotheses. Retained rows
-- remain available only for generated smoothness/domain certification, never
-- for establishing the unconditional exact replacement on the NLP path.
run_cmd liftTermElabM do
  check (← `(fun (c : ℝ) (_hc : 0 < c) =>
    input (fun x : ℝ => shiftedAbs c x ≤ 3) #[])) 2
    (some ``guardedShiftedRule) 2
  reject (← `(fun c : ℝ => input (fun x : ℝ => shiftedAbs c x ≤ 3)
    #[(fun _ : ℝ => 1 ≤ c)])) "missing domain evidence"
    (some ``guardedShiftedRule) 1

attribute [morew_nlp] shiftedRule

run_cmd liftTermElabM do
  check (← `(fun c : ℝ => input (fun x : ℝ => shiftedAbs c (x * x) ≤ 3) #[]))
    2 none 1

-- Product inputs must match intact values, their eta expansions, and nested
-- projections without changing the selected predicate checked by the lift.
noncomputable def pairAbs (p : ℝ × ℝ) : ℝ := |p.1 - p.2|

@[morew_nlp] noncomputable def pairAbsRule : EpigraphRepresentation pairAbs where
  Auxiliary := Unit
  target p t _ := p.1 - p.2 ≤ t ∧ -(p.1 - p.2) ≤ t
  source_iff_exists p t := by
    simpa only [pairAbs, exists_const] using Rewrite.Polyhedral.abs_le_iff (p.1 - p.2) t

run_cmd liftTermElabM do
  exactRows (← `(input (fun p : ℝ × ℝ => pairAbs p ≤ 3)
    #[(fun p : ℝ × ℝ => p.1 - p.2 ≤ 3),
      (fun p : ℝ × ℝ => -(p.1 - p.2) ≤ 3)]))
  exactRows (← `(input (fun p : ℝ × ℝ => pairAbs (p.1, p.2) ≤ 3)
    #[(fun p : ℝ × ℝ => p.1 - p.2 ≤ 3),
      (fun p : ℝ × ℝ => -(p.1 - p.2) ≤ 3)]))
  exactRows (← `(input (fun p : (ℝ × ℝ) × ℝ => pairAbs p.1 ≤ p.2)
    #[(fun p : (ℝ × ℝ) × ℝ => p.1.1 - p.1.2 ≤ p.2),
      (fun p : (ℝ × ℝ) × ℝ => -(p.1.1 - p.1.2) ≤ p.2)]))

noncomputable def nestedPairAbs (p : (ℝ × ℝ) × ℝ) : ℝ := |p.1.1 - p.1.2 + p.2|

@[morew_nlp] noncomputable def nestedPairAbsRule : EpigraphRepresentation nestedPairAbs where
  Auxiliary := Unit
  target p t _ := p.1.1 - p.1.2 + p.2 ≤ t ∧ -(p.1.1 - p.1.2 + p.2) ≤ t
  source_iff_exists p t := by
    simpa only [nestedPairAbs, exists_const] using
      Rewrite.Polyhedral.abs_le_iff (p.1.1 - p.1.2 + p.2) t

run_cmd liftTermElabM do
  exactRows (← `(input (fun p : (ℝ × ℝ) × ℝ => nestedPairAbs p ≤ 3)
    #[(fun p : (ℝ × ℝ) × ℝ => p.1.1 - p.1.2 + p.2 ≤ 3),
      (fun p : (ℝ × ℝ) × ℝ => -(p.1.1 - p.1.2 + p.2) ≤ 3)]))

-- Exact predicates infer their input map even when the rule's input type and
-- the current decision space coincide.
noncomputable def bounded (x : ℝ) : Prop := |x| ≤ 3

@[morew_nlp] noncomputable def boundedRule : ExactConstraintLift bounded :=
  .ofIff (fun x => x ≤ 3 ∧ -x ≤ 3)
    (fun x => Rewrite.Polyhedral.abs_le_iff x 3)

run_cmd liftTermElabM do
  exactRows (← `(input (fun x : ℝ => bounded x)
    #[(fun x : ℝ => x ≤ 3), (fun x : ℝ => -x ≤ 3)]))
  exactRows (← `(input (fun x : ℝ => bounded (x + 1))
    #[(fun x : ℝ => x + 1 ≤ 3), (fun x : ℝ => -(x + 1) ≤ 3)]))
  exactRows (← `(input (fun p : ℝ × ℝ => bounded (p.1 + 1))
    #[(fun p : ℝ × ℝ => p.1 + 1 ≤ 3),
      (fun p : ℝ × ℝ => -(p.1 + 1) ≤ 3)]))

-- Concrete exact lifts certify their entire source; named declarations infer
-- an input map, but concrete records retain the original full-source check.
run_cmd liftTermElabM do
  let concreteRule ← Domain.elaborate (← `(boundedRule))
  exactRows (← `(input (fun x : ℝ => bounded x)
    #[(fun x : ℝ => x ≤ 3), (fun x : ℝ => -x ≤ 3)])) (rule? := some concreteRule)
  exactRows (← `(input (fun x : ℝ => bounded (x + 1))
    #[(fun x : ℝ => x + 1 ≤ 3), (fun x : ℝ => -(x + 1) ≤ 3)]))
    (declaration? := some ``boundedRule)
  reject (← `(input (fun x : ℝ => bounded (x + 1)) #[]))
    "entire selected predicate" (rule? := some concreteRule)
  reject (← `(input (fun p : ℝ × ℝ => bounded (p.1 + 1)) #[]))
    "entire selected predicate" (rule? := some concreteRule)

noncomputable def userBound (c x : ℝ) : Prop := |x| ≤ c

@[morew_nlp] noncomputable def completePredicateRule (c : ℝ) :
    ExactConstraintLift (fun x : ℝ => userBound c x) :=
  .ofIff (fun x => x ≤ c ∧ -x ≤ c)
    (fun x => Rewrite.Polyhedral.abs_le_iff x c)

run_cmd liftTermElabM do
  check (← `(fun c : ℝ => input (fun x : ℝ => userBound c x) #[])) 2 none 1

noncomputable def userSquare (x : ℝ) : ℝ := x * x

@[morew_nlp] noncomputable def graphRule : GraphRepresentation userSquare where
  Auxiliary := Unit
  target x y _ := y = x * x
  source_iff_exists _ _ := by simp [userSquare]

run_cmd liftTermElabM do
  check (← `(input (fun p : ℝ × ℝ => p.2 = userSquare p.1) #[])) 1
  check (← `(input (fun p : ℝ × ℝ => userSquare p.1 = p.2) #[])) 1

-- A graph orientation is usable only after its generated rows are certified.
-- The first source below initially matches the constant input, leaving the
-- unsupported decision-dependent helper `shift x` in the target. Retrying with
-- the other orientation must discard that attempt's metavariables and declarations.
noncomputable def shift (x : ℝ) : ℝ := x + 1

@[morew_nlp] noncomputable def shiftGraph : GraphRepresentation shift where
  Auxiliary := Unit
  target x y _ := y = x + 1
  source_iff_exists x y := by simp only [shift, exists_const]

run_cmd liftTermElabM do
  exactRows (← `(input (fun x : ℝ => shift x = shift 3)
    #[(fun x : ℝ => shift 3 = x + 1)]))
  exactRows (← `(input (fun x : ℝ => shift 3 = shift x)
    #[(fun x : ℝ => shift 3 = x + 1)]))
  exactRows (← `(input (fun x : ℝ => shift x = shift 3)
    #[(fun x : ℝ => shift 3 = x + 1)])) (declaration? := some ``shiftGraph)
  exactRows (← `(input (fun x : ℝ => shift 3 = shift x)
    #[(fun x : ℝ => shift 3 = x + 1)])) (declaration? := some ``shiftGraph)
  let concreteRule ← Domain.elaborate (← `(shiftGraph))
  exactRows (← `(input (fun x : ℝ => shift x = shift 3)
    #[(fun x : ℝ => shift 3 = x + 1)])) (rule? := some concreteRule)
  exactRows (← `(input (fun x : ℝ => shift 3 = shift x)
    #[(fun x : ℝ => shift 3 = x + 1)])) (rule? := some concreteRule)

-- One general Euclidean registration handles both carrier spellings. Adding the
-- specialized record is a real second success, not an implicit priority choice.
run_cmd liftTermElabM do
  check (← `(input (fun v : Fin 2 → ℝ => ‖WithLp.toLp 2 v‖ ≤ 3) #[])) 2
  check (← `(input (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖ ≤ 3) #[])) 2
  check (← `(input (fun v : Fin 2 → ℝ => ‖WithLp.toLp 2 v‖ ≤ 3) #[])) 2
    (some ``Morew.Rewrite.norm2Epigraph)

run_cmd liftTermElabM do
  exactRows (← `(fun n : ℕ => input
    (fun p : (Fin n → ℝ) × ℝ => ‖WithLp.toLp 2 (fun i => (p.1 i) ^ 2 - 1)‖ ≤ p.2)
    #[(fun p : (Fin n → ℝ) × ℝ => 0 ≤ p.2),
      (fun p : (Fin n → ℝ) × ℝ => (∑ i, ((p.1 i) ^ 2 - 1) ^ 2) ≤ p.2 ^ 2)])) 1
  exactRows (← `(fun n : ℕ => input
    (fun p : EuclideanSpace ℝ (Fin n) × ℝ => ‖p.1‖ ≤ p.2)
    #[(fun p : EuclideanSpace ℝ (Fin n) × ℝ => 0 ≤ p.2),
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        (∑ i, (WithLp.ofLp p.1 i) ^ 2) ≤ p.2 ^ 2)])) 1

section
attribute [local morew_nlp] Morew.Rewrite.norm2Epigraph

run_cmd liftTermElabM do
  reject (← `(input (fun v : Fin 2 → ℝ => ‖WithLp.toLp 2 v‖ ≤ 3) #[]))
    "ambiguous exact NLP rules: Morew.Rewrite.euclideanNormEpigraph, Morew.Rewrite.norm2Epigraph"
  check (← `(input (fun v : Fin 2 → ℝ => ‖WithLp.toLp 2 v‖ ≤ 3) #[])) 2
    (some ``Morew.Rewrite.norm2Epigraph)
end

end MorewTest.NLP.Registry
