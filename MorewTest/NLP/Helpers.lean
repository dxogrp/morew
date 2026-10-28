/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.HelperFixtures
import MorewTest.NLP.DomainSupport

/-!
# Ordinary helpers in smooth certificates

Helpers expand only for proof construction. Success assertions check the exact
original source and kernel-check all analytic and domain evidence.
-/

namespace MorewTest.NLP.Helpers

open Lean Lean.Meta Lean.Elab.Term
open MorewTest.NLP.Smooth MorewTest.NLP.HelperFixtures

private noncomputable def betaConstantWrapper (x : ℝ) : ℝ :=
  hiddenLog ((fun _ : ℝ => 0) x) + x

private noncomputable def closedProblem : Morew.Problem ℝ ℝ :=
  ⟨fun x => x * x, fun _ => True⟩

private noncomputable def throughClosedProblem (x : ℝ) : ℝ :=
  closedProblem.objective x

private noncomputable def powerSquare (x : ℝ) : ℝ := x ^ 2

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => square x))
  assertSmooth (← `(fun x : ℝ => shift x))
  assertSmooth (← `(fun x : ℝ => nestedSquare x))
  assertSmooth (← `(fun a b : ℝ => fun x : ℝ => polynomial a b x)) 2
  assertSmooth (← `(fun (α : Type 1) (tag : α) => fun x : ℝ => taggedSquare tag x)) 2
  assertSmooth (← `(fun x : ℝ => taggedSquare (ULift.up.{1} ()) x))
  assertSmooth (← `(square ∘ Real.exp))
  assertSmooth (← `(Real.exp ∘ square))
  assertSmooth (← `(fun x : ℝ => let f := square; f x))
  assertSmooth (← `(fun n : Nat => fun v : Fin n → ℝ => sumSquares v)) 1
  assertSmooth (← `(fun v : EuclideanSpace ℝ (Fin 1) => euclideanSquare v))

run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← elaborate (← `(fun x : ℝ => square x))
  let proof ← checkSuccess source
  let type ← inferType proof
  unless type.isAppOfArity ``ContDiffOn 11 && type.getAppArgs[9]! == source do
    throwError "helper certificate exposed its expanded body instead of the original source"

-- Opening the applied helper comes before evaluating its unused arguments.
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => ignored (Real.log x)))
  assertSmooth (← `(fun x : ℝ => ignoredPair (Real.log x, |x|)))
  assertSmooth (← `(fun x : ℝ => ignoredVector (fun _i => Real.log x)))
  assertSmooth (← `(fun x : ℝ => ignored (x ^ hiddenExponent x)))
  assertSmooth (← `(fun x : ℝ => (smoothTuple x).1))
  assertSmooth (← `(fun x : ℝ => functionPair.1 x))
  assertSmooth (← `(fun x : ℝ => (partialAddPair x).1 x))

-- Native operations keep their own boundary even when an operand is a helper.
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => hiddenAbs x)) .nonsmooth 0 (some ``abs)
  assertRejected (← `(fun x : ℝ => hiddenLog x)) .restrictedDomain 0 (some ``Real.log)
  assertRejected (← `(fun x : ℝ => hiddenTan x)) .unknownHead 0 (some ``Real.tan)
  assertRejected (← `(fun x : ℝ => branchSquare x)) .unknownHead
  assertRejected (← `(fun x : ℝ => |ignored x|)) .nonsmooth 0 (some ``abs)
  assertRejected (← `(fun x : ℝ => noncanonical x)) .invalidInstance
  assertRejected (← `(fun x : ℝ => noncanonicalPair.1 x)) .invalidInstance
  assertRejected (← `(fun x : ℝ => (noncanonicalPartial x).1 x)) .invalidInstance
  assertRejected (← `(fun x : ℝ => x ^ hiddenExponent x)) .dependency
  assertRejected (← `(fun x : Fin 2 → ℝ => x (hiddenIndex (x 1)))) .dependency
  assertRejected (← `(fun x : ℝ => sealedSquare x)) .unknownHead 0 (some ``sealedSquare)
  assertRejected (← `(fun x : ℝ => irreducibleSquare x)) .unknownHead 0
    (some ``irreducibleSquare)
  assertRejected (← `(fun x : ℝ => recursiveSquare 1 x)) .unknownHead 0
    (some ``recursiveSquare)
  assertRejected (← `(fun x : ℝ => (squareProblem x).objective 0)) .unknownHead
  assertSmooth (← `(fun x : ℝ => closedProblem.objective x))
  assertRejected (← `(fun x : ℝ => throughClosedProblem x)) .unknownHead

-- Inner diagnostics preserve both the true obstruction and the helper chain.
run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← elaborate (← `(fun x : ℝ => nestedLog x))
  let .error error ← Morew.Elab.NLP.Smooth.certifyGlobal source
    | throwError "a helper hid a restricted logarithm"
  unless error.source == source && error.kind == .restrictedDomain &&
      error.expression.isAppOf ``Real.log do
    throwError "helper expansion lost the original source or inner obstruction"
  let reason ← error.reason.toString
  unless reason.contains "nestedLog" && reason.contains "hiddenLog" do
    throwError "helper diagnostic omitted its expansion chain: {reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  Domain.assertDomain (← `(((fun x : ℝ => 1 ≤ x), #[fun x : ℝ => hiddenLog x])))
  Domain.assertDomainRejected (← `(((fun x : ℝ => 0 ≤ x),
    #[fun x : ℝ => hiddenLog x]))) .feasibleInclusion 0 (some 0) none (some ``Real.log)
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignored (Real.log x)])))
  Domain.assertDomain (← `(fun c : ℝ => ((fun _x : ℝ => True),
    #[fun x : ℝ => withEvidence c x]))) 1
  Domain.assertDomain (← `(fun c : ℝ => ((fun _x : ℝ => True),
    #[fun x : ℝ => withInstanceEvidence c x]))) 1
  Domain.assertDomainRejected (← `(fun c : ℝ => ((fun _x : ℝ => True),
    #[fun x : ℝ => withDependentEvidence c x]))) .feasibleInclusion 1
  Domain.assertDomain (← `(fun n : Nat => fun c : Fin n → ℝ =>
    ((fun _v : Fin n → ℝ => True), #[fun v : Fin n → ℝ => indexedEvidence c v]))) 2
  Domain.assertDomainRejected (← `(fun c : Fin 2 → ℝ =>
    ((fun _v : Fin 2 → ℝ => True), #[fun v : Fin 2 → ℝ => wrongIndexEvidence c v])))
    .feasibleInclusion 1
  Domain.assertDomainRejected (← `(((fun x : ℝ => wrappedRow x),
    #[fun x : ℝ => square x]))) .unsupportedRow 0 none (some 0)

-- Evidence sees the already certified body through native constructors. The
-- matching native controls require no additional mathematical evidence rules.
run_cmd Lean.Elab.Command.liftTermElabM do
  for term in #[
      (← `(((fun _x : ℝ => True), #[fun x : ℝ => Real.log (x ^ 2 + 1)]))),
      (← `(((fun _x : ℝ => True), #[fun x : ℝ => Real.log (x * x + 1)]))),
      (← `(((fun _x : ℝ => True), #[fun x : ℝ => Real.log (coefficient x)]))),
      (← `(((fun _x : ℝ => True), #[fun x : ℝ => Real.log (square x + 1)])))] do
    Domain.assertDomain term
  for term in #[
      (← `(fun n : Nat => fun i : Fin n =>
        ((fun _v : Fin n → ℝ => True), #[fun v : Fin n → ℝ => Real.log ((v i) ^ 2 + 1)]))),
      (← `(fun n : Nat => fun i : Fin n =>
        ((fun _v : Fin n → ℝ => True), #[fun v : Fin n → ℝ => Real.log (coefficient (v i))])))] do
    Domain.assertDomain term 2
  Domain.withInput (← `(fun n : Nat => ((fun _v : Fin n → ℝ => True),
    #[fun v : Fin n → ℝ => Real.log ((∑ i, (v i) ^ 2) + 1),
      fun v : Fin n → ℝ => Real.log ((∑ i, powerSquare (v i)) + 1)]))) 1
    fun feasible sources => do
      unless ← isDefEq sources[0]! sources[1]! do
        throwError "finite-sum helper and native control differ"
      for source in sources do
        discard <| Domain.checkSuccess feasible #[source]
  for term in #[
      (← `(fun n : Nat => ((fun _v : Fin n → ℝ => True),
        #[fun v : Fin n → ℝ => ∑ i, Real.log ((v i) ^ 2 + 1)]))),
      (← `(fun n : Nat => ((fun _v : Fin n → ℝ => True),
        #[fun v : Fin n → ℝ => ∑ i, Real.log (coefficient (v i))])))] do
    Domain.assertDomain term 1
  for term in #[
      (← `(((fun _v : Fin 1 → ℝ => True),
        #[fun v : Fin 1 → ℝ => Real.log
          ((WithLp.toLp 2 (fun i : Fin 1 => (v i) ^ 2 + 1)) 0)]))),
      (← `(((fun _v : Fin 1 → ℝ => True),
        #[fun v : Fin 1 → ℝ => Real.log
          ((WithLp.toLp 2 (fun i : Fin 1 => coefficient (v i))) 0)])))] do
    Domain.assertDomain term

run_cmd Lean.Elab.Command.liftTermElabM do
  Domain.withInput (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => Real.log (coefficient x)]))) 0 fun feasible sources => do
      let result ← Domain.checkSuccess feasible sources
      let type ← inferType result.smooth[0]!
      unless type.isAppOfArity ``ContDiffOn 11 && type.getAppArgs[9]! == sources[0]! do
        throwError "domain certificate exposed its inspected helper body as the original function"

-- Certifying a sibling must not inspect an already independent helper's body.
run_cmd Lean.Elab.Command.liftTermElabM do
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => hiddenLog 0 + square x])))
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => square x + hiddenLog 0])))
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => constantPair.1 + square x])))
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => square x + constantPair.1])))
  Domain.assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => ignored (Real.log 0) + square x]))) .feasibleInclusion
  Domain.assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => square x + ignored (Real.log 0)]))) .feasibleInclusion
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => constantWrapper x])))
  Domain.assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => constantArgumentWrapper x]))) .feasibleInclusion
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => betaConstantWrapper x])))

end MorewTest.NLP.Helpers
