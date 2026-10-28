/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.DomainSupport

/-!
# Native Euclidean smoothness and domain certificates

Coordinate extraction and construction preserve the exact original function,
including symbolic and empty dimensions. Bounded smooth helper expansion keeps
the existing independent-helper argument policy and native-operation checks.
-/

namespace MorewTest.NLP.Euclidean

open Lean Lean.Meta Lean.Elab.Term
open MorewTest.NLP.Smooth MorewTest.NLP.Domain

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : EuclideanSpace ℝ (Fin 2) => x 0 * x 1))
  assertSmooth (← `(fun n : Nat => fun i : Fin n =>
    fun x : EuclideanSpace ℝ (Fin n) => WithLp.ofLp x i)) 2
  assertSmooth (← `(fun n : Nat => fun x : EuclideanSpace ℝ (Fin n) =>
    ∑ i, x i ^ 2)) 1
  assertSmooth (← `(fun x : EuclideanSpace ℝ (Fin 0) => ∑ i, x i ^ 2))
  assertSmooth (← `(fun x : EuclideanSpace ℝ (Fin 2) × ℝ =>
    (x.1 + x.1) 0 - x.2 ^ 2))
  assertSmooth (← `(fun x : ℝ =>
    WithLp.ofLp (WithLp.toLp 2 (fun _i : Fin 2 => Real.exp x)) 0))
  assertSmooth (← `(fun x : EuclideanSpace ℝ (Fin 2) =>
    (WithLp.toLp 2 (WithLp.ofLp x)) 0))
  assertSmooth (← `(fun n : Nat => fun i : Fin n =>
    fun x : Fin 2 → EuclideanSpace ℝ (Fin n) => (x 0) i)) 2

/-! Canonical operations remain fixed when unrelated analytic instances are local. -/

private def checkAmbientGroup (term : TSyntax `term) : TermElabM Unit := do
  let source ← MorewTest.NLP.Smooth.elaborate term
  let baseline ← MorewTest.NLP.Smooth.checkSuccess source
  let baselineType ← inferType baseline
  let .forallE _ decision _ _ ← whnf (← inferType source)
    | throwError "expected a decision function"
  let groupType ← mkAppM ``NormedAddCommGroup #[decision]
  withLocalDecl `ambientGroup .instImplicit groupType fun ambient => do
    let proof ← MorewTest.NLP.Smooth.checkSuccess source
    let proofType ← inferType proof
    if proof.containsFVar ambient.fvarId! || proofType.containsFVar ambient.fvarId! then
      throwError "Euclidean smoothness captured an unrelated ambient analytic instance"
    unless ← isDefEq proofType baselineType do
      throwError "ambient analytic instance changed the Euclidean smoothness proposition"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAmbientGroup (← `(fun x : EuclideanSpace ℝ (Fin 2) => (x + x) 0))
  assertRejected (← `(fun [HAdd (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))] =>
    fun x : EuclideanSpace ℝ (Fin 2) => (x + x) 0)) .invalidInstance 1
  assertRejected (← `(fun [Neg (EuclideanSpace ℝ (Fin 2))] =>
    fun x : EuclideanSpace ℝ (Fin 2) => (-x) 0)) .invalidInstance 1

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(fun n : Nat => fun i : Fin n =>
    ((fun x : EuclideanSpace ℝ (Fin n) => 1 ≤ x i),
      #[fun x : EuclideanSpace ℝ (Fin n) => Real.log (x i)]))) 2
  assertDomain (← `(((fun _x : EuclideanSpace ℝ (Fin 0) => True),
    #[fun x : EuclideanSpace ℝ (Fin 0) => ∑ i, Real.log (x i)])))
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => (WithLp.toLp 2 (fun _i : Fin 1 => Real.log (Real.exp x))) 0])))
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => (WithLp.toLp 2 (fun _i : Fin 1 => Real.log x)) 0])))
    .feasibleInclusion

private noncomputable def euclideanHelper (_x : EuclideanSpace ℝ (Fin 1)) : ℝ := 7
private noncomputable def mixedHelper (_x : EuclideanSpace ℝ (Fin 1) × ℝ) : ℝ := 7
private noncomputable def scalarHelper (x : ℝ) : ℝ := Real.exp x

run_cmd Lean.Elab.Command.liftTermElabM do
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => euclideanHelper (WithLp.toLp 2 (fun _i : Fin 1 => Real.log 0)) + x])))
  assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => mixedHelper (WithLp.toLp 2 (fun _i : Fin 1 => 0), Real.log 0) + x])))
  assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => scalarHelper (Real.log 0) + x]))) .feasibleInclusion
  assertSmooth (← `(fun x : ℝ => scalarHelper x))
  assertSmooth (← `(fun x : EuclideanSpace ℝ (Fin 1) => euclideanHelper x))
  assertRejected (← `(fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖)) .unknownHead

set_option morew.smooth.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => scalarHelper x)) .unknownHead
  assertRejected (← `(fun x : EuclideanSpace ℝ (Fin 1) => euclideanHelper x)) .unknownHead

end MorewTest.NLP.Euclidean
