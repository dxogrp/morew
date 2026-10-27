/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Polyhedral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Typed exact polyhedral planning

These tests check exactness, ordered row decomposition, native instance
recognition, local evidence, caller metavariable state, and custom whole-predicate
certificate adapters independently of the surface reformulation command.
-/

namespace MorewTest.Conic.PolyhedralElab

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Morew
open scoped ENNReal

noncomputable section

private def elaborate (stx : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

private def expectPlan (stx : TSyntax `term) (rows : Nat) (auxiliary : Bool)
    (rule? : Option (TSyntax `term) := none) (parameterCount : Nat := 0) :
    TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let rule? ← rule?.mapM elaborate
    let outcome ← Morew.Elab.Conic.Polyhedral.plan source rule?
    let result ← match outcome with
      | .ok result => pure result
      | .error error => throwError "expected a polyhedral plan for {source}: {error.reason}"
    unless result.rowPredicates.size == rows && result.certifiedRows.size == rows do
      throwError "expected {rows} rows, got {result.rowPredicates.size}"
    unless result.auxiliary?.isSome == auxiliary do
      throwError "unexpected auxiliary-variable shape"
    checkWithKernel result.lift
    checkWithKernel result.targetIff
    for row in result.certifiedRows do
      checkWithKernel row.constraint
      checkWithKernel row.pointwiseIff

private def expectRejected (stx : TSyntax `term) (fragment : String)
    (rule? : Option (TSyntax `term) := none) : TermElabM Unit := do
  let source ← elaborate stx
  let rule? ← rule?.mapM elaborate
  let .error error ← Morew.Elab.Conic.Polyhedral.plan source rule?
    | throwError "unsupported polyhedral predicate was accepted"
  let message ← error.reason.toString
  unless message.contains fragment do
    throwError "expected diagnostic containing {fragment}, got {message}"

elab "polyhedral_lift% " source:term : term => do
  let source ← elaborate source
  match ← Morew.Elab.Conic.Polyhedral.plan source with
  | .ok result => pure result.lift
  | .error error => throwError "{error.reason}"

def symbolicNorm (n : ℕ) : ExactConstraintLift (fun v : Fin n → ℝ => ‖v‖ ≤ 2) :=
  polyhedral_lift% (fun v : Fin n → ℝ => ‖v‖ ≤ 2)

def symbolicOneNorm (n : ℕ) :
    ExactConstraintLift (fun v : Fin n → ℝ => ‖WithLp.toLp 1 v‖ ≤ 2) :=
  polyhedral_lift% (fun v : Fin n → ℝ => ‖WithLp.toLp 1 v‖ ≤ 2)

def symbolicMaximum {ι : Type u} (s : Finset ι) (hs : s.Nonempty) (a : ι → ℝ) :
    ExactConstraintLift (fun x : ℝ => s.sup' hs (fun i => a i * x) ≤ 2) :=
  polyhedral_lift% (fun x : ℝ => s.sup' hs (fun i => a i * x) ≤ 2)

run_cmd Lean.Elab.Command.liftTermElabM do
  expectPlan (← `(fun p : ℝ × ℝ => |p.1 + 1| ≤ p.2)) 2 false
  expectPlan (← `(fun p : ℝ × ℝ => p.2 ≥ |p.1 + 1|)) 2 false
  expectPlan (← `(fun x : ℝ => x⁺ ≤ 3)) 2 false
  expectPlan (← `(fun p : ℝ × ℝ => max (p.1 + 1) (-p.1) ≤ p.2)) 2 false
  expectPlan (← `(fun p : ℝ × ℝ => p.2 ≤ min (p.1 + 1) (-p.1))) 2 false
  expectPlan (← `(fun v : Fin 3 → ℝ => ‖v‖ ≤ 4)) 3 false
  expectPlan (← `(fun v : Fin 0 → ℝ => ‖v‖ ≤ -1)) 3 false
  expectPlan (← `(fun v : Fin 3 → ℝ => ‖WithLp.toLp ∞ v‖ ≤ 4)) 3 false
  expectPlan (← `(fun v : Fin 3 → ℝ => ‖WithLp.toLp 1 v‖ ≤ 4)) 3 true
  expectPlan (← `(fun v : Fin 0 → ℝ => ‖WithLp.toLp 1 v‖ ≤ -1)) 3 true
  expectPlan (← `(fun x : ℝ =>
    ({1, 3} : Finset ℕ).sup' (by decide) (fun i => (i : ℝ) * x) ≤ 4)) 1 false
  expectPlan (← `(fun x : ℝ =>
    4 ≤ ({1, 3} : Finset ℕ).inf' (by decide) (fun i => (i : ℝ) * x))) 1 false

/-! Affine certification must retain local nonzero proofs and finite-index
instances supplied only inside the selected predicate. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  expectPlan (← `(fun (a : ℝ) => fun x : ℝ =>
    let h : Real.exp a ≠ 0 := Real.exp_ne_zero a
    |x / Real.exp a| ≤ 1)) 2 false (parameterCount := 1)
  expectPlan (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) =>
    fun x : ι → ℝ =>
      |@dotProduct ι ℝ (Fintype.ofEquiv (Fin 2) e) _ _ a x| ≤ 1))
    2 false (parameterCount := 3)
  expectPlan (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) =>
    fun x : ι → ℝ =>
      letI := Fintype.ofEquiv (Fin 2) e
      max (a ⬝ᵥ x) (x ⬝ᵥ a) ≤ 1)) 2 false (parameterCount := 3)

def wholeConjunction : ExactConstraintLift (fun p : ℝ × ℝ => |p.1| ≤ p.2 ∧ 0 ≤ p.2) :=
  ExactConstraintLift.ofIff
    (fun p : ℝ × ℝ => True ∧ (p.1 ≤ p.2 ∧ -p.1 ≤ p.2) ∧ 0 ≤ p.2 ∧ True)
    (fun _ => by simp only [true_and, and_true, Morew.Conic.Polyhedral.abs_le_iff])

def affineGraph : GraphRepresentation (fun x : ℝ => x + 1) where
  Auxiliary := Unit
  target x y _ := y = x + 1
  source_iff_exists _ _ := ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩

def absEpigraph : EpigraphRepresentation (fun x : ℝ => |x|) where
  Auxiliary := Unit
  target x t _ := x ≤ t ∧ -x ≤ t
  source_iff_exists _ _ := by simp only [exists_const, Morew.Conic.Polyhedral.abs_le_iff]

def minimumHypograph : HypographRepresentation (fun p : ℝ × ℝ => min p.1 p.2) where
  Auxiliary := Unit
  target p t _ := t ≤ p.1 ∧ t ≤ p.2
  source_iff_exists _ _ := by simp only [exists_const, Morew.Conic.Polyhedral.le_min_iff]

def oneAuxiliary : ExactConstraintLift (fun x : ℝ => 0 ≤ x) where
  Auxiliary := ℝ
  target x a := a = x ∧ 0 ≤ a
  source_iff_exists x := by
    constructor
    · intro h
      exact ⟨x, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h

def nonlinearExact : ExactConstraintLift (fun x : ℝ => 0 ≤ x ^ 2) :=
  ExactConstraintLift.ofIff (fun x : ℝ => 0 ≤ x ^ 2) (fun _ => Iff.rfl)

def boolAuxiliary : ExactConstraintLift (fun x : ℝ => 0 ≤ x) where
  Auxiliary := Bool
  target x _ := 0 ≤ x
  source_iff_exists _ := ⟨fun h => ⟨false, h⟩, fun ⟨_, h⟩ => h⟩

def opaqueAbs (x : ℝ) : ℝ := |x|

def unchangedTrue : ExactConstraintLift (fun _ : ℝ => True) :=
  ExactConstraintLift.ofIff (fun _ => True) (fun _ => Iff.rfl)

def predicateHelper (x : ℝ) : Prop := 0 ≤ x

def wrappedTarget : ExactConstraintLift predicateHelper :=
  ExactConstraintLift.ofIff predicateHelper (fun _ => Iff.rfl)

def disjunctiveTarget : ExactConstraintLift (fun x : ℝ => 0 ≤ x ∨ x ≤ 0) :=
  ExactConstraintLift.ofIff (fun x => 0 ≤ x ∨ x ≤ 0) (fun _ => Iff.rfl)

run_cmd Lean.Elab.Command.liftTermElabM do
  expectPlan (← `(fun p : ℝ × ℝ => |p.1| ≤ p.2 ∧ 0 ≤ p.2)) 3 false
    (some (← `(wholeConjunction)))
  expectPlan (← `(fun p : ℝ × ℝ => p.2 = p.1 + 1)) 1 false
    (some (← `(affineGraph)))
  expectPlan (← `(fun p : ℝ × ℝ => p.1 + 1 = p.2)) 1 false
    (some (← `(affineGraph)))
  expectPlan (← `(fun p : ℝ × ℝ => |p.1| ≤ p.2)) 2 false
    (some (← `(absEpigraph)))
  expectPlan (← `(fun p : (ℝ × ℝ) × ℝ => p.2 ≤ min p.1.1 p.1.2)) 2 false
    (some (← `(minimumHypograph)))
  expectPlan (← `(fun x : ℝ => 0 ≤ x)) 2 true (some (← `(oneAuxiliary)))
  expectPlan (← `(fun _ : ℝ => True)) 0 false (some (← `(unchangedTrue)))
  expectRejected (← `(fun x : ℝ => 0 ≤ x ^ 2)) "generated row"
    (some (← `(nonlinearExact)))
  expectRejected (← `(fun x : ℝ => 0 ≤ x)) "unsupported exact-lift decision space"
    (some (← `(boolAuxiliary)))
  expectRejected (← `(fun p : ℝ × ℝ => |p.1| ≤ p.2 ∧ 0 ≤ p.2)) "does not match"
    (some (← `(absEpigraph)))
  expectRejected (← `(fun x : ℝ => opaqueAbs x ≤ 1)) "no supported"
  expectRejected (← `(fun x : ℝ => |x * x| ≤ 1)) "generated row"
  expectRejected (← `(fun x : ℝ => 1 ≤ |x|)) "no supported"
  expectRejected (← `(fun x : ℝ => |x| = 1)) "no supported"
  expectRejected (← `(fun v : Fin 2 → ℝ => ‖WithLp.toLp 2 v‖ ≤ 1)) "WithLp 2"
  expectRejected (← `(fun x : ℝ => @LE.le ℝ ⟨fun a b => a + 1 ≤ b⟩ |x| 1)) "order instance"
  expectRejected (← `(fun v : Fin 2 → ℝ =>
    @Norm.norm (Fin 2 → ℝ) ⟨fun _ => 0⟩ v ≤ 1)) "instance"
  -- Coincident operands still require the native maximum instance.
  expectRejected (← `(fun x : ℝ =>
    @Max.max ℝ ⟨fun a _ => a⟩ x x ≤ 1)) "instance"
  expectRejected (← `(fun x : ℝ =>
    @Finset.sup' ℝ ℕ (inferInstance : SemilatticeSup (OrderDual ℝ))
      {0} (by simp) (fun _ => x) ≤ 1)) "instance"
  expectRejected (← `(fun x : ℝ =>
    (if x ≤ 0 then ({0} : Finset ℕ) else {1}).sup'
      (by split <;> simp) (fun i => (i : ℝ) * x) ≤ 1)) "decision variable"
  expectRejected (← `(fun x : ℝ => 0 ≤ x ∨ x ≤ 0)) "unsupported exact target"
    (some (← `(disjunctiveTarget)))
  expectRejected (← `(predicateHelper)) "unsupported exact target"
    (some (← `(wrappedTarget)))

/-! Unresolved data may be hidden in let declarations. Neither failed nor
successful recognition may assign caller metavariables or retain scratch ones. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => |x| ≤ c))
  let missing ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  let .error error ← Morew.Elab.Conic.Polyhedral.plan (mkApp builder missing)
    | throwError "an unresolved bound was accepted"
  unless (← error.reason.toString).contains "unresolved metavariables" do
    throwError "wrong unresolved-bound diagnostic: {error.reason}"
  if ← missing.mvarId!.isAssigned then throwError "the planner assigned the unresolved bound"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "failed planning leaked scratch metavariables"
  withLetDecl `hiddenBound (mkConst ``Real) missing fun hidden => do
    let .error error ← Morew.Elab.Conic.Polyhedral.plan (mkApp builder hidden)
      | throwError "an unresolved bound hidden in a let was accepted"
    unless (← error.reason.toString).contains "unresolved metavariables" do
      throwError "wrong hidden-bound diagnostic: {error.reason}"
  let coefficientBuilder ← elaborate (← `(fun (a x : ℝ) => |a * x| ≤ 1))
  withLetDecl `coefficient (mkConst ``Real) missing fun coefficient => do
    let .error error ← Morew.Elab.Conic.Polyhedral.plan (mkApp coefficientBuilder coefficient)
      | throwError "planner specialized an unresolved coefficient hidden in a local declaration"
    unless (← error.reason.toString).contains "unresolved" do
      throwError "missing unresolved-coefficient diagnostic"
    if ← missing.mvarId!.isAssigned then
      throwError "failed planning assigned a caller metavariable"
  let source ← elaborate (← `(fun x : ℝ => |x| ≤ 2))
  let before ← getMCtx
  let .ok _ ← Morew.Elab.Conic.Polyhedral.plan source
    | throwError "the state-isolation success case failed"
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "successful planning leaked scratch metavariables"
  if ← missing.mvarId!.isAssigned then throwError "successful planning assigned an unrelated hole"

end

end MorewTest.Conic.PolyhedralElab
