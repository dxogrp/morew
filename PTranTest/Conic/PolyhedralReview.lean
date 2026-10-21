import PTran.Elab.Conic.Polyhedral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Polyhedral planning evidence and instance boundaries

The planner must retain the affine fragment's local evidence while rejecting
custom native instances, decision-dependent indexing, and caller metavariables.
-/

namespace PTranTest.Conic.PolyhedralReview

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

private def elaborate (stx : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

private def expectPlan (stx : TSyntax `term) (parameterCount : Nat := 0) :
    TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression parameterCount fun _ predicate => do
    let result ← match ← PTran.Elab.Conic.Polyhedral.plan predicate with
      | .ok result => pure result
      | .error error => throwError "supported local evidence was lost: {error.reason}"
    checkWithKernel result.lift
    checkWithKernel result.targetIff
    for row in result.certifiedRows do
      checkWithKernel row.constraint
      checkWithKernel row.pointwiseIff

private def expectRejected (stx : TSyntax `term) (fragment : String) :
    TermElabM Unit := do
  let source ← elaborate stx
  let .error error ← PTran.Elab.Conic.Polyhedral.plan source
    | throwError "unsupported native instance or index set was accepted"
  unless (← error.reason.toString).contains fragment do
    throwError "unexpected polyhedral diagnostic: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  expectPlan (← `(fun (a : ℝ) => fun x : ℝ =>
    let h : Real.exp a ≠ 0 := Real.exp_ne_zero a
    |x / Real.exp a| ≤ 1)) 1
  expectPlan (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) =>
    fun x : ι → ℝ =>
      |@dotProduct ι ℝ (Fintype.ofEquiv (Fin 2) e) _ _ a x| ≤ 1)) 3
  expectPlan (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) =>
    fun x : ι → ℝ =>
      letI := Fintype.ofEquiv (Fin 2) e
      max (a ⬝ᵥ x) (x ⬝ᵥ a) ≤ 1)) 3

run_cmd Lean.Elab.Command.liftTermElabM do
  expectRejected (← `(fun x : ℝ =>
    @Max.max ℝ ⟨fun a _ => a⟩ x x ≤ 1)) "no supported"
  expectRejected (← `(fun v : Fin 1 → ℝ =>
    @Norm.norm (Fin 1 → ℝ) ⟨fun _ => 0⟩ v ≤ 1)) "unsupported instance"
  expectRejected (← `(fun x : ℝ =>
    @Finset.sup' ℝ ℕ (inferInstance : SemilatticeSup (OrderDual ℝ))
      {0} (by simp) (fun _ => x) ≤ 1)) "unsupported instance"
  expectRejected (← `(fun x : ℝ =>
    (if x ≤ 0 then ({0} : Finset ℕ) else {1}).sup'
      (by split <;> simp) (fun i => (i : ℝ) * x) ≤ 1)) "depends on a decision"

run_cmd Lean.Elab.Command.liftTermElabM do
  let family ← elaborate (← `(fun (a x : ℝ) => |a * x| ≤ 1))
  let real := Lean.mkConst ``Real
  let hole ← mkFreshExprMVar (some real)
  withLetDecl `coefficient real hole fun coefficient => do
    let source := mkApp family coefficient
    let .error error ← PTran.Elab.Conic.Polyhedral.plan source
      | throwError "planner specialized unresolved data hidden in a local declaration"
    unless (← error.reason.toString).contains "unresolved" do
      throwError "missing unresolved-source diagnostic"
    if ← hole.mvarId!.isAssigned then
      throwError "failed planning assigned a caller metavariable"

end PTranTest.Conic.PolyhedralReview
