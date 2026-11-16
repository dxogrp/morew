/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Cone.Rewrite
import MorewTest.ElabSupport
import MorewTest.Environment

/-!
# Matrix-quadratic epigraph certificates

Named and native sources retain separate rule heads and share a single rotated
cone. Fixed semidefinite matrices include singular and empty matrices.
-/

namespace MorewTest.Conic.QuadForm

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Conic MorewTest.Affine
open scoped Matrix

noncomputable section

example (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) :
    (Conic.QuadForm.epigraph Q hQ).Auxiliary = Unit := rfl

example (Q : Matrix (Fin n) (Fin n) ℝ) (hQ hQ' : Q.PosSemidef)
    (v : Fin n → ℝ) (t : ℝ) :
    (Conic.QuadForm.epigraph Q hQ).target v t () =
      (Conic.QuadForm.nativeEpigraph Q hQ').target v t () := rfl

example (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef)
    (v : Fin n → ℝ) (t : ℝ) :
    (Conic.QuadForm.epigraph Q hQ).target v t () ↔
      (t, 1 / 2, Conic.QuadForm.factor Q *ᵥ v) ∈ RSOC n := Iff.rfl

example (v : Fin n → ℝ) (t : ℝ) :
    (∃ u, (Conic.QuadForm.epigraph 0 Matrix.PosSemidef.zero).target v t u) ↔
      0 ≤ t := by
  rw [← (Conic.QuadForm.epigraph 0 Matrix.PosSemidef.zero).source_iff_exists]
  simp

example (Q : Matrix (Fin 0) (Fin 0) ℝ) (hQ : Q.PosSemidef)
    (v : Fin 0 → ℝ) (t : ℝ) :
    (∃ u, (Conic.QuadForm.nativeEpigraph Q hQ).target v t u) ↔ 0 ≤ t := by
  rw [← (Conic.QuadForm.nativeEpigraph Q hQ).source_iff_exists]
  simp [dotProduct]

example (Q : Matrix (Fin 0) (Fin 0) ℝ) (hQ : Q.PosSemidef)
    (v : Fin 0 → ℝ) :
    ¬ ∃ u, (Conic.QuadForm.epigraph Q hQ).target v (-1) u := by
  rw [← (Conic.QuadForm.epigraph Q hQ).source_iff_exists]
  simp

private def singular : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]

private theorem singularPSD : singular.PosSemidef :=
  Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)

example : ∃ u, (Conic.QuadForm.epigraph singular singularPSD).target ![3, 7] 9 u := by
  rw [← (Conic.QuadForm.epigraph singular singularPSD).source_iff_exists]
  norm_num [Fn.quadForm, singular, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

example : ¬ ∃ u, (Conic.QuadForm.nativeEpigraph singular singularPSD).target ![3, 7] 8 u := by
  rw [← (Conic.QuadForm.nativeEpigraph singular singularPSD).source_iff_exists]
  norm_num [singular, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private def check (source expected : Expr) (rule? : Option Name := none) : MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let outcome ← match rule? with
    | none => Morew.Elab.Cone.Rewrite.planUnique source
    | some rule => Morew.Elab.Cone.Rewrite.planDeclaration source rule
  assertExprMVarStateUnchanged before "matrix-quadratic planning"
  unless sameLocalDeclarationNames environment (← getEnv) do
    throwError "matrix-quadratic planning changed local declarations"
  let result ← match outcome with
    | .ok result => pure result
    | .error error => throwError "matrix-quadratic epigraph was rejected: {error.reason}"
  result.toResult.check source #[]
  unless result.auxiliary?.isNone && result.rowPredicates.size == 1 &&
      result.certifiedRows.size == 1 do
    throwError "expected one rotated cone without auxiliary decisions"
  unless ← isDefEq result.nextDomain (← Morew.Elab.Rewrite.Plan.predicateDomain source) do
    throwError "matrix-quadratic planning changed the decision space"
  unless ← isDefEq result.rowPredicates[0]! expected do
    throwError "unexpected matrix-quadratic cone coordinates"
  for proof in #[result.certificate.expression, result.targetIff] ++
      result.certifiedRows.flatMap (fun row => #[row.constraint, row.pointwiseIff]) do
    checkCompleteWithKernel proof "incomplete matrix-quadratic certificate"

private def reject (source : Expr) (rule? : Option Name := none) : MetaM Unit := do
  let sentinel ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  let environment ← getEnv
  let outcome ← match rule? with
    | none => Morew.Elab.Cone.Rewrite.planUnique source
    | some rule => Morew.Elab.Cone.Rewrite.planDeclaration source rule
  let .error _ := outcome | throwError "unsupported matrix-quadratic bound was accepted"
  assertExprMVarStateUnchanged before "failed matrix-quadratic planning"
  if ← sentinel.mvarId!.isAssigned then
    throwError "failed matrix-quadratic planning assigned a caller metavariable"
  unless sameLocalDeclarationNames environment (← getEnv) do
    throwError "failed matrix-quadratic planning changed local declarations"

-- Use symbolic dimensions and rectangular affine residuals for both source heads.
private def checkFamily (native : Bool) (rule? : Option Name := none)
    (rejected : Bool := false) : TermElabM Unit := do
  let expression ← elaborate (← `(fun (m n : Nat) (Q : Matrix (Fin m) (Fin m) ℝ)
    (_hQ : Q.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) =>
    ((fun p : (Fin n → ℝ) × ℝ => Fn.quadForm (A *ᵥ p.1 + b) Q ≤ p.2),
     (fun p : (Fin n → ℝ) × ℝ =>
       p.2 ≥ (A *ᵥ p.1 + b) ⬝ᵥ (Q *ᵥ (A *ᵥ p.1 + b))),
     (fun p : (Fin n → ℝ) × ℝ =>
       (p.2, 1 / 2, Conic.QuadForm.factor Q *ᵥ (A *ᵥ p.1 + b)) ∈ RSOC m))))
  lambdaBoundedTelescope expression 6 fun _ bodies => do
    let source ← whnf <| .proj ``Prod 0
      (if native then .proj ``Prod 1 bodies else bodies)
    let expected ← whnf <| .proj ``Prod 1 (.proj ``Prod 1 bodies)
    if rejected then reject source rule? else check source expected rule?

run_cmd liftTermElabM do
  checkFamily false
  checkFamily true
  checkFamily false (some ``Conic.QuadForm.epigraph)
  checkFamily true (some ``Conic.QuadForm.nativeEpigraph)
  -- Definitional equality must not silently exchange the two source spellings.
  checkFamily false (some ``Conic.QuadForm.nativeEpigraph) true
  checkFamily true (some ``Conic.QuadForm.epigraph) true

section NamedRemoved

attribute [-morew_conic] Morew.Conic.QuadForm.epigraph

run_cmd liftTermElabM do
  checkFamily false none true
  checkFamily true
  checkFamily false (some ``Conic.QuadForm.epigraph)

end NamedRemoved

section NativeRemoved

attribute [-morew_conic] Morew.Conic.QuadForm.nativeEpigraph

run_cmd liftTermElabM do
  checkFamily true none true
  checkFamily false
  checkFamily true (some ``Conic.QuadForm.nativeEpigraph)

end NativeRemoved

-- Plan concrete zero and empty matrices, rather than only specializing a symbolic plan.
run_cmd liftTermElabM do
  let expression ← elaborate (← `(fun
    (_hQ : (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef) =>
    ((fun p : (Fin 2 → ℝ) × ℝ => Fn.quadForm p.1 0 ≤ p.2),
     (fun p : (Fin 2 → ℝ) × ℝ =>
       (p.2, 1 / 2, Conic.QuadForm.factor 0 *ᵥ p.1) ∈ RSOC 2))))
  lambdaBoundedTelescope expression 1 fun _ bodies => do
    check (← whnf <| .proj ``Prod 0 bodies) (← whnf <| .proj ``Prod 1 bodies)
  let expression ← elaborate (← `(fun
    (_hQ : (0 : Matrix (Fin 0) (Fin 0) ℝ).PosSemidef) =>
    ((fun p : (Fin 0 → ℝ) × ℝ => p.1 ⬝ᵥ ((0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ p.1) ≤ p.2),
     (fun p : (Fin 0 → ℝ) × ℝ =>
       (p.2, 1 / 2, Conic.QuadForm.factor 0 *ᵥ p.1) ∈ RSOC 0))))
  lambdaBoundedTelescope expression 1 fun _ bodies => do
    check (← whnf <| .proj ``Prod 0 bodies) (← whnf <| .proj ``Prod 1 bodies)

run_cmd liftTermElabM do
  let expression ← elaborate (← `(fun (Q : Matrix (Fin 2) (Fin 2) ℝ) =>
    fun p : (Fin 2 → ℝ) × ℝ => Fn.quadForm p.1 Q ≤ p.2))
  lambdaBoundedTelescope expression 1 fun _ source => do
    reject source
    reject source (some ``Conic.QuadForm.epigraph)
  let expression ← elaborate (← `(fun (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (_hQ : Q.PosSemidef) =>
    ((fun p : (Fin 2 → ℝ) × ℝ => p.2 ≤ Fn.quadForm p.1 Q),
     (fun p : (Fin 2 → ℝ) × ℝ => Fn.quadForm p.1 Q = p.2),
     (fun p : (Fin 2 → ℝ) × ℝ => Fn.quadForm (fun i => p.1 i ^ 2) Q ≤ p.2),
     (fun p : (Fin 2 → ℝ) × ℝ => Fn.quadForm p.1 Q ≤ p.2 ^ 2),
     (fun p : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ℝ => p.1.1 ⬝ᵥ (Q *ᵥ p.1.2) ≤ p.2))))
  lambdaBoundedTelescope expression 2 fun _ bodies => do
    let mut bodies := bodies
    for _ in [:4] do
      reject (← whnf <| .proj ``Prod 0 bodies)
      bodies ← whnf <| .proj ``Prod 1 bodies
    reject bodies
  let expression ← elaborate (← `(fun
    (Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (_hQ : ∀ x, (Q x).PosSemidef) =>
    fun p : ℝ × (Fin 2 → ℝ) × ℝ => Fn.quadForm p.2.1 (Q p.1) ≤ p.2.2))
  lambdaBoundedTelescope expression 2 fun _ source => reject source

end
end MorewTest.Conic.QuadForm
