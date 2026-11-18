/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import Morew.Elab.Cone.Rewrite
import MorewTest.ElabSupport
import MorewTest.Environment

/-!
# Matrix-fraction rule priority

When both built-in representations certify a fixed inverse matrix, automatic
selection retains the matrix-fraction representation. Explicit selection can use
either cone, and custom rules still participate in ambiguity checks.
-/

namespace MorewTest.Conic.MatFracPriority

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Conic MorewTest.Affine
open scoped Matrix

private meta def check (source expected : Expr) (rule? : Option Name := none) : MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let outcome ← match rule? with
    | none => Morew.Elab.Cone.Rewrite.planUnique source
    | some rule => Morew.Elab.Cone.Rewrite.planDeclaration source rule
  assertExprMVarStateUnchanged before "native matrix rule selection"
  unless sameLocalDeclarationNames environment (← getEnv) do
    throwError "native matrix rule selection changed local declarations"
  let result ← match outcome with
    | .ok result => pure result
    | .error error => throwError "native matrix rule was rejected: {error.reason}"
  result.toResult.check source #[]
  unless result.auxiliary?.isNone && result.rowPredicates.size == 1 &&
      result.certifiedRows.size == 1 do
    throwError "expected one cone row without auxiliary decisions"
  unless ← isDefEq result.rowPredicates[0]! expected do
    throwError "native matrix selection produced the wrong cone representation"
  let some row := result.certifiedRows[0]? | throwError "missing certified native matrix row"
  for proof in #[result.certificate.expression, result.targetIff,
      row.constraint, row.pointwiseIff] do
    checkCompleteWithKernel proof "incomplete native matrix representation certificate"

private meta def rejectAmbiguous (source : Expr) : MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let .error _ ← Morew.Elab.Cone.Rewrite.planUnique source
    | throwError "automatic selection suppressed a custom rule ambiguity"
  assertExprMVarStateUnchanged before "ambiguous native matrix selection"
  unless sameLocalDeclarationNames environment (← getEnv) do
    throwError "ambiguous native matrix selection changed local declarations"

/-- A custom alias remains an independent candidate beside the preferred built-in. -/
def customNativeEpigraph {n : Nat} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) :
    EpigraphRepr (fun x : Fin n → ℝ => x ⬝ᵥ (Q *ᵥ x)) :=
  Conic.QuadForm.nativeEpigraph Q hQ

private meta def checkBoth (ambiguous : Bool := false) : TermElabM Unit := do
  let expression ← elaborate (← `(fun (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ)
    (_hP : P.PosDef) (_hQ : (P⁻¹).PosSemidef) =>
    ((fun p : (Fin n → ℝ) × ℝ => p.1 ⬝ᵥ (P⁻¹ *ᵥ p.1) ≤ p.2),
     (fun p : (Fin n → ℝ) × ℝ =>
       (fromBlocksFin P (fun i (_ : Fin 1) => p.1 i) (fun _ : Fin 1 => p.1)
         (Matrix.diagonal (fun _ : Fin 1 => p.2))).PosSemidef),
     (fun p : (Fin n → ℝ) × ℝ =>
       (p.2, 1 / 2, Conic.QuadForm.factor P⁻¹ *ᵥ p.1) ∈ RSOC n))))
  lambdaBoundedTelescope expression 4 fun _ bodies => do
    let source ← whnf <| .proj ``Prod 0 bodies
    let targets ← whnf <| .proj ``Prod 1 bodies
    let psd ← whnf <| .proj ``Prod 0 targets
    let rsoc ← whnf <| .proj ``Prod 1 targets
    check source psd (some ``Conic.MatrixFraction.nativeEpigraph)
    check source rsoc (some ``Conic.QuadForm.nativeEpigraph)
    if ambiguous then
      check source rsoc (some ``customNativeEpigraph)
      rejectAmbiguous source
    else check source psd

run_cmd liftTermElabM checkBoth

-- Without a positive-definiteness proof, the certified quadratic rule remains available.
run_cmd liftTermElabM do
  let expression ← elaborate (← `(fun (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ)
    (_hQ : (P⁻¹).PosSemidef) =>
    ((fun p : (Fin n → ℝ) × ℝ => p.1 ⬝ᵥ (P⁻¹ *ᵥ p.1) ≤ p.2),
     (fun p : (Fin n → ℝ) × ℝ =>
       (p.2, 1 / 2, Conic.QuadForm.factor P⁻¹ *ᵥ p.1) ∈ RSOC n))))
  lambdaBoundedTelescope expression 3 fun _ bodies => do
    check (← whnf <| .proj ``Prod 0 bodies) (← whnf <| .proj ``Prod 1 bodies)

section CustomAmbiguity

attribute [local morew_conic] customNativeEpigraph

run_cmd liftTermElabM (checkBoth true)

end CustomAmbiguity

end MorewTest.Conic.MatFracPriority
