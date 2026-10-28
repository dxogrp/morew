/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.Support

/-!
# Registered scalar-power rules

Every spelling passes the same unique-success search and kernel-checked target
certification. Retained rows supply only the base-domain premises; independent
parameters supply exponent ranges.
-/

namespace MorewTest.Conic.PowerRules

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew MorewTest.Affine

private def check (term : TSyntax `term) (rows : Nat) (parameters : Nat := 0)
    (name? : Option Name := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ pair => do
    let source ← Morew.Elab.Expr.reduceStructure (mkProj ``Prod 0 pair)
    let retained ← Morew.Elab.Expr.reduceStructure (mkProj ``Prod 1 pair)
    let before ← getMCtx
    let result ← match name? with
      | some name => Morew.Elab.Conic.Rewrite.planDeclaration source name #[retained]
      | none => Morew.Elab.Conic.Rewrite.planUnique source #[retained]
    let .ok result := result
      | match result with
        | .error error => throwError "power rule failed: {error.reason}"
        | .ok _ => throwError "unreachable"
    unless before.mvarCounter == (← getMCtx).mvarCounter &&
        before.lmvarCounter == (← getMCtx).lmvarCounter do
      throwError "power rule leaked scratch metavariables"
    result.toResult.check source #[retained]
    unless result.rowPredicates.size == rows && result.certifiedRows.size == rows do
      throwError "wrong number of power-rule rows"
    unless result.auxiliary?.isSome == (rows == 3) do
      throwError "wrong power-rule auxiliary layout"
    checkWithKernel result.certificate.expression
    for row in result.certifiedRows do
      checkWithKernel row.constraint
      checkWithKernel row.pointwiseIff

run_cmd liftTermElabM do
  check (← `(((fun x : ℝ × ℝ => Real.rpow x.1 (3 / 2) ≤ x.2),
    (fun x : ℝ × ℝ => 0 ≤ x.1)))) 1
  check (← `(((fun x : ℝ × ℝ => x.1 ^ (3 / 2 : ℝ) ≤ x.2),
    (fun x : ℝ × ℝ => 0 ≤ x.1)))) 1
  check (← `(((fun x : ℝ × ℝ => Real.rpow x.1 (-2) ≤ x.2),
    (fun x : ℝ × ℝ => 1 ≤ x.1)))) 1
  check (← `(((fun x : ℝ × ℝ => x.1 ^ (-2 : ℝ) ≤ x.2),
    (fun x : ℝ × ℝ => 1 ≤ x.1)))) 1
  check (← `(((fun x : ℝ × ℝ => x.2 ≤ Real.rpow x.1 (1 / 3)),
    (fun x : ℝ × ℝ => 0 ≤ x.1)))) 3
  check (← `(((fun x : ℝ × ℝ => x.2 ≤ x.1 ^ (1 / 3 : ℝ)),
    (fun x : ℝ × ℝ => 0 ≤ x.1)))) 3

-- Both native spellings in either factor remain disjoint registry candidates.
run_cmd liftTermElabM do
  check (← `(((fun x : ℝ × ℝ × ℝ =>
    x.2.2 ≤ Real.rpow x.1 (1 / 3) * Real.rpow x.2.1 (1 - 1 / 3)),
    (fun x : ℝ × ℝ × ℝ => 0 ≤ x.1 ∧ 0 ≤ x.2.1)))) 3
  check (← `(((fun x : ℝ × ℝ × ℝ =>
    x.2.2 ≤ x.1 ^ (1 / 3 : ℝ) * x.2.1 ^ (1 - 1 / 3 : ℝ)),
    (fun x : ℝ × ℝ × ℝ => 0 ≤ x.1 ∧ 0 ≤ x.2.1)))) 3
  check (← `(((fun x : ℝ × ℝ × ℝ =>
    x.2.2 ≤ x.1 ^ (1 / 3 : ℝ) * Real.rpow x.2.1 (1 - 1 / 3)),
    (fun x : ℝ × ℝ × ℝ => 0 ≤ x.1 ∧ 0 ≤ x.2.1)))) 3
  check (← `(((fun x : ℝ × ℝ × ℝ =>
    x.2.2 ≤ Real.rpow x.1 (1 / 3) * x.2.1 ^ (1 - 1 / 3 : ℝ)),
    (fun x : ℝ × ℝ × ℝ => 0 ≤ x.1 ∧ 0 ≤ x.2.1)))) 3

-- Ranges may be symbolic and supplied separately or in a conjunction.
run_cmd liftTermElabM do
  check (← `(fun (p : ℝ) (_hp : 1 < p) =>
    ((fun x : ℝ × ℝ => Real.rpow x.1 p ≤ x.2),
     (fun x : ℝ × ℝ => 0 ≤ x.1)))) 1 2
  check (← `(fun (p : ℝ) (_hp : p < 0) =>
    ((fun x : ℝ × ℝ => Real.rpow x.1 p ≤ x.2),
     (fun x : ℝ × ℝ => 1 ≤ x.1)))) 1 2
  check (← `(fun (p : ℝ) (_hp : 0 < p ∧ p < 1) =>
    ((fun x : ℝ × ℝ => x.2 ≤ Real.rpow x.1 p),
     (fun x : ℝ × ℝ => 0 ≤ x.1)))) 3 2
  check (← `(fun (p : ℝ) (_hp : 0 < p) (_hp' : p < 1) =>
    ((fun x : ℝ × ℝ => x.2 ≤ x.1 ^ p),
     (fun x : ℝ × ℝ => 0 ≤ x.1)))) 3 3
  check (← `(fun (_hp : 1 < Real.sqrt 2) =>
    ((fun x : ℝ × ℝ => Real.rpow x.1 (Real.sqrt 2) ≤ x.2),
     (fun x : ℝ × ℝ => 0 ≤ x.1)))) 1 1

-- Endpoint records work without retained base signs, including nonlinear bases at zero.
run_cmd liftTermElabM do
  check (← `(((fun x : ℝ × ℝ => Real.rpow (Real.exp x.1) 0 ≤ x.2),
    (fun _ : ℝ × ℝ => True)))) 1
  check (← `(((fun x : ℝ × ℝ => x.2 ≤ Real.rpow (Real.exp x.1) 0),
    (fun _ : ℝ × ℝ => True)))) 1
  check (← `(((fun x : ℝ × ℝ => Real.rpow x.1 1 ≤ x.2),
    (fun _ : ℝ × ℝ => True)))) 1
  check (← `(((fun x : ℝ × ℝ => x.2 ≤ Real.rpow x.1 1),
    (fun _ : ℝ × ℝ => True)))) 1
  check (← `(((fun x : ℝ × ℝ => (Real.exp x.1) ^ (0 : ℝ) ≤ x.2),
    (fun _ : ℝ × ℝ => True)))) 1
  check (← `(((fun x : ℝ × ℝ => x.2 ≤ (Real.exp x.1) ^ (0 : ℝ)),
    (fun _ : ℝ × ℝ => True)))) 1
  check (← `(((fun x : ℝ × ℝ => x.1 ^ (1 : ℝ) ≤ x.2),
    (fun _ : ℝ × ℝ => True)))) 1
  check (← `(((fun x : ℝ × ℝ => x.2 ≤ x.1 ^ (1 : ℝ)),
    (fun _ : ℝ × ℝ => True)))) 1

-- Explicit selection reports the exact unsatisfied exponent condition.
private def checkMissingRange (term : TSyntax `term) (rule : Name) (required : String) :
    TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression 1 fun _ source => do
    let .error error ← Morew.Elab.Conic.Rewrite.planDeclaration source rule
      | throwError "a power range without evidence was accepted"
    let text := (← error.reason.toString).replace "\n" " " |>.replace "✝" ""
    let text := String.intercalate " " (text.splitOn " " |>.filter (!·.isEmpty))
    unless text.contains required do
      throwError "power-range diagnostic lost its required proposition: {error.reason}"

run_cmd liftTermElabM do
  checkMissingRange (← `(fun (p : ℝ) => fun t : ℝ => Real.rpow 2 p ≤ t))
    ``Morew.Conic.Power.rpowEpigraph "required 1 < p"
  checkMissingRange (← `(fun (p : ℝ) => fun t : ℝ => Real.rpow 2 p ≤ t))
    ``Morew.Conic.Power.rpowNegativeEpigraph "required p < 0"
  checkMissingRange (← `(fun (p : ℝ) => fun t : ℝ => t ≤ Real.rpow 2 p))
    ``Morew.Conic.Power.rpowHypograph "required 0 < p ∧ p < 1"

end MorewTest.Conic.PowerRules
