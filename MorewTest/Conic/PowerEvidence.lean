/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Evidence
import MorewTest.Affine.Support
import MorewTest.Environment

/-! # Independent exponent evidence and its deliberately bounded policy -/

namespace MorewTest.Conic.PowerEvidence

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open MorewTest.Affine

private def check (term : TSyntax `term) (parameters : Nat) (success : Bool) :
    TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ source => do
    lambdaTelescope source fun points goal => do
      unless points.size == 1 do throwError "expected one decision point"
      let before ← getMCtx
      let environment ← getEnv
      let result ← Morew.Elab.Conic.Evidence.proveIndependent? points[0]! goal
      unless result.isSome == success do
        throwError "unexpected independent exponent evidence result for {goal}"
      unless before.mvarCounter == (← getMCtx).mvarCounter &&
          before.lmvarCounter == (← getMCtx).lmvarCounter do
        throwError "parameter evidence changed caller metavariables"
      if let some proof := result then
        checkWithKernel proof
        unless ← isDefEq (← inferType proof) goal do throwError "evidence proves the wrong goal"
      else if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
        throwError "failed parameter evidence leaked declaration {name}"

run_cmd liftTermElabM do
  check (← `(fun (_ : ℝ) => (0 : ℝ) < 1 / 3 ∧ (1 / 3 : ℝ) < 1)) 0 true
  check (← `(fun (_ : ℝ) => (1 : ℝ) < 3 / 2)) 0 true
  check (← `(fun (_ : ℝ) => (-2 : ℝ) < 0)) 0 true
  check (← `(fun (_ : ℝ) => (1 : ℝ) < 1)) 0 false
  check (← `(fun (p : ℝ) (_hp : 1 < p) (_ : ℝ) => 1 < p)) 2 true
  check (← `(fun (p : ℝ) (_hp : 0 < p ∧ p < 1) (_ : ℝ) => p < 1)) 2 true
  check (← `(fun (p : ℝ) (_hp : True ∧ (0 < p ∧ p < 1)) (_ : ℝ) => 0 < p)) 2 true
  check (← `(fun (p : ℝ) (_hp : 0 < p) (_hp' : p < 1) (_ : ℝ) => 0 < p ∧ p < 1)) 3 true
  check (← `(fun (p : ℝ) (_hp : 2 < p) (_ : ℝ) => 1 < p)) 2 false
  check (← `(fun (p : ℝ) (_hp : p < 0) (_ : ℝ) => p < 1)) 2 false
  check (← `(fun (p : ℝ) (_ : ℝ) => 0 < p)) 1 false
  check (← `(fun x : ℝ => 0 < x)) 0 false

end MorewTest.Conic.PowerEvidence
