/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Evidence
import MorewTest.ElabSupport
import MorewTest.Environment

/-! # Independent parameter evidence and supported proof forms -/

namespace MorewTest.Evidence

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
      let result ← Morew.Elab.Evidence.proveIndependent? points[0]! goal
      unless result.isSome == success do
        throwError "unexpected independent parameter evidence result for {goal}"
      assertMVarCountersUnchanged before "parameter evidence changed caller metavariables"
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

/-! Natural shape bounds use canonical order and the same independent proof scope. -/
run_cmd liftTermElabM do
  check (← `(fun (_ : ℝ) => (2 : Nat) ≤ 3)) 0 true
  check (← `(fun (_ : ℝ) => (3 : Nat) ≤ 2)) 0 false
  check (← `(fun (_ : ℝ) => (0 : Nat) ≤ 0)) 0 true
  check (← `(fun (n : Nat) (_ : ℝ) => 0 ≤ n)) 1 true
  check (← `(fun (n : Nat) (_ : ℝ) => n ≤ n)) 1 true
  check (← `(fun (k n : Nat) (_hk : k ≤ n) (_ : ℝ) => k ≤ n)) 3 true
  check (← `(fun (k n : Nat) (_hk : True ∧ k ≤ n) (_ : ℝ) => k ≤ n)) 3 true
  check (← `(fun (k n : Nat) (_ : ℝ) => k ≤ n)) 2 false
  check (← `(fun n : Nat => 0 ≤ n)) 0 false
  check (← `(fun (_ : ℝ) => @LE.le Nat ⟨fun _ _ => False⟩ 0 2)) 0 false

private def zeroAlias : Nat := 0
private def factorialAlias : Nat := Nat.factorial 1000
private def chooseAlias : Nat := Nat.choose 100 100

-- Zero and reflexive bounds do not require evaluating the factorial. Failed
-- reductions return no evidence and leave caller state unchanged.
run_cmd liftTermElabM do
  check (← `(fun (_ : ℝ) => (0 : Nat) ≤ Nat.factorial 1000)) 0 true
  check (← `(fun (_ : ℝ) => Nat.factorial 1000 ≤ Nat.factorial 1000)) 0 true
  check (← `(fun (_ : ℝ) => zeroAlias ≤ Nat.factorial 1000)) 0 true
  check (← `(fun (_ : ℝ) => factorialAlias ≤ Nat.factorial 1000)) 0 true
  check (← `(fun (_ : ℝ) => Nat.factorial 1000 ≤ factorialAlias)) 0 true
  check (← `(fun (_ : ℝ) => Nat.factorial 1000 ≤ 0)) 0 false

-- Zero reduction exhausts its local heartbeat allowance for these bounds, but
-- reflexivity through the alias needs only one unfolding.
run_cmd liftTermElabM do
  check (← `(fun (_ : ℝ) => chooseAlias ≤ Nat.choose 100 100)) 0 true
  check (← `(fun (_ : ℝ) => Nat.choose 100 100 ≤ chooseAlias)) 0 true

end MorewTest.Evidence
