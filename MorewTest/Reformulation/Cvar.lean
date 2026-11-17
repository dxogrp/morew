/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.ElabSupport

/-! # CVaR bounds, objective lifts, and projection recovery -/

namespace MorewTest.Reformulation.Cvar

open Morew
open scoped Matrix

noncomputable section

def affineLosses (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :=
  A *ᵥ x - b

def riskValue (β : ℝ) (x : Fin n → ℝ) := Fn.cvar β x

open Lean Lean.Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (n : Nat) (β : ℝ)
    (x : Fin n → ℝ) => riskValue β x))
  lambdaBoundedTelescope expression 3 fun _ body => do
    let expanded ← Morew.Elab.Affine.Expansion.expand body fun value preserveLets =>
      Morew.Elab.Expr.reduceStructure value (preserveLets := preserveLets)
    unless expanded.isAppOf ``Fn.cvar do
      throwError "helper expansion did not preserve the CVaR atom"
    unless ← isDefEq expanded body do
      throwError "helper expansion changed the CVaR expression"
    MorewTest.checkCompleteWithKernel expanded "incomplete CVaR helper expansion"

def source (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (β : ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    let losses := affineLosses A b x
    minimize t
    subject to
      before : 0 ≤ x
      loss : Fn.cvar β losses ≤ t
      after : t ≤ 10

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (β : ℝ)
  (hm : 0 < m) (hβ : 0 ≤ β ∧ β < 1)

include hm hβ in
reformulation targeted : (source A b β) := by conic at loss

include hm hβ in
reformulation automatic : (source A b β) := by conic

include hm hβ in
reformulation named : (source A b β) := by
  conic at loss using Rewrite.cvarEpigraph
  conic

reformulation selected : (source A b β) := by
  conic at loss using (Rewrite.cvarEpigraph β hm hβ)
  conic

example : GlobalEquiv (source A b β) (targeted A b β) := targeted.equiv A b β hm hβ
example : GlobalEquiv (source A b β) (automatic A b β) := automatic.equiv A b β hm hβ
example : GlobalEquiv (source A b β) (named A b β) := named.equiv A b β hm hβ
example : GlobalEquiv (source A b β) (selected A b β) := selected.equiv A b β hm hβ
example : automatic A b β = selected A b β := rfl
example : automatic A b β = named A b β := rfl
example : IsConic (automatic A b β) := automatic.isConic A b β
example : (automatic.conicForm A b β).data.toProblem = automatic A b β :=
  (automatic.conicForm A b β).represents
example : (automatic.conicForm A b β).data.rowCount = 5 := rfl

example (x : Fin n → ℝ) (t τ : ℝ) (u : Fin m → ℝ) :
    (targeted A b β).objective ((x, t), τ, u) = t := rfl

example (x : Fin n → ℝ) (t τ : ℝ) (u : Fin m → ℝ) :
    (targeted A b β).feasible ((x, t), τ, u) ↔
      0 ≤ x ∧ 0 ≤ u ∧ A *ᵥ x - b - (fun _ => τ) ≤ u ∧
        τ + (∑ i, u i) / ((m : ℝ) * (1 - β)) ≤ t ∧ t ≤ 10 := Iff.rfl

example (p : FeasiblePoint (automatic A b β)) :
    ((automatic.equiv A b β hm hβ).backward.map p).val = p.val.1 := rfl

def objectiveSource (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (β : ℝ) :=
  problem (x : Fin n → ℝ)
    let losses := A *ᵥ x - b
    minimize Fn.cvar β losses

include hm hβ in
reformulation objectiveTarget : (objectiveSource A b β) := by
  epigraph t as loss
  conic

include hm hβ in
reformulation objectiveNamed : (objectiveSource A b β) := by
  epigraph t as loss
  conic at loss using Rewrite.cvarEpigraph
  conic

reformulation objectiveSelected : (objectiveSource A b β) := by
  epigraph t as loss
  conic at loss using (Rewrite.cvarEpigraph β hm hβ)
  conic

example : GlobalEquiv (objectiveSource A b β) (objectiveTarget A b β) :=
  objectiveTarget.equiv A b β hm hβ
example : GlobalEquiv (objectiveSource A b β) (objectiveNamed A b β) :=
  objectiveNamed.equiv A b β hm hβ
example : GlobalEquiv (objectiveSource A b β) (objectiveSelected A b β) :=
  objectiveSelected.equiv A b β hm hβ
example : objectiveTarget A b β = objectiveNamed A b β := rfl
example : objectiveTarget A b β = objectiveSelected A b β := rfl
example : IsConic (objectiveTarget A b β) := objectiveTarget.isConic A b β
example : (objectiveTarget.conicForm A b β).data.toProblem = objectiveTarget A b β :=
  (objectiveTarget.conicForm A b β).represents
example : (objectiveTarget.conicForm A b β).data.rowCount = 3 := rfl

example (x : Fin n → ℝ) (t τ : ℝ) (u : Fin m → ℝ) :
    (objectiveTarget A b β).objective ((x, t), τ, u) = t := rfl

example (p : FeasiblePoint (objectiveSource A b β)) :
    ((objectiveTarget.equiv A b β hm hβ).forward.map p).val.1 =
      (p.val, Fn.cvar β (A *ᵥ p.val - b)) := rfl

example (p : FeasiblePoint (objectiveTarget A b β)) :
    ((objectiveTarget.equiv A b β hm hβ).backward.map p).val = p.val.1.1 := rfl

example {p : FeasiblePoint (objectiveTarget A b β)}
    (hp : (objectiveTarget A b β).IsGlobalOptimum p) :
    (objectiveSource A b β).IsGlobalOptimum
      ((objectiveTarget.equiv A b β hm hβ).backward.map p) :=
  (objectiveTarget.equiv A b β hm hβ).map_isGlobalOptimum_backward hp

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``objectiveTarget
    | Lean.throwError "missing CVaR presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `objectiveReplay
  Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : objectiveReplay A b β = objectiveTarget A b β := rfl

def scenarios :=
  problem (x : ℝ)
    minimize Fn.cvar (1 / 2) ![x, 1 - x, 3 * x - 1]
    subject to
      lower : 0 ≤ x
      upper : x ≤ 1

reformulation scenarioTarget : scenarios := by
  epigraph t as risk
  conic

example : GlobalEquiv scenarios scenarioTarget := scenarioTarget.equiv
example : IsConic scenarioTarget := scenarioTarget.isConic
example : scenarioTarget.conicForm.data.toProblem = scenarioTarget :=
  scenarioTarget.conicForm.represents
example : scenarioTarget.conicForm.data.rowCount = 5 := rfl

example (p : FeasiblePoint scenarios) :
    (scenarioTarget.equiv.forward.map p).val.1 =
      (p.val, Fn.cvar (1 / 2) ![p.val, 1 - p.val, 3 * p.val - 1]) := rfl

example (p : FeasiblePoint scenarioTarget) :
    (scenarioTarget.equiv.backward.map p).val = p.val.1.1 := rfl

end
end MorewTest.Reformulation.Cvar
