/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.ElabSupport

/-!
# Matrix-quadratic reformulations

Both source spellings yield the same cone on an affine residual. Objective lifts
use the original quadratic value as the forward bound and recover the original
variables by projection.
-/

namespace MorewTest.Reformulation.QuadForm

open Morew Morew.Conic
open scoped Matrix

noncomputable section

def namedBound (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    let residual := A *ᵥ x + b
    minimize t
    subject to
      before : 0 ≤ x
      bound : Fn.quadForm residual Q ≤ t
      after : t ≤ 100

def nativeBound (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    let residual := A *ᵥ x + b
    minimize t
    subject to
      before : 0 ≤ x
      bound : t ≥ residual ⬝ᵥ (Q *ᵥ residual)
      after : t ≤ 100

def namedObjective (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    let residual := A *ᵥ x + b
    minimize Fn.quadForm residual Q

def nativeObjective (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    let residual := A *ᵥ x + b
    minimize residual ⬝ᵥ (Q *ᵥ residual)

variable (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ) (hQ : Q.PosSemidef)

include hQ in
reformulation namedAutomatic : (namedBound Q A b) := by conic

include hQ in
reformulation nativeAutomatic : (nativeBound Q A b) := by conic

reformulation namedExplicit : (namedBound Q A b) := by
  conic at bound using (Conic.QuadForm.epigraph Q hQ)
  conic

reformulation nativeExplicit : (nativeBound Q A b) := by
  conic at bound using (Conic.QuadForm.nativeEpigraph Q hQ)
  conic

example : GlobalEquiv (namedBound Q A b) (namedAutomatic Q A b) :=
  namedAutomatic.equiv Q A b hQ
example : GlobalEquiv (nativeBound Q A b) (nativeAutomatic Q A b) :=
  nativeAutomatic.equiv Q A b hQ
example : GlobalEquiv (namedBound Q A b) (namedExplicit Q A b) :=
  namedExplicit.equiv Q A b hQ
example : GlobalEquiv (nativeBound Q A b) (nativeExplicit Q A b) :=
  nativeExplicit.equiv Q A b hQ
example : namedAutomatic Q A b = namedExplicit Q A b := rfl
example : nativeAutomatic Q A b = nativeExplicit Q A b := rfl
example : namedAutomatic Q A b = nativeAutomatic Q A b := rfl
example : IsConic (namedAutomatic Q A b) := namedAutomatic.isConic Q A b
example : IsConic (nativeAutomatic Q A b) := nativeAutomatic.isConic Q A b
example : (namedAutomatic.conicForm Q A b).data.toProblem = namedAutomatic Q A b :=
  (namedAutomatic.conicForm Q A b).represents
example : (nativeAutomatic.conicForm Q A b).data.toProblem = nativeAutomatic Q A b :=
  (nativeAutomatic.conicForm Q A b).represents
example : (namedAutomatic.conicForm Q A b).data.rowCount = 3 := rfl

example (x : Fin n → ℝ) (t : ℝ) : (namedAutomatic Q A b).objective (x, t) = t := rfl

example (x : Fin n → ℝ) (t : ℝ) : (namedAutomatic Q A b).feasible (x, t) ↔
    0 ≤ x ∧ (t, 1 / 2, Conic.QuadForm.factor Q *ᵥ (A *ᵥ x + b)) ∈ RSOC m ∧
      t ≤ 100 := by
  change (0 ≤ x ∧ (t, 1 / 2, Conic.QuadForm.factor Q *ᵥ (A *ᵥ x + b)) ∈ RSOC m ∧
    0 ≤ 100 - t) ↔ _
  rw [sub_nonneg]

example (p : FeasiblePoint (namedAutomatic Q A b)) :
    ((namedAutomatic.equiv Q A b hQ).backward.map p).val = p.val := rfl

include hQ in
reformulation namedLift : (namedObjective Q A b) := by
  epigraph t
  conic

include hQ in
reformulation nativeLift : (nativeObjective Q A b) := by
  epigraph t
  conic

reformulation namedLiftExplicit : (namedObjective Q A b) := by
  epigraph t
  conic at epigraph_t using (Conic.QuadForm.epigraph Q hQ)
  conic

reformulation nativeLiftExplicit : (nativeObjective Q A b) := by
  epigraph t
  conic at epigraph_t using (Conic.QuadForm.nativeEpigraph Q hQ)
  conic

example : GlobalEquiv (namedObjective Q A b) (namedLift Q A b) := namedLift.equiv Q A b hQ
example : GlobalEquiv (nativeObjective Q A b) (nativeLift Q A b) := nativeLift.equiv Q A b hQ
example : GlobalEquiv (namedObjective Q A b) (namedLiftExplicit Q A b) :=
  namedLiftExplicit.equiv Q A b hQ
example : GlobalEquiv (nativeObjective Q A b) (nativeLiftExplicit Q A b) :=
  nativeLiftExplicit.equiv Q A b hQ
example : namedLift Q A b = namedLiftExplicit Q A b := rfl
example : nativeLift Q A b = nativeLiftExplicit Q A b := rfl
example : namedLift Q A b = nativeLift Q A b := rfl
example : IsConic (namedLift Q A b) := namedLift.isConic Q A b
example : IsConic (nativeLift Q A b) := nativeLift.isConic Q A b
example : (namedLift.conicForm Q A b).data.toProblem = namedLift Q A b :=
  (namedLift.conicForm Q A b).represents
example : (nativeLift.conicForm Q A b).data.toProblem = nativeLift Q A b :=
  (nativeLift.conicForm Q A b).represents
example : (namedLift.conicForm Q A b).data.rowCount = 1 := rfl

example (x : Fin n → ℝ) (t : ℝ) : (namedLift Q A b).objective (x, t) = t := rfl

example (x : Fin n → ℝ) (t : ℝ) : (namedLift Q A b).feasible (x, t) ↔
    (t, 1 / 2, Conic.QuadForm.factor Q *ᵥ (A *ᵥ x + b)) ∈ RSOC m := Iff.rfl

example (p : FeasiblePoint (namedObjective Q A b)) :
    ((namedLift.equiv Q A b hQ).forward.map p).val =
      (p.val, Fn.quadForm (A *ᵥ p.val + b) Q) := rfl

example (p : FeasiblePoint (nativeObjective Q A b)) :
    ((nativeLift.equiv Q A b hQ).forward.map p).val =
      (p.val, (A *ᵥ p.val + b) ⬝ᵥ (Q *ᵥ (A *ᵥ p.val + b))) := rfl

example (p : FeasiblePoint (namedLift Q A b)) :
    ((namedLift.equiv Q A b hQ).backward.map p).val = p.val.1 := rfl

example (p : FeasiblePoint (nativeLift Q A b)) :
    ((nativeLift.equiv Q A b hQ).backward.map p).val = p.val.1 := rfl

example {p : FeasiblePoint (namedLift Q A b)} (hp : (namedLift Q A b).IsGlobalOptimum p) :
    (namedObjective Q A b).IsGlobalOptimum ((namedLift.equiv Q A b hQ).backward.map p) :=
  (namedLift.equiv Q A b hQ).map_isGlobalOptimum_backward hp

private def singular : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]
private theorem singularPSD : singular.PosSemidef :=
  Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)

example : GlobalEquiv (namedObjective singular (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 2])
    (namedLift singular (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 2]) :=
  namedLift.equiv _ _ _ singularPSD

example : (namedLift singular (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 2]).feasible (![2, 3], 9) := by
  change (9, 1 / 2, Conic.QuadForm.factor singular *ᵥ
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![2, 3] + ![1, 2])) ∈ RSOC 2
  rw [← Conic.QuadForm.quadForm_le_iff _ _ singularPSD]
  norm_num [Fn.quadForm, singular, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

example : GlobalEquiv (nativeObjective (0 : Matrix (Fin m) (Fin m) ℝ) A b)
    (nativeLift 0 A b) := nativeLift.equiv _ _ _ Matrix.PosSemidef.zero

example (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ) (x : Fin n → ℝ) (t : ℝ) :
    (namedLift (0 : Matrix (Fin 0) (Fin 0) ℝ) A b).feasible (x, t) ↔ 0 ≤ t := by
  change (t, 1 / 2, Conic.QuadForm.factor 0 *ᵥ (A *ᵥ x + b)) ∈ RSOC 0 ↔ 0 ≤ t
  rw [← Conic.QuadForm.quadForm_le_iff _ _ Matrix.PosSemidef.zero]
  simp

example (A : Matrix (Fin m) (Fin 0) ℝ) : IsConic (nativeLift Q A b) :=
  nativeLift.isConic Q A b

-- Stored cone syntax re-elaborates without exposing the matrix-square-root construction.
run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``namedLift
    | Lean.throwError "missing matrix-quadratic presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `namedLiftCopy
  Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : namedLiftCopy Q A b = namedLift Q A b := rfl

end
end MorewTest.Reformulation.QuadForm
