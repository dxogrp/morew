/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics
import MorewTest.Environment
import MorewTest.Reformulation.PrintDetails

/-!
# PSD memberships through exact reformulation workflows

Native predicates become actual symmetric-cone memberships. Schur certificates
use the ordinary explicit and locally registered exact-rule interfaces.
-/

namespace MorewTest.Reformulation.PositiveSemidefinite

open Morew Morew.Conic
noncomputable section

def diagonalSource :=
  problem (x : ℝ)
    let matrix := Matrix.diagonal ![x, 1]
    minimize x
    subject to
      semidefinite : matrix.PosSemidef
      upper : x ≤ 3

reformulation diagonalTarget : diagonalSource := by conic

example : GlobalEquivalence diagonalSource diagonalTarget := diagonalTarget.equivalence
example : IsConic diagonalTarget := diagonalTarget.isConic
example : diagonalTarget.conicForm.data.toProblem = diagonalTarget :=
  diagonalTarget.conicForm.represents
example : diagonalTarget.conicForm.data.rowCount = 2 := rfl
example (x : ℝ) : diagonalTarget.feasible x ↔
    SymmetricMatrix.ofMatrix (Matrix.diagonal ![x, 1]) (Matrix.isSymm_diagonal _) ∈ PSD 2 ∧
      3 - x ∈ (Cone.nonnegativeScalar).carrier := Iff.rfl

/--
info: problem (x : ℝ)
  let matrix := Matrix.diagonal ![x, 1]
  minimize x
  subject to
    semidefinite : matrix.PosSemidef
    upper : x ≤ 3
-/
#guard_msgs in
#printp diagonalSource

/--
info: problem (x : ℝ)
  let matrix := Matrix.diagonal ![x, 1]
  minimize x
  subject to
    semidefinite : SymmetricMatrix.ofMatrix matrix ⋯ ∈ PSD 2
    upper : 3 - x ∈ ℝ₊
-/
#guard_msgs in
#printp diagonalTarget

/--
info: problem (x : ℝ)
  let matrix := Matrix.diagonal ![x, 1]
  minimize x
  subject to
    semidefinite : SymmetricMatrix.ofMatrix matrix (diagonalTarget._proof_1 x) ∈ PSD 2
    upper : 3 - x ∈ ℝ₊
-/
#guard_msgs in
set_option pp.proofs true in
#printp diagonalTarget

def maximumSource :=
  problem (x : ℝ)
    maximize x
    subject to
      semidefinite : (Matrix.diagonal ![x, 1]).PosSemidef

reformulation maximumTarget : maximumSource := by conic
example : maximumTarget.conicForm.data.sense = ObjectiveSense.maximize := rfl
example : GlobalEquivalence maximumSource maximumTarget := maximumTarget.equivalence

def symmetricDecisionSource :=
  problem (M : SymmetricMatrix 2)
    minimize M.toMatrix 0 0
    subject to
      semidefinite : M ∈ PSD 2

reformulation symmetricDecisionTarget : symmetricDecisionSource := by conic
example : symmetricDecisionTarget.conicForm.data.toProblem = symmetricDecisionTarget :=
  symmetricDecisionTarget.conicForm.represents

/-- A reusable exact certificate, with no global automatic registration. -/
def schurRule (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef) :
    ExactConstraintLift (fun p : Matrix (Fin 1) (Fin 1) ℝ × ℝ =>
      (Matrix.diagonal ![p.2] - p.1.transpose * A.toMatrix⁻¹ * p.1).PosSemidef) :=
  .ofIff (fun p =>
    (fromBlocksFin A.toMatrix p.1 p.1.transpose (Matrix.diagonal ![p.2])).PosSemidef) (by
      intro p
      simpa only [Cone.mem_positiveSemidefinite, SymmetricMatrix.toMatrix_fromBlocks,
        SymmetricMatrix.toMatrix_ofMatrix] using
        schurComplement_mem_iff A p.1
          (SymmetricMatrix.ofMatrix (Matrix.diagonal ![p.2]) (Matrix.isSymm_diagonal _)) hA)

def schurSource (A : SymmetricMatrix 1) :=
  problem (B : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ)
    minimize t
    subject to
      schur : (Matrix.diagonal ![t] - B.transpose * A.toMatrix⁻¹ * B).PosSemidef
      remaining : |t| ≤ 5

def schurMaximumSource (A : SymmetricMatrix 1) :=
  problem (B : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ)
    maximize t
    subject to
      schur : (Matrix.diagonal ![t] - B.transpose * A.toMatrix⁻¹ * B).PosSemidef

variable (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef)

reformulation schurSelected : (schurSource A) := by
  conic at schur using schurRule

reformulation schurReady : (schurSelected A) := by conic

example : GlobalEquivalence (schurSource A) (schurReady A) :=
  (schurSelected.equivalence A hA).trans (schurReady.equivalence A)
example : (schurReady.conicForm A).data.toProblem = schurReady A :=
  (schurReady.conicForm A).represents
example : (schurReady.conicForm A).data.rowCount = 3 := rfl

reformulation schurMaximum : (schurMaximumSource A) := by
  conic at schur using schurRule
  conic

example : (schurMaximum.conicForm A).data.sense = ObjectiveSense.maximize := rfl

def rightSchurRule (D : SymmetricMatrix 1) (hD : D.toMatrix.PosDef) :
    ExactConstraintLift (fun p : Matrix (Fin 1) (Fin 1) ℝ × ℝ =>
      (Matrix.diagonal ![p.2] - p.1 * D.toMatrix⁻¹ * p.1.transpose).PosSemidef) :=
  .ofIff (fun p =>
    (fromBlocksFin (Matrix.diagonal ![p.2]) p.1 p.1.transpose D.toMatrix).PosSemidef) (by
      intro p
      simpa only [Cone.mem_positiveSemidefinite, SymmetricMatrix.toMatrix_fromBlocks,
        SymmetricMatrix.toMatrix_ofMatrix] using
        schurComplement_mem_iff_right
          (SymmetricMatrix.ofMatrix (Matrix.diagonal ![p.2]) (Matrix.isSymm_diagonal _))
          p.1 D hD)

def rightSchurSource (D : SymmetricMatrix 1) :=
  problem (B : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ)
    minimize t
    subject to
      schur : (Matrix.diagonal ![t] - B * D.toMatrix⁻¹ * B.transpose).PosSemidef

reformulation rightSchurReady : (rightSchurSource A) := by
  conic at schur using rightSchurRule
  conic

example : GlobalEquivalence (rightSchurSource A) (rightSchurReady A) :=
  rightSchurReady.equivalence A hA
example : (rightSchurReady.conicForm A).data.rowCount = 1 := rfl

section Registered
attribute [local morew_conic] schurRule

reformulation schurRegistered : (schurSource A) := by
  conic at schur
  conic

example : (schurRegistered.conicForm A).data.rowCount = 3 := rfl
end Registered

-- A retained certified PSD row must keep its global symmetry witness when an
-- unrelated logarithmic sum introduces an auxiliary decision vector.
def auxiliarySource :=
  problem (x t : ℝ)
    let matrix := Matrix.diagonal ![x, 1]
    minimize t
    subject to
      semidefinite : matrix.PosSemidef
      sum : Fn.logSumExp ![x, -x] ≤ t

reformulation auxiliaryTarget : auxiliarySource := by conic

example : GlobalEquivalence auxiliarySource auxiliaryTarget := auxiliaryTarget.equivalence
example : auxiliaryTarget.conicForm.data.toProblem = auxiliaryTarget :=
  auxiliaryTarget.conicForm.represents

run_cmd do
  let printed ← PrintDetails.printed ``diagonalTarget false
  unless printed.contains "semidefinite" && printed.contains "matrix" &&
      printed.contains "SymmetricMatrix.ofMatrix" && printed.contains "PSD 2" do
    Lean.throwError m!"terminal PSD printing lost its matrix conversion or retained name: {printed}"
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``diagonalTarget
    | Lean.throwError "missing PSD presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent `diagonalReplay) := $term))

example : diagonalReplay = diagonalTarget := rfl

namespace GlobalEvidence
def source (C D : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : ℝ)
    minimize x
    subject to
      semidefinite : (C + x • D).PosSemidef

variable (C D : Matrix (Fin 2) (Fin 2) ℝ)
  (hSym : ∀ x : ℝ, (C + x • D).IsSymm)

reformulation target : (source C D) := by conic

example : GlobalEquivalence (source C D) (target C D hSym) := target.equivalence C D hSym
example : (target.conicForm C D hSym).data.toProblem = target C D hSym :=
  (target.conicForm C D hSym).represents

run_cmd do
  PrintDetails.checkDetails ``target "hSym" #["semidefinite", "PSD 2"]
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing global-symmetry PSD presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent `replayed) := $term))

example : replayed C D hSym = target C D hSym := rfl
end GlobalEvidence

def substitutionSource :=
  problem (x : ℝ)
    let a := Real.log x
    let witness : a = Real.log x := rfl
    let matrix := Matrix.diagonal ![a, 1]
    minimize a
    subject to
      positive : 0 < x
      semidefinite : matrix.PosSemidef

reformulation substituted : substitutionSource := by
  substitute x := Real.exp u
  conic

example : GlobalEquivalence substitutionSource substituted := substituted.equivalence
example : substituted.conicForm.data.toProblem = substituted := substituted.conicForm.represents

end
end MorewTest.Reformulation.PositiveSemidefinite
