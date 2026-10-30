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

/-- PSD compact output hides the carrier conversion; detailed output recovers it. -/
def checkPSDDetails (declaration : Lean.Name) (proofName : String)
    (required : Array String := #[]) : Lean.Elab.Command.CommandElabM Unit := do
  let compact ← PrintDetails.printed declaration false
  let detailed ← PrintDetails.printed declaration true
  let compactAgain ← PrintDetails.printed declaration false
  unless compact == compactAgain do
    Lean.throwError "detailed PSD printing changed the next compact presentation"
  unless !compact.contains "SymmetricMatrix.ofMatrix" && !compact.contains proofName do
    Lean.throwError m!"compact PSD printing retained its carrier conversion or proof: {compact}"
  unless detailed.contains "SymmetricMatrix.ofMatrix" && detailed.contains proofName &&
      !detailed.contains "⋯" && compact != detailed do
    Lean.throwError m!"detailed PSD printing did not restore its carrier conversion and proof: {detailed}"
  for fragment in required do
    unless compact.contains fragment && detailed.contains fragment do
      Lean.throwError m!"PSD proof-detail selection changed mathematical syntax {fragment}:\n{compact}\n{detailed}"

noncomputable section

def diagonalSource :=
  problem (x : ℝ)
    let matrix := Matrix.diagonal ![x, 1]
    minimize x
    subject to
      semidefinite : matrix.PosSemidef
      upper : x ≤ 3

reformulation diagonalTarget : diagonalSource := by conic

set_option pp.proofs true in
reformulation diagonalRegisteredDetailed : diagonalSource := by conic

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
    semidefinite : matrix ∈ PSD 2
    upper : 3 - x ∈ ℝ₊
-/
#guard_msgs in
#printp diagonalTarget

run_cmd do
  checkPSDDetails ``diagonalTarget "diagonalTarget._proof_1" #["semidefinite", "matrix", "PSD 2"]
  checkPSDDetails ``diagonalRegisteredDetailed "_proof_1"
    #["semidefinite", "matrix", "PSD 2"]
  unless (← PrintDetails.printed ``diagonalTarget false) ==
      (← PrintDetails.printed ``diagonalRegisteredDetailed false) do
    Lean.throwError "registration-time pp.proofs changed compact PSD printing"

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

namespace MatrixHelpers
def diagonalHelper {n : Nat} (x : Fin n → ℝ) := Matrix.diagonal x

def source (n : Nat) :=
  problem (x : Fin n → ℝ)
    let matrix := diagonalHelper x + (diagonalHelper (-x)).transpose
    minimize ∑ i, x i
    subject to
      semidefinite : matrix.PosSemidef

variable (n : Nat)

reformulation target : (source n) := by conic

example : GlobalEquivalence (source n) (target n) := target.equivalence n
example : (target.conicForm n).data.toProblem = target n := (target.conicForm n).represents

run_cmd do
  let compact ← PrintDetails.printed ``target false
  unless compact.contains "diagonalHelper x" && compact.contains "matrix ∈ PSD n" do
    Lean.throwError m!"helper symmetry expansion changed the retained PSD spelling: {compact}"
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing helper PSD presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent `replayed) := $term))

example : replayed n = target n := rfl
end MatrixHelpers

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

/-- This target retains symmetric block constructors instead of a native matrix. -/
def blockSchurRule (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef) :
    ExactConstraintLift (fun p : Matrix (Fin 1) (Fin 1) ℝ × ℝ =>
      (Matrix.diagonal ![p.2] - p.1.transpose * A.toMatrix⁻¹ * p.1).PosSemidef) :=
  .ofIff (fun p => A.fromBlocks p.1
    (SymmetricMatrix.ofMatrix (Matrix.diagonal ![p.2]) (Matrix.isSymm_diagonal _)) ∈ PSD (1 + 1))
    (fun p => schurComplement_mem_iff A p.1
      (SymmetricMatrix.ofMatrix (Matrix.diagonal ![p.2]) (Matrix.isSymm_diagonal _)) hA)

reformulation blockSchur : (schurMaximumSource A) := by
  conic at schur using blockSchurRule
  conic

/--
info: problem (B : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ)
  maximize t
  subject to
    schur_conic_1 : A.fromBlocks B (Matrix.diagonal ![t]) ∈ PSD (1 + 1)
-/
#guard_msgs in
#printp blockSchur

-- Only an unused diagonal index becomes anonymous in compact PSD output.
def lambdaDiagonalSource (A : SymmetricMatrix 1) :=
  problem (B : Matrix (Fin 1) (Fin 2) ℝ) (d : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      constant : A.fromBlocks B
        (SymmetricMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin 2 => t))
          (Matrix.isSymm_diagonal _)) ∈ PSD (1 + 2)
      indexed : (Matrix.diagonal (fun i : Fin 2 => d i + t)).PosSemidef

reformulation lambdaDiagonals : (lambdaDiagonalSource A) := by conic

/--
info: problem (B : Matrix (Fin 1) (Fin 2) ℝ) (d : Fin 2 → ℝ) (t : ℝ)
  minimize t
  subject to
    constant : A.fromBlocks B (Matrix.diagonal fun _ => t) ∈ PSD (1 + 2)
    indexed : (Matrix.diagonal fun i => d i + t) ∈ PSD 2
-/
#guard_msgs in
#printp lambdaDiagonals

run_cmd do
  checkPSDDetails ``lambdaDiagonals "_proof_" #["constant", "indexed", "fun i => d i + t"]
  let detailed ← PrintDetails.printed ``lambdaDiagonals true
  unless detailed.contains "fun x => t" && !detailed.contains "fun _ => t" do
    Lean.throwError m!"compact diagonal formatting changed detailed lambda binders: {detailed}"

-- Both diagonal positions contain conversions, including inside another block.
def nestedBlockSource :=
  problem (x y z : ℝ)
    minimize x
    subject to
      semidefinite : (SymmetricMatrix.fromBlocks
        (SymmetricMatrix.fromBlocks
          (SymmetricMatrix.ofMatrix (Matrix.diagonal ![x]) (Matrix.isSymm_diagonal _))
          (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (SymmetricMatrix.ofMatrix (Matrix.diagonal ![y]) (Matrix.isSymm_diagonal _)))
        (0 : Matrix (Fin (1 + 1)) (Fin 1) ℝ)
        (SymmetricMatrix.ofMatrix (Matrix.diagonal ![z]) (Matrix.isSymm_diagonal _)))
          ∈ PSD ((1 + 1) + 1)

reformulation nestedBlocks : nestedBlockSource := by conic

-- Conversions outside a PSD coordinate keep their ordinary constructor syntax.
def ordinaryConversionSource :=
  problem (x : ℝ)
    let coordinate := SymmetricMatrix.ofMatrix (Matrix.diagonal ![x]) (Matrix.isSymm_diagonal _)
    minimize coordinate.toMatrix 0 0
    subject to
      upper : x ≤ 3

reformulation ordinaryConversion : ordinaryConversionSource := by conic

run_cmd do
  checkPSDDetails ``blockSchur "_proof_" #["A.fromBlocks B", "PSD (1 + 1)"]
  checkPSDDetails ``nestedBlocks "_proof_"
    #["Matrix.diagonal ![x]", "Matrix.diagonal ![y]", "Matrix.diagonal ![z]", "fromBlocks"]
  let ordinary ← PrintDetails.printed ``ordinaryConversion false
  unless ordinary.contains "let coordinate := SymmetricMatrix.ofMatrix" do
    Lean.throwError m!"compact PSD formatting changed an unrelated local definition: {ordinary}"

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
  unless printed.contains "semidefinite : matrix ∈ PSD 2" do
    Lean.throwError m!"terminal PSD printing lost its compact membership or retained name: {printed}"
  for (original, copied) in #[(``diagonalTarget, `diagonalReplay),
      (``diagonalRegisteredDetailed, `detailedReplay), (``blockSchur, `blockSchurReplay),
      (``nestedBlocks, `nestedBlocksReplay), (``lambdaDiagonals, `lambdaDiagonalsReplay)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "missing PSD presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))

example : diagonalReplay = diagonalTarget := rfl
example : detailedReplay = diagonalRegisteredDetailed := rfl
example : blockSchurReplay A = blockSchur A := rfl
example : nestedBlocksReplay = nestedBlocks := rfl
example : lambdaDiagonalsReplay A = lambdaDiagonals A := rfl

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
  checkPSDDetails ``target "hSym" #["semidefinite", "PSD 2"]
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

-- A constraint-local matrix let becomes a dependency of the generated symmetry
-- proof, even when its original native predicate used a nondependent binding.
def localLetSource :=
  problem (x : ℝ)
    minimize x
    subject to
      semidefinite : let matrix := Matrix.diagonal ![x, 1]; matrix.PosSemidef

reformulation localLetTarget : localLetSource := by conic

def localLetGroupSource :=
  problem (x : ℝ)
    minimize x
    subject to
      group :
        let scalar := x + 1
        let matrix := Matrix.diagonal ![scalar, 1]
        let _symmetric : matrix.IsSymm := Matrix.isSymm_diagonal _
        matrix.PosSemidef ∧ scalar ≤ 3

reformulation localLetGroupTarget : localLetGroupSource := by conic

example : GlobalEquivalence localLetSource localLetTarget := localLetTarget.equivalence
example : localLetTarget.conicForm.data.rowCount = 1 := rfl
example : localLetGroupTarget.conicForm.data.rowCount = 2 := rfl
example : localLetGroupTarget.conicForm.data.toProblem = localLetGroupTarget :=
  localLetGroupTarget.conicForm.represents

run_cmd do
  for (original, copied) in #[(``localLetTarget, `localLetReplay),
      (``localLetGroupTarget, `localLetGroupReplay)] do
    let compact ← PrintDetails.printed original false
    unless compact.contains "let matrix :=" && compact.contains "matrix ∈ PSD 2" do
      Lean.throwError m!"PSD normalization lost its constraint-local matrix binding: {compact}"
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "missing constraint-local PSD presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
  let detailed ← PrintDetails.printed ``localLetGroupTarget true
  unless detailed.contains "symmetric" && detailed.contains "scalar" &&
      detailed.contains "SymmetricMatrix.ofMatrix matrix" do
    Lean.throwError m!"PSD normalization lost its nested let or proof bindings: {detailed}"

example : localLetReplay = localLetTarget := rfl
example : localLetGroupReplay = localLetGroupTarget := rfl

-- Native membership and an ordinary predicate can be definitionally equal.
-- Their cached conversions must still follow each occurrence through True
-- leaves, local lets and retained group boundaries.
def mixedMembershipSource :=
  problem (x : ℝ)
    let matrix := Matrix.diagonal ![x]
    minimize x
    subject to
      semidefinite : True ∧
        (SymmetricMatrix.ofMatrix matrix (Matrix.isSymm_diagonal _) ∈ PSD 1 ∧
          matrix.PosSemidef)
      scalar : let value := x; (value ∈ (Cone.nonnegativeScalar).carrier ∧ True) ∧ 0 ≤ value

reformulation mixedMembershipTarget : mixedMembershipSource := by conic

example : GlobalEquivalence mixedMembershipSource mixedMembershipTarget :=
  mixedMembershipTarget.equivalence
example : mixedMembershipTarget.conicForm.data.rowCount = 4 := rfl
example : mixedMembershipTarget.conicForm.data.toProblem = mixedMembershipTarget :=
  mixedMembershipTarget.conicForm.represents

run_cmd do
  let compact ← PrintDetails.printed ``mixedMembershipTarget false
  unless !compact.contains "PosSemidef" && !compact.contains "0 ≤ value" &&
      compact.contains "matrix ∈ PSD 1" && compact.contains "value := x" do
    Lean.throwError m!"mixed native and ordinary predicates were not normalized: {compact}"
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``mixedMembershipTarget
    | Lean.throwError "missing mixed-membership presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) == #[`semidefinite, `scalar] do
    Lean.throwError "mixed-membership normalization changed retained groups"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent `mixedMembershipReplay) := $term))

example : mixedMembershipReplay = mixedMembershipTarget := rfl

end
end MorewTest.Reformulation.PositiveSemidefinite
