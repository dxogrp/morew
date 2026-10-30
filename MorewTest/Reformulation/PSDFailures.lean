/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.PSD

/-!
# PSD diagnostic context and transactional failure
-/

namespace MorewTest.Reformulation.PositiveSemidefiniteFailures

open Morew Morew.Conic
open MorewTest.Reformulation.PositiveSemidefinite
noncomputable section

#guard_error_fragments ["type mismatch", "Fin 2", "Fin 3"] in
example (M : Matrix (Fin 2) (Fin 3) ℝ) : Prop := M.PosSemidef

#guard_error_fragments ["type mismatch", "Fin 2", "Fin 3"] in
example (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 3) ℝ)
    (C : Matrix (Fin 2) (Fin 2) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ) :=
  fromBlocksFin A B C D

elab "assert_psd_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  if let some name := MorewTest.newLocalDeclaration? before (← Lean.getEnv) then
    Lean.throwError m!"failed PSD conversion leaked declaration {name}"

def nonsymmetricSource :=
  problem (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize X 0 0
    subject to
      semidefinite : X.PosSemidef

#guard_error_fragments ["semidefinite", "global matrix symmetry"] in
assert_psd_atomic%
reformulation nonsymmetric : nonsymmetricSource := by conic

def nonlinearSource :=
  problem (x : ℝ)
    minimize x
    subject to
      semidefinite : (Matrix.diagonal ![x ^ 2, 1]).PosSemidef

#guard_error_fragments ["semidefinite", "PSD matrix entry or block"] in
assert_psd_atomic%
reformulation nonlinear : nonlinearSource := by conic

def nonlinearMembershipSource :=
  problem (x : ℝ)
    minimize x
    subject to
      semidefinite : SymmetricMatrix.ofMatrix (Matrix.diagonal ![x ^ 2, 1])
        (Matrix.isSymm_diagonal _) ∈ PSD 2

#guard_error_fragments ["semidefinite", "power"] in
assert_psd_atomic%
reformulation nonlinearMembership : nonlinearMembershipSource := by conic

def bilinearSource :=
  problem (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize X 0 0
    subject to
      semidefinite : (X.transpose * X).PosSemidef

#guard_error_fragments ["semidefinite", "both matrix factors"] in
assert_psd_atomic%
reformulation bilinear : bilinearSource := by conic

#guard_error_fragments ["unknown or stale constraint label `absent`"] in
assert_psd_atomic%
reformulation unknownLabel : diagonalSource := by conic at absent

namespace MissingPD
variable (A : SymmetricMatrix 1)

#guard_error_fragments ["schur", "positive-definiteness"] in
assert_psd_atomic%
reformulation missing : (schurSource A) := by
  conic at schur using schurRule
end MissingPD

namespace Polarity
def source (A : SymmetricMatrix 1) :=
  problem (B : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ)
    minimize t
    subject to
      schur : ¬ (Matrix.diagonal ![t] - B.transpose * A.toMatrix⁻¹ * B).PosSemidef

variable (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef)

#guard_error_fragments ["schur", "does not match"] in
assert_psd_atomic%
reformulation rejected : (source A) := by conic at schur using schurRule
end Polarity

namespace Ambiguity
def otherSchurRule (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef) := schurRule A hA
attribute [local morew_conic] schurRule otherSchurRule
variable (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef)

#guard_error_fragments ["ambiguous exact conic rules", "schurRule", "otherSchurRule"] in
assert_psd_atomic%
reformulation ambiguous : (schurSource A) := by conic at schur

reformulation selected : (schurSource A) := by
  conic at schur using schurRule
  conic

example : (selected.conicForm A).data.rowCount = 3 := rfl

#guard_error_fragments ["unknown or stale constraint label `schur`"] in
assert_psd_atomic%
reformulation stale : (schurSource A) := by
  conic at schur using schurRule
  conic at schur using schurRule
end Ambiguity

namespace DeclarationCollision
def target.conicForm : Nat := 17

#guard_error_fragments ["target.conicForm", "has already been declared"] in
assert_psd_atomic%
reformulation target : diagonalSource := by conic

example : target.conicForm = 17 := rfl
end DeclarationCollision

namespace Freshening
def source (A : SymmetricMatrix 1) :=
  problem (B : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ)
    minimize t
    subject to
      schur : (Matrix.diagonal ![t] - B.transpose * A.toMatrix⁻¹ * B).PosSemidef
      schur_conic_1 : t ≤ 5

variable (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef)

reformulation target : (source A) := by
  conic at schur using schurRule
  conic

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing collision-safe PSD presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) == #[`schur_conic_1_1, `schur_conic_1] do
    Lean.throwError "PSD generated rows did not preserve the existing label"

example : (target.conicForm A).data.rowCount = 2 := rfl
end Freshening

end
end MorewTest.Reformulation.PositiveSemidefiniteFailures
