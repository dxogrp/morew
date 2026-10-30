/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Affine.Support
import Morew.Elab.Conic.Symmetry

/-!
# Checked global symmetry and direct PSD rows

Symmetry certificates must hold for every decision point. Independent universal
and entrywise hypotheses are accepted; feasibility-local evidence and incomplete
proofs are rejected without changing caller metavariables. Row certificates keep
the original ordinary matrix predicate exactly.
-/

namespace MorewTest.Conic.PositiveSemidefiniteElab

open Lean Lean.Meta Lean.Elab.Term
open Morew.Conic MorewTest.Affine

private def checkUnchanged (before : MetavarContext) : MetaM Unit := do
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "symmetry recognition leaked scratch metavariables"
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "symmetry recognition changed a caller assignment"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "symmetry recognition assigned an unresolved caller metavariable"

private def assertSymmetry (term : TSyntax `term) (parameters : Nat := 0)
    (accepted : Bool := true) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ source => do
    lambdaTelescope source fun points matrix => do
      unless points.size == 1 do throwError "symmetry test needs one decision binder"
      let unresolved ← mkFreshExprMVar (mkConst ``Nat)
      let assigned ← mkFreshExprMVar (mkConst ``Nat)
      assigned.mvarId!.assign (mkNatLit 7)
      let before ← getMCtx
      let messagesBefore ← Core.getMessageLog
      let proof ← Morew.Elab.Conic.Symmetry.prove? points[0]! matrix
      checkUnchanged before
      unless (← Core.getMessageLog).toList.length == messagesBefore.toList.length do
        throwError "symmetry recognition leaked tactic diagnostics"
      unless proof.isSome == accepted do
        throwError "unexpected global symmetry result for {matrix}: {proof.isSome}"
      if let some proof := proof then
        if proof.hasMVar || proof.hasSorry then throwError "incomplete symmetry certificate"
        checkWithKernel proof
        let expected ← mkForallFVars points (← mkAppM ``Matrix.IsSymm #[matrix])
        unless ← isDefEq (← inferType proof) expected do
          throwError "symmetry certificate proves the wrong statement"
      if ← unresolved.mvarId!.isAssigned then throwError "assigned unrelated caller metavariable"
      unless (← instantiateMVars assigned) == mkNatLit 7 do
        throwError "discarded unrelated caller assignment"

/-! Universal hypotheses do not need separately symmetric affine coefficients. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSymmetry (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ x, (F x).IsSymm) => fun x : ℝ => F x)) 3
  assertSymmetry (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ x i j, F x j i = F x i j) => fun x : ℝ => F x)) 3
  assertRow (← `(fun (n : Nat) (A B : Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ x : ℝ, (A + x • B).IsSymm) =>
    fun x : ℝ => (A + x • B).PosSemidef)) 4
  assertRow (← `(fun (n : Nat) (A B : Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ (x : ℝ) i j, (A + x • B) j i = (A + x • B) i j) =>
    fun x : ℝ => (A + x • B).PosSemidef)) 4
  assertSymmetry (← `(fun (n : Nat) (A B : Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ (x : ℝ) i j, A j i + x * B j i = A i j + x * B i j) =>
    fun x : ℝ => Matrix.of (fun i j => A i j + x * B i j))) 4
  assertRow (← `(fun (n : Nat) (A B : Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ (x : ℝ) i j, A j i + x * B j i = A i j + x * B i j) =>
    fun x : ℝ => (Matrix.of (fun i j => A i j + x * B i j)).PosSemidef)) 4

/-! Structural rules preserve ordinary matrix expressions and symbolic sizes. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSymmetry (← `(fun n : Nat => fun x : Fin n → ℝ => Matrix.diagonal x)) 1
  assertSymmetry (← `(fun (n : Nat) (A : Matrix (Fin n) (Fin n) ℝ) (_h : A.IsSymm) =>
    fun x : Fin n → ℝ => A + Matrix.diagonal x)) 3
  assertSymmetry (← `(fun (n : Nat) (A : Matrix (Fin n) (Fin n) ℝ) (_h : A.IsSymm) =>
    fun x : Fin n → ℝ => A - Matrix.diagonal x)) 3
  assertSymmetry (← `(fun n : Nat => fun x : Fin n → ℝ => -Matrix.diagonal x)) 1
  assertSymmetry (← `(fun (n : Nat) (c : ℝ) =>
    fun x : Fin n → ℝ => c • Matrix.diagonal x)) 2
  assertSymmetry (← `(fun n : Nat =>
    fun x : Fin n → ℝ => (Matrix.diagonal x).transpose)) 1
  assertSymmetry (← `(fun n : Nat =>
    fun x : Matrix (Fin n) (Fin n) ℝ => x + x.transpose)) 1
  assertSymmetry (← `(fun n : Nat => fun x : SymmetricMatrix n => x.toMatrix)) 1
  assertSymmetry (← `(fun (m n : Nat) (C : Matrix (Fin m) (Fin n) ℝ) =>
    fun x : Fin m → ℝ => C.transpose * Matrix.diagonal x * C)) 3
  assertSymmetry (← `(fun (m n : Nat) (C : Matrix (Fin m) (Fin n) ℝ) =>
    fun x : Fin n → ℝ => C * Matrix.diagonal x * C.transpose)) 3
  assertSymmetry (← `(fun (m n : Nat) (B : Matrix (Fin m) (Fin n) ℝ) =>
    fun x : (Fin m → ℝ) × (Fin n → ℝ) =>
      fromBlocksFin (Matrix.diagonal x.1) B B.transpose (Matrix.diagonal x.2))) 3
  assertSymmetry (← `(fun (k n : Nat) => fun x : Fin k → Fin n → ℝ =>
    ∑ i, Matrix.diagonal (x i))) 2
  assertSymmetry (← `(fun (n : Nat) (e : Fin n ≃ Fin n) =>
    fun x : Fin n → ℝ => Matrix.reindex e e (Matrix.diagonal x))) 2
  assertSymmetry (← `(fun (m n : Nat) (f : Fin m → Fin n) =>
    fun x : Fin n → ℝ => (Matrix.diagonal x).submatrix f f)) 3
  assertSymmetry (← `(fun x : ℝ => (!![x, 2 * x + 1; x + x + 1, 3] :
    Matrix (Fin 2) (Fin 2) ℝ)))

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRow (← `(fun n : Nat => fun x : Fin n → ℝ => (Matrix.diagonal x).PosSemidef)) 1
  assertRow (← `(fun n : Nat => fun x : SymmetricMatrix n => x ∈ PSD n)) 1
  assertRow (← `(fun n : Nat => fun x : SymmetricMatrix n => x.toMatrix.PosSemidef)) 1
  assertRow (← `(fun x : ℝ => (!![x, 2; 2, x + 1] :
    Matrix (Fin 2) (Fin 2) ℝ).PosSemidef))
  assertRow (← `(fun x : Fin 0 → ℝ => (Matrix.diagonal x).PosSemidef))
  assertRow (← `(fun x : ℝ => (!![x] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef))
  assertRow (← `(fun (m n : Nat) (C : Matrix (Fin m) (Fin n) ℝ) =>
    fun x : Fin m → ℝ => (C.transpose * Matrix.diagonal x * C).PosSemidef)) 3
  assertRow (← `(fun (m n : Nat) (C : Matrix (Fin m) (Fin n) ℝ) =>
    fun x : Fin n → ℝ => (C * Matrix.diagonal x * C.transpose).PosSemidef)) 3
  assertRow (← `(fun (m n : Nat) (B : Matrix (Fin m) (Fin n) ℝ) =>
    fun x : (Fin m → ℝ) × (Fin n → ℝ) =>
      (fromBlocksFin (Matrix.diagonal x.1) B B.transpose (Matrix.diagonal x.2)).PosSemidef)) 3
  assertRow (← `(fun (k n : Nat) => fun x : Fin k → Fin n → ℝ =>
    (∑ i, Matrix.diagonal (x i)).PosSemidef)) 2
  assertRow (← `(fun (n : Nat) (e : Fin n ≃ Fin n) =>
    fun x : Fin n → ℝ => (Matrix.reindex e e (Matrix.diagonal x)).PosSemidef)) 2
  assertRow (← `(fun (m n : Nat) (f : Fin m → Fin n) =>
    fun x : Fin n → ℝ => ((Matrix.diagonal x).submatrix f f).PosSemidef)) 3

/-! A native PSD predicate cannot silently impose symmetry on an arbitrary
matrix, and non-affine symmetric expressions remain unsupported rows. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSymmetry (← `(fun n : Nat => fun x : Matrix (Fin n) (Fin n) ℝ => x)) 1 false
  assertSymmetry (← `(fun x : ℝ => (!![x, 1; 0, x] :
    Matrix (Fin 2) (Fin 2) ℝ))) 0 false
  assertRowUnsupported (← `(fun n : Nat => fun x : Matrix (Fin n) (Fin n) ℝ =>
    x.PosSemidef)) 1
  assertRowUnsupported (← `(fun x : ℝ => (!![x, 1; 0, x] :
    Matrix (Fin 2) (Fin 2) ℝ).PosSemidef))
  assertRowUnsupported (← `(fun x : ℝ => (!![x * x] :
    Matrix (Fin 1) (Fin 1) ℝ).PosSemidef))
  assertRowUnsupported (← `(fun (n : Nat) => fun x : Matrix (Fin n) (Fin n) ℝ =>
    (x.transpose * x).PosSemidef)) 1

/-! Neither a feasibility-local assumption nor an unresolved/placeholder
independent witness may become a global symmetry certificate. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ) =>
    fun x : ℝ => F x))
  lambdaBoundedTelescope expression 2 fun _ source => do
    lambdaTelescope source fun points matrix => do
      let proposition ← mkAppM ``Matrix.IsSymm #[matrix]
      withLocalDeclD `feasibleSymmetry proposition fun _ => do
        let before ← getMCtx
        if (← Morew.Elab.Conic.Symmetry.prove? points[0]! matrix).isSome then
          throwError "feasibility-local symmetry was accepted globally"
        checkUnchanged before
      let universal ← mkForallFVars points proposition
      let hole ← mkFreshExprMVar universal
      withLetDecl `unfinishedSymmetry universal hole fun _ => do
        let before ← getMCtx
        if (← Morew.Elab.Conic.Symmetry.prove? points[0]! matrix).isSome then
          throwError "unfinished symmetry proof was accepted"
        checkUnchanged before
      if ← hole.mvarId!.isAssigned then throwError "symmetry checker solved a caller proof hole"
      let placeholder ← mkSorry universal true
      withLetDecl `placeholderSymmetry universal placeholder fun _ => do
        let before ← getMCtx
        if (← Morew.Elab.Conic.Symmetry.prove? points[0]! matrix).isSome then
          throwError "placeholder symmetry proof was accepted"
        checkUnchanged before

/-! Source operations and relations must use canonical instances, regardless
of whether a custom operation happens to agree at a particular point. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRowUnsupported (← `(fun n : Nat => fun x : SymmetricMatrix n =>
    @Membership.mem (SymmetricMatrix n) (ConvexCone ℝ (SymmetricMatrix n))
      ⟨fun _ _ => True⟩ (PSD n) x)) 1
  assertRowUnsupported (← `(fun [PartialOrder ℝ] =>
    fun x : Fin 2 → ℝ => (Matrix.diagonal x).PosSemidef)) 1
  assertRowUnsupported (← `(fun x : ℝ =>
    (@HAdd.hAdd (Matrix (Fin 1) (Fin 1) ℝ) (Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix (Fin 1) (Fin 1) ℝ) ⟨fun _ _ => !![1]⟩ !![x] !![x]).PosSemidef))

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate (← `(fun n : Nat => fun x : SymmetricMatrix n => x ∈ PSD n))
  lambdaBoundedTelescope expression 1 fun _ source => do
    lambdaTelescope source fun points body => do
      let arguments := body.getAppArgs
      let type ← inferType arguments[2]!
      let hole ← mkFreshExprMVar type
      withLetDecl `hiddenMembership type hole fun binding => do
        let predicate ← mkLambdaFVars points (mkAppN body.getAppFn (arguments.set! 2 binding))
        let before ← getMCtx
        let .error error ← Morew.Elab.Conic.normalizeRow predicate (label? := some `unfinished_psd)
          | throwError "unfinished PSD membership instance was accepted"
        checkUnchanged before
        let diagnostic ← error.reason.toString
        unless diagnostic.contains "unfinished_psd" && diagnostic.contains "unresolved metavariables" do
          throwError "missing contextual unresolved PSD diagnostic: {diagnostic}"
      if ← hole.mvarId!.isAssigned then throwError "PSD recognition assigned a caller instance hole"

end MorewTest.Conic.PositiveSemidefiniteElab
