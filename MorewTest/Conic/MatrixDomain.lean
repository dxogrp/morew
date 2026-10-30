/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.MatrixDomain
import MorewTest.Affine.Support

/-!
# Adversarial positive-definite domain recognition

Every accepted premise proves the original proposition under exactly the
supplied retained rows. Invalid instances, pivots, margins, incomplete evidence,
and unavailable selected-row facts must not change caller metavariables.
-/

namespace MorewTest.Conic.MatrixDomain

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew.Conic MorewTest.Affine

private def checkUnchanged (before : MetavarContext) : MetaM Unit := do
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "matrix domain recognition leaked scratch metavariables"
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "matrix domain recognition changed a caller assignment"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "matrix domain recognition assigned a caller metavariable"
  for (id, value) in before.lAssignment.toList do
    unless after.lAssignment.find? id == some value do
      throwError "matrix domain recognition changed a caller universe assignment"
  for (id, _) in before.lDecls.toList do
    unless before.lAssignment.contains id || !(after.lAssignment.contains id) do
      throwError "matrix domain recognition assigned a caller universe metavariable"

private def checkDomain (point goal : Expr) (retained : Array Expr) (proof : Expr)
    (accepted : Bool) : MetaM Unit := do
  let unrelated ← mkFreshExprMVar (mkConst ``Nat)
  let assigned ← mkFreshExprMVar (mkConst ``Nat)
  assigned.mvarId!.assign (mkNatLit 7)
  let before ← getMCtx
  let messagesBefore ← Core.getMessageLog
  let result ← Morew.Elab.Conic.MatrixDomain.prove? point goal retained proof
  checkUnchanged before
  unless (← Core.getMessageLog).toList.length == messagesBefore.toList.length do
    throwError "matrix domain recognition leaked diagnostics"
  unless result.isSome == accepted do
    throwError "unexpected matrix domain result ({result.isSome}) for {goal}; rows: {retained}"
  if let some evidence := result then
    if evidence.hasMVar || evidence.hasSorry then throwError "incomplete matrix domain certificate"
    checkWithKernel evidence
    unless ← isDefEq (← inferType evidence) goal do
      throwError "matrix domain certificate proves the wrong proposition"
  if ← unrelated.mvarId!.isAssigned then throwError "assigned an unrelated caller metavariable"
  unless (← instantiateMVars assigned) == mkNatLit 7 do
    throwError "discarded an unrelated caller assignment"

private def assertDomain (stx : TSyntax `term) (parameters : Nat := 0)
    (accepted : Bool := true) : TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression parameters fun _ source => do
    lambdaTelescope source fun points pair => do
      unless points.size == 1 do throwError "matrix domain test needs one decision binder"
      let pair ← Morew.Elab.Expr.reduceStructure pair
      unless pair.isAppOfArity ``Prod.mk 4 do throwError "expected a goal/retained pair"
      let goal := pair.getAppArgs[2]!
      let some rows ← getArrayLit? pair.getAppArgs[3]!
        | throwError "expected a literal array of retained propositions"
      let conjunction := Morew.Elab.Rewrite.Decomposition.conjunction rows.toList
      withLocalDeclD `remainder conjunction fun proof =>
        checkDomain points[0]! goal rows proof accepted

/-! Independent constant and universal evidence retain their actual domains. -/

run_cmd liftTermElabM do
  assertDomain (← `(fun (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ) (_h : P.PosDef) =>
    fun _ : ℝ => (P.PosDef, (#[] : Array Prop)))) 3
  assertDomain (← `(fun (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ)
      (_h : True ∧ (True ∧ P.PosDef)) =>
    fun _ : ℝ => (P.PosDef, (#[] : Array Prop)))) 3
  assertDomain (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ x, (F x).PosDef) =>
    fun x : ℝ => ((F x).PosDef, (#[] : Array Prop)))) 3
  assertDomain (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ x, True ∧ (F x).PosDef) =>
    fun x : ℝ => ((F x).PosDef, (#[] : Array Prop)))) 3
  assertDomain (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ x, (F x).PosDef) =>
    fun point : (ℝ × (Fin n → ℝ)) × ℝ =>
      ((F point.1.1).PosDef, (#[] : Array Prop)))) 3
  assertDomain (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ x, True ∧ (F x).PosDef) =>
    fun point : ((ℝ × (Fin n → ℝ)) × ℝ) × (SymmetricMatrix n × SymmetricMatrix n) =>
      ((F point.1.1.1).PosDef, (#[] : Array Prop)))) 3
  assertDomain (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
      (_h : ∀ x, (F 0).PosDef ∧ (F x).PosDef) =>
    fun _ : ℝ => ((F 0).PosDef, (#[] : Array Prop)))) 3

/-! Retained raw domains preserve conjunctions and local lets, including
bindings that depend on the decision point. -/

run_cmd liftTermElabM do
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[P.PosDef]))) 1
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[True, True ∧ (P.PosDef ∧ True), True]))) 1
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[let Q := P; True ∧ Q.PosDef]))) 1
  assertDomain (← `(fun (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ) => fun _ : ℝ =>
    (P.PosDef, #[let Q := P; True ∧ Q.PosDef]))) 2

/-! Strictly positive independent margins work as native predicates or genuine
PSD memberships; zero, negative, and decision-dependent margins do not. -/

run_cmd liftTermElabM do
  assertDomain (← `(fun (n : Nat) (epsilon : ℝ) (_h : 0 < epsilon) =>
    fun P : Matrix (Fin n) (Fin n) ℝ =>
      (P.PosDef, #[(P - epsilon • 1).PosSemidef]))) 3
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef, #[(P.toMatrix - (1 / 2 : ℝ) • 1).PosSemidef]))) 1
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef, #[SymmetricMatrix.ofMatrix (P.toMatrix - (2 : ℝ) • 1)
      (P.isSymm.sub (Matrix.isSymm_one.smul 2)) ∈ PSD n]))) 1
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef, #[let epsilon : ℝ := 2;
      True ∧ (P - epsilon • SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one) ∈ PSD n]))) 1
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[(P - (0 : ℝ) • 1).PosSemidef]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[(P - (-1 : ℝ) • 1).PosSemidef]))) 1 false
  assertDomain (← `(fun n : Nat => fun p : Matrix (Fin n) (Fin n) ℝ × ℝ =>
    (p.1.PosDef, #[(p.1 - p.2 • 1).PosSemidef, 0 < p.2]))) 1 false

/-! Identity-coupled witnesses require the exact pivot and both identity
blocks. Canonical native and membership spellings have identical meaning. -/

run_cmd liftTermElabM do
  assertDomain (← `(fun n : Nat =>
    fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      (p.1.PosDef, #[(fromBlocksFin p.1 1 1 p.2).PosSemidef]))) 1
  assertDomain (← `(fun n : Nat => fun p : SymmetricMatrix n × SymmetricMatrix n =>
    (p.1.toMatrix.PosDef, #[SymmetricMatrix.fromBlocks p.1 1 p.2 ∈ PSD (n + n)]))) 1
  assertDomain (← `(fun n : Nat => fun p : SymmetricMatrix n × SymmetricMatrix n =>
    (p.1.toMatrix.PosDef, #[let W := p.2;
      True ∧ SymmetricMatrix.fromBlocks p.1 1 W ∈ PSD (n + n)]))) 1
  assertDomain (← `(fun n : Nat =>
    fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      (p.1.PosDef, #[(fromBlocksFin p.2 1 1 p.2).PosSemidef]))) 1 false
  assertDomain (← `(fun n : Nat =>
    fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      (p.1.PosDef, #[(fromBlocksFin p.1 0 1 p.2).PosSemidef]))) 1 false
  assertDomain (← `(fun n : Nat =>
    fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      (p.1.PosDef, #[(fromBlocksFin p.1 1 0 p.2).PosSemidef]))) 1 false

/-! Missing domains and merely semidefinite or singular pivots remain rejected. -/

run_cmd liftTermElabM do
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, (#[] : Array Prop)))) 1 false
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[P.PosSemidef]))) 1 false
  assertDomain (← `(fun _ : ℝ =>
    ((0 : Matrix (Fin 1) (Fin 1) ℝ).PosDef,
      #[(0 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef]))) 0 false
  assertDomain (← `(fun p : Σ n : Nat, Matrix (Fin n) (Fin n) ℝ =>
    (p.2.PosDef, #[p.2.PosDef]))) 0 false

/-! Custom relations and operations cannot masquerade as canonical domains. -/

run_cmd liftTermElabM do
  assertDomain (← `(fun n : Nat => fun p : SymmetricMatrix n × SymmetricMatrix n =>
    (p.1.toMatrix.PosDef,
      #[@Membership.mem (SymmetricMatrix (n + n))
        (ConvexCone ℝ (SymmetricMatrix (n + n))) ⟨fun _ _ => True⟩
        (PSD (n + n)) (SymmetricMatrix.fromBlocks p.1 1 p.2)]))) 1 false
  assertDomain (← `(fun [PartialOrder ℝ] => fun P : Matrix (Fin 2) (Fin 2) ℝ =>
    (P.PosDef, #[P.PosDef]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[(@HSub.hSub (Matrix (Fin n) (Fin n) ℝ)
      (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ)
      ⟨fun _ _ => 1⟩ P ((1 : ℝ) • 1)).PosSemidef]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[(P - @HSMul.hSMul ℝ (Matrix (Fin n) (Fin n) ℝ)
      (Matrix (Fin n) (Fin n) ℝ) ⟨fun _ _ => 0⟩ 1 1).PosSemidef]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : Matrix (Fin n) (Fin n) ℝ =>
    (P.PosDef, #[(P - @HSMul.hSMul ℝ (Matrix (Fin n) (Fin n) ℝ)
      (Matrix (Fin n) (Fin n) ℝ) ⟨fun _ A => A⟩ 1 1).PosSemidef]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef,
      #[(@HSub.hSub (SymmetricMatrix n) (SymmetricMatrix n) (SymmetricMatrix n)
        ⟨fun _ _ => 0⟩ P (2 • SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one)) ∈ PSD n])))
    1 false
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef,
      #[(P - @HSMul.hSMul ℝ (SymmetricMatrix n) (SymmetricMatrix n)
        ⟨fun _ _ => 0⟩ 2 (SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one)) ∈ PSD n])))
    1 false
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef,
      #[(@HSub.hSub (SymmetricMatrix n) (SymmetricMatrix n) (SymmetricMatrix n)
        ⟨fun Q _ => Q - (2 : ℝ) • SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one⟩
        P (SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one)) ∈ PSD n]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef,
      #[(P - @HSMul.hSMul ℝ (SymmetricMatrix n) (SymmetricMatrix n)
        ⟨fun _ Q => (2 : ℝ) • Q⟩ 1
        (SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one)) ∈ PSD n]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef,
      #[(@HSub.hSub ℝ ℝ (SymmetricMatrix n) ⟨fun _ _ => 0⟩ 0 0) ∈ PSD n]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef,
      #[(P - @HSMul.hSMul Nat (SymmetricMatrix n) (SymmetricMatrix n)
        ⟨fun _ Q => Q⟩ 2 (SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one)) ∈ PSD n]))) 1 false
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef,
      #[(@HSub.hSub ℝ ℝ (SymmetricMatrix n) ⟨fun _ _ => 0⟩ 0 0) ∈ PSD n,
        P.toMatrix.PosDef]))) 1
  assertDomain (← `(fun n : Nat => fun P : SymmetricMatrix n =>
    (P.toMatrix.PosDef,
      #[(P - @HSMul.hSMul Nat (SymmetricMatrix n) (SymmetricMatrix n)
        ⟨fun _ Q => Q⟩ 2 (SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one)) ∈ PSD n,
        P.toMatrix.PosDef]))) 1

/-! Unresolved/placeholder witnesses, including hidden local definitions, are
not domain evidence. Unretained point-dependent assumptions model the selected
row and cannot justify their own replacement. -/

run_cmd liftTermElabM do
  let expression ← elaborate (← `(fun P : Matrix (Fin 2) (Fin 2) ℝ => P.PosDef))
  lambdaTelescope expression fun points goal => do
    let point := points[0]!
    let truth := Lean.mkConst ``True.intro
    withLocalDeclD `selectedRow goal fun _ =>
      checkDomain point goal #[] truth false
    let universal ← mkForallFVars points goal
    let independentHole ← mkFreshExprMVar universal
    withLetDecl `unfinishedDomain universal independentHole fun _ =>
      checkDomain point goal #[] truth false
    if ← independentHole.mvarId!.isAssigned then
      throwError "assigned an independent domain proof hole"
    let independentSorry ← mkSorry universal true
    withLetDecl `placeholderDomain universal independentSorry fun _ =>
      checkDomain point goal #[] truth false
    let retainedHole ← mkFreshExprMVar goal
    checkDomain point goal #[goal] retainedHole false
    withLetDecl `unfinishedRetained goal retainedHole fun proof =>
      checkDomain point goal #[goal] proof false
    if ← retainedHole.mvarId!.isAssigned then
      throwError "assigned a retained domain proof hole"
    let retainedSorry ← mkSorry goal true
    checkDomain point goal #[goal] retainedSorry false
    withLetDecl `placeholderRetained goal retainedSorry fun proof =>
      checkDomain point goal #[goal] proof false
    let matrixHole ← mkFreshExprMVar (← inferType point)
    let unfinishedGoal ← mkAppM ``Matrix.PosDef #[matrixHole]
    checkDomain point unfinishedGoal #[] truth false
    if ← matrixHole.mvarId!.isAssigned then
      throwError "assigned a matrix-expression hole"
    let arguments := goal.getAppArgs
    for index in #[3, 4] do
      withLocalDeclD `customScalarInstance (← inferType arguments[index]!) fun binding => do
        let customGoal := mkAppN goal.getAppFn (arguments.set! index binding)
        withLocalDeclD `customDomain customGoal fun proof =>
          checkDomain point goal #[customGoal] proof false
    let instanceHole ← mkFreshExprMVar (← inferType arguments[3]!)
    let unfinishedInstanceGoal := mkAppN goal.getAppFn (arguments.set! 3 instanceHole)
    checkDomain point unfinishedInstanceGoal #[] truth false
    withLetDecl `unfinishedOrder (← inferType instanceHole) instanceHole fun binding => do
      let hiddenGoal := mkAppN goal.getAppFn (arguments.set! 3 binding)
      checkDomain point hiddenGoal #[] truth false
    if ← instanceHole.mvarId!.isAssigned then
      throwError "assigned a scalar-order instance hole"

end MorewTest.Conic.MatrixDomain
