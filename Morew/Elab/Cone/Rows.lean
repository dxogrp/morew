/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Cone.Constraint
import Morew.Elab.Rewrite.Plan
import Morew.Elab.Expr
import Morew.Elab.State

/-! Assemble checked affine cone rows and their exact feasibility certificate. -/

namespace Morew.Elab.Cone

open Lean Lean.Meta
open Morew.Elab.Rewrite
open Reformulation

private theorem emptyRows {X : Type u} [AddCommGroup X] [Module ℝ X]
    (x : X) :
    (∀ i : Fin 0, (Fin.elim0 i : Morew.Conic.Constraint X).Holds x) ↔ True :=
  Fin.forall_fin_zero

private def prependRow {X : Type u} [AddCommGroup X] [Module ℝ X]
    {n : Nat} (row : Morew.Conic.Constraint X)
    (rest : Fin n → Morew.Conic.Constraint X) : Fin (n + 1) → Morew.Conic.Constraint X :=
  Fin.cons row rest

private theorem consRows {X : Type u} [AddCommGroup X] [Module ℝ X]
    {n : Nat} (row : Morew.Conic.Constraint X)
    (rest : Fin n → Morew.Conic.Constraint X) (x : X) :
    (∀ i, (prependRow row rest i).Holds x) ↔ row.Holds x ∧ ∀ i, (rest i).Holds x :=
  Fin.forall_fin_succ

private structure RowBlock where
  predicates : Array Expr
  decomposition : Expr
  rows : Array RowResult

-- Build the row table and its ordered conjunction equivalence together.
private def assembleRows (domain : Expr) (predicates : Array Expr)
    (rows : Array RowResult) : MetaM (Expr × Expr) := do
  let rowType ← mkAppOptM ``Morew.Conic.Constraint #[some domain, none, none]
  let empty ← withLocalDeclD `i (← mkAppM ``Fin #[mkNatLit 0]) fun i => do
    mkLambdaFVars #[i] (← mkAppOptM ``Fin.elim0 #[some rowType, some i])
  withLocalDeclD `point domain fun point => do
    let mut table := empty
    let mut proof ← mkAppM ``emptyRows #[point]
    let mut tailPredicates := []
    for (row, predicate) in (rows.zip predicates).toList.reverse do
      let head := mkApp predicate point
      let split ← mkAppM ``consRows #[row.constraint, table, point]
      let paired ← mkAppM ``and_congr #[mkApp row.pointwiseIff point, proof]
      let joined ← Decomposition.appendIff [head] tailPredicates
      proof ← mkAppM ``Iff.trans #[split, ← mkAppM ``Iff.trans #[paired, joined]]
      table ← mkAppM ``prependRow #[row.constraint, table]
      tailPredicates := head :: tailPredicates
    return (table, ← mkLambdaFVars #[point] proof)

-- Flatten conjunctions into data while retaining named presentation boundaries.
private def assembleDecomposition (domain : Expr) (blocks : Array RowBlock) :
    MetaM Expr :=
  withLocalDeclD `point domain fun point => do
    let mut proof := mkApp (mkConst ``Iff.rfl) (mkConst ``True)
    let mut leaves := []
    let mut first := true
    for block in blocks.toList.reverse do
      let predicates := block.predicates.toList.map (mkApp · point)
      if first then
        proof := mkApp block.decomposition point
        first := false
      else
        let paired ← mkAppM ``and_congr #[mkApp block.decomposition point, proof]
        proof ← mkAppM ``Iff.trans #[paired, ← Decomposition.appendIff predicates leaves]
      leaves := predicates ++ leaves
    mkLambdaFVars #[point] proof

-- Check cached row certificates against the current domain and predicates.
private def checkCertifiedRow (domain predicate : Expr) (row : RowResult) :
    MetaM RowResult := do
  for expression in #[row.constraint, row.pointwiseIff] do
    if ← Morew.Elab.Rewrite.Plan.unresolved expression then
      throwError "cached row contains unresolved metavariables"
  let row ← row.mapExprM instantiateMVars
  checkWithKernel row.constraint
  checkWithKernel row.pointwiseIff
  let constraintType ← whnf (← inferType row.constraint)
  unless constraintType.isAppOfArity ``Morew.Conic.Constraint 3 do
    throwError "cached row is not a conic constraint"
  unless ← isDefEq constraintType.getAppArgs[0]! domain do
    throwError "cached row does not use the current decision domain"
  let expected ← withLocalDeclD `point domain fun point => do
    let holds := mkAppN
      (mkConst ``Morew.Conic.Constraint.Holds constraintType.getAppFn.constLevels!)
      (constraintType.getAppArgs ++ #[row.constraint, point])
    mkForallFVars #[point] (mkApp2 (mkConst ``Iff) holds (mkApp predicate point))
  unless ← isDefEq (← inferType row.pointwiseIff) expected do
    throwError "cached row certificate does not match its decomposed predicate"
  return row

/-- A finite table of cone rows representing the complete current feasible predicate. -/
structure RowTable where
  /-- Number of rows after decomposing presentation groups. -/
  count : Nat
  /-- A term of type `Fin count → Conic.Constraint X`. -/
  constraints : Expr
  /-- Pointwise equivalence between all stored rows and the current feasible predicate. -/
  feasibleIff : Expr

/-- Certify and assemble cone rows in presentation order, validating any cached evidence. -/
def buildRows (presentation : PresentationState) (provider : Affine.EvidenceProvider := {})
    (certifiedRows : Array (Option (Array RowResult)) := #[]) :
    MetaM (Except Expr.Error RowTable) := do
  unless certifiedRows.isEmpty || certifiedRows.size == presentation.constraints.size do
    throwError "cached row entry count does not match the typed presentation"
  let mut blocks := #[]
  for entryIndex in [:presentation.constraints.size] do
    let entry := presentation.constraints[entryIndex]!
    let (predicates, decomposition) ← try
      decomposePredicate entry.predicate
    catch error =>
      return .error {
        expression := entry.predicate
        reason := ← addMessageContext m!"constraint `{entry.name}`: {error.toMessageData}"
      }
    let mut rows := #[]
    if let some cached := (certifiedRows[entryIndex]?).getD none then
      try
        unless cached.size == predicates.size do
          throwError "cached row count does not match the decomposed predicate count"
        rows ← (cached.zip predicates).mapM fun (row, predicate) =>
          checkCertifiedRow presentation.domainType predicate row
      catch error =>
        return .error {
          expression := entry.predicate
          reason := ← addMessageContext m!"constraint `{entry.name}`: {error.toMessageData}"
        }
    else
      for predicate in predicates do
        match ← normalizeRow predicate provider (some entry.name) with
        | .error error => return .error error
        | .ok row => rows := rows.push row
    blocks := blocks.push { predicates, decomposition, rows : RowBlock }
  let predicates := blocks.flatMap (·.predicates)
  let rows := blocks.flatMap (·.rows)
  let (constraints, feasibleIff) ← Space.withCanonicalDomainPair presentation.domainType do
    let (constraints, rowsIff) ← assembleRows presentation.domainType predicates rows
    let decomposition ← assembleDecomposition presentation.domainType blocks
    let feasibleIff ← withLocalDeclD `point presentation.domainType fun point => do
      let proof ← mkAppM ``Iff.trans #[mkApp rowsIff point,
        ← mkAppM ``Iff.symm #[mkApp decomposition point]]
      mkLambdaFVars #[point] proof
    return (constraints, feasibleIff)
  return .ok { count := rows.size, constraints, feasibleIff }

end Morew.Elab.Cone
