/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Plan
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Persistent certified conic forms

Build affine cone data for the complete current typed problem. The stored
representation proves equality of objective and feasibility, independently of
the reformulation runner's source-to-target optimization certificate.

For abstract function indices, certification accepts `Finite` evidence. Ordinary
norm-dependent field notation follows mathlib's `Fintype` prerequisites; callers
with only `Finite ι` can install `letI := Fintype.ofFinite ι` when using the data.
-/

namespace Morew.Elab.Conic

open Lean Lean.Meta
open Morew.Elab.Rewrite
open Reformulation

private theorem problemEq {X : Type u} {V : Type v} (p q : Morew.Problem X V)
    (objective : ∀ x, p.objective x = q.objective x)
    (feasible : ∀ x, p.feasible x ↔ q.feasible x) : p = q := by
  cases p with
  | mk po pf =>
    cases q with
    | mk qo qf =>
      exact congrArg₂ Morew.Problem.mk (funext objective)
        (funext fun x => propext (feasible x))

private theorem emptyRows {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : X) :
    (∀ i : Fin 0, (Fin.elim0 i : Morew.Conic.Constraint X).Holds x) ↔ True :=
  Fin.forall_fin_zero

private def prependRow {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : Nat} (row : Morew.Conic.Constraint X)
    (rest : Fin n → Morew.Conic.Constraint X) : Fin (n + 1) → Morew.Conic.Constraint X :=
  Fin.cons row rest

private theorem consRows {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : Nat} (row : Morew.Conic.Constraint X)
    (rest : Fin n → Morew.Conic.Constraint X) (x : X) :
    (∀ i, (prependRow row rest i).Holds x) ↔ row.Holds x ∧ ∀ i, (rest i).Holds x :=
  Fin.forall_fin_succ

private structure RowBlock where
  predicates : Array Expr
  decomposition : Expr
  rows : Array RowResult

-- Build the finite table and its equivalence with the ordered leaf conjunction
-- together, so zero and singleton tables obey the presentation convention.
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

-- Named presentation entries may themselves be conjunctions. Their original
-- boundaries remain in the represented problem, while data stores the leaves.
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

-- Cached rows are untrusted inputs: retain their certificates only after checking
-- that they prove the exact decomposed predicate for the current domain.
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

private def buildFormCore (presentation : PresentationState) (provider : Affine.EvidenceProvider)
    (certifiedRows : Array (Option (Array RowResult))) :
    MetaM (Except Expr.Error Expr) := do
  for expression in #[presentation.domainType, presentation.valueType, presentation.objective] ++
      presentation.binders.map (·.type) ++ presentation.constraints.map (·.predicate) do
    if ← Morew.Elab.Rewrite.Plan.unresolved expression then
      return .error {
        expression
        reason := ← addMessageContext "conic form: unresolved metavariables in typed presentation"
      }
  unless certifiedRows.isEmpty || certifiedRows.size == presentation.constraints.size do
    throwError "cached row entry count does not match the typed presentation"
  let canonical ← presentation.canonicalProblem
  let objective ← match ← reifyObjective presentation provider with
    | .error error => return .error error
    | .ok result => pure result
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
  let form ← Space.withCanonicalDomain presentation.domainType do
    let (constraints, rowsIff) ← assembleRows presentation.domainType predicates rows
    let decomposition ← assembleDecomposition presentation.domainType blocks
    let feasibleIff ← withLocalDeclD `point presentation.domainType fun point => do
      let proof ← mkAppM ``Iff.trans #[mkApp rowsIff point,
        ← mkAppM ``Iff.symm #[mkApp decomposition point]]
      mkLambdaFVars #[point] proof
    let sense := mkConst <| match presentation.sense with
      | .minimize => ``Morew.ObjectiveSense.minimize
      | .maximize => ``Morew.ObjectiveSense.maximize
    let data ← mkAppM ``Morew.Conic.Data.mk
      #[sense, objective.map, mkNatLit rows.size, constraints]
    let represented ← mkAppM ``Morew.Conic.Data.toProblem #[data]
    let equality ← mkAppM ``problemEq
      #[represented, canonical, objective.pointwiseEquality, feasibleIff]
    let form ← instantiateMVars (← mkAppM ``Morew.Conic.Form.mk #[data, equality])
    let expected ← mkAppM ``Morew.Conic.Form #[canonical]
    unless ← isDefEq (← inferType form) expected do
      throwError "conic form does not represent the current canonical problem"
    if form.hasMVar then
      throwError "conic form contains unresolved metavariables"
    checkWithKernel form
    return form
  -- A declaration inferred directly from this expression must support ordinary
  -- `.data` projections. Expose aliases in the domain and in every canonical
  -- instance type: retaining Matrix aliases inside a product's group would
  -- prevent later NormedSpace synthesis even after exposing the outer domain.
  let domain ← Space.structuralDomain presentation.domainType
  let publicType ← Space.withCanonicalDomain domain do
    mkAppOptM ``Morew.Conic.Form #[some domain, none, none, none, some canonical]
  let form ← mkAppOptM ``id #[some publicType, some form]
  checkWithKernel form
  return .ok form

/-- Certify the complete current typed problem as persistent affine cone data.
Conjunction leaves retain presentation order; literal `True` contributes no
rows. The returned form represents `presentation.canonicalProblem` exactly and
retains the explicit objective sense, including maximizing declarations.
An optional nonempty cache has one slot per presentation entry. Each `some`
contains checked rows in decomposed predicate order; `none` normalizes the entry.
Cached constraints and proofs are checked against their current predicates. -/
def buildForm (presentation : PresentationState) (provider : Affine.EvidenceProvider := {})
    (certifiedRows : Array (Option (Array RowResult)) := #[]) :
    MetaM (Except Expr.Error Expr) :=
  State.withIsolatedMVars do
    try
      Plan.withPresentationFiniteInstances
        (fun result oldVars newVars => result.replaceFVars oldVars newVars)
        presentation (buildFormCore presentation provider certifiedRows)
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext m!"conic form: {error.toMessageData}"
      }

end Morew.Elab.Conic
