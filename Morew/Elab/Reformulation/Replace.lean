/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Presentation
import Morew.Elab.Rewrite.Decomposition
import Morew.Elab.Rewrite.Plan
import Morew.Transform

/-! Assemble exact replacements in ordered constraints, preserving unselected row boundaries.
`Rows` updates names and displayed constraints. -/

namespace Morew.Elab.Reformulation.Replace

open Lean Lean.Meta
open Morew.Elab.Reformulation

private theorem unitTargetIff {X : Type u} (source : X → Prop)
    (target : X → Unit → Prop)
    (h : ∀ x, source x ↔ ∃ a, target x a) :
    ∀ x, source x ↔ target x () :=
  fun x => (h x).trans Unique.exists_iff

private theorem existsUnitIff (target : Unit → Prop) : (∃ a, target a) ↔ target () :=
  Unique.exists_iff

open Morew.Elab.Rewrite.Decomposition (conjunctionParts)

private def proveIff (lhs rhs : Expr)
    (forward backward : Expr → MetaM Expr) : MetaM Expr := do
  let forward ← withLocalDeclD `h lhs fun h => do
    mkLambdaFVars #[h] (← forward h)
  let backward ← withLocalDeclD `h rhs fun h => do
    mkLambdaFVars #[h] (← backward h)
  mkAppM ``Iff.intro #[forward, backward]

private def applyRows (rows : Array Expr) (point : Expr) : Array Expr :=
  rows.map (mkApp · point)

/-- Separate exactly one displayed row from the retained ordered conjunction.
Conjunctions inside an individual row keep their original boundaries. -/
def makeDecomposition (presentation : PresentationState) (index : Nat)
    (targetProblem : Expr) : MetaM Expr := do
  unless index < presentation.constraints.size do
    throwError "constraint decomposition index is out of bounds"
  let rows := presentation.constraints.map (·.predicate)
  let remainder := splice rows index #[]
  let remainderFunction ← mkFeasibleFunction presentation.domainType remainder
  let source := rows[index]!
  let feasible ← mkAppM ``Morew.Problem.feasible #[targetProblem]
  let proof ← withLocalDeclD `point presentation.domainType fun point => do
    let lhs := mkApp feasible point
    let rhs := mkApp2 (mkConst ``And)
      (mkApp remainderFunction point) (mkApp source point)
    let proof ← proveIff lhs rhs (fun h => do
      let parts ← conjunctionParts rows.size h
      mkAppM ``And.intro
        #[← mkAndIntroN (splice parts index #[]).toList, parts[index]!]) (fun h => do
      let other ← conjunctionParts remainder.size (← mkAppM ``And.left #[h])
      let selected ← mkAppM ``And.right #[h]
      mkAndIntroN (other.extract 0 index ++ #[selected] ++
        other.extract index other.size).toList)
    mkLambdaFVars #[point] proof
  mkAppM ``Morew.ConstraintDecomposition.mk #[remainderFunction, proof]

/-- The canonical problem and its exact equivalence from the old presentation. -/
structure RewriteResult where
  /-- Explicit canonical problem containing the ordered replacement rows. -/
  targetProblem : Expr
  /-- `GlobalEquiv` from the old canonical problem to `targetProblem`. -/
  equiv : Expr

/-- Assemble a selected-row replacement; `targetIff` equates the representation target
with the ordered replacement conjunction. -/
private def rewriteConstraintCore (presentation : PresentationState) (index : Nat)
    (certificate : Rewrite.Plan.Certificate) (auxiliary? : Option Expr) (nextDomain : Expr)
    (rows : Array Expr) (targetIff : Expr) : MetaM RewriteResult := do
  unless index < presentation.constraints.size do
    throwError "constraint replacement index is out of bounds"
  let oldProblem ← presentation.canonicalProblem
  let oldRows := presentation.constraints.map (·.predicate)
  let source := oldRows[index]!
  let (objective, retainedRows) ← match auxiliary? with
    | none => pure (presentation.objective, oldRows)
    | some _ => withLocalDeclD `point nextDomain fun point => do
      let original ← mkAppM ``Prod.fst #[point]
      let objective ← mkLambdaFVars #[point] (mkApp presentation.objective original)
      let retained ← oldRows.mapM fun row => do
        mkLambdaFVars #[point] (mkApp row original)
      pure (objective, retained)
  let nextRows := splice retainedRows index rows
  let feasible ← mkFeasibleFunction nextDomain nextRows
  let targetProblem ← mkAppM ``Morew.Problem.mk #[objective, feasible]
  let (natural, primitive) ← match auxiliary? with
    | none => pure (oldProblem, none)
    | some _ => do
      let decomposition ← makeDecomposition presentation index oldProblem
      let (natural, primitive) ← match certificate with
        | .exact repr => do
          let natural ← mkAppM ``Morew.Problem.replaceConstraint #[oldProblem, repr, decomposition]
          let primitive ← mkAppM ``Morew.replaceConstraintEquiv
            #[oldProblem, repr, decomposition]
          pure (natural, primitive)
        | .contextual _ target sourceIffExists => do
          let natural ← mkAppM ``Morew.Problem.replaceConstraintUnder
            #[oldProblem, decomposition, target]
          let primitive ← mkAppM ``Morew.replaceConstraintUnderEquiv
            #[oldProblem, decomposition, target, sourceIffExists]
          pure (natural, primitive)
      pure (natural, some primitive)
  let naturalFeasible ← mkAppM ``Morew.Problem.feasible #[natural]
  let feasibleIff ← withLocalDeclD `point nextDomain fun point => do
    let blockIff := fun (retained : Array Expr) => do
      match auxiliary? with
      | none =>
        let sourceIff ← match certificate with
          | .exact repr => do
            let target ← mkAppM ``Morew.ConstraintRepr.target #[repr]
            let exact ← mkAppM ``Morew.ConstraintRepr.source_iff_exists #[repr]
            let unitIff ← mkAppM ``unitTargetIff #[source, target, exact]
            pure (mkApp unitIff point)
          | .contextual _ target sourceIffExists => do
            let exact := mkApp2 sourceIffExists point (← mkAndIntroN retained.toList)
            mkAppM ``Iff.trans
              #[exact, ← mkAppM ``existsUnitIff #[mkApp target point]]
        mkAppM ``Iff.trans #[sourceIff, mkApp targetIff point]
      | some _ => pure (mkApp targetIff point)
    let proof ← proveIff (mkApp naturalFeasible point) (mkApp feasible point)
      (fun h => do
        let (other, selected) ← match auxiliary? with
          | none => do
            let parts ← conjunctionParts oldRows.size h
            pure (splice parts index #[], parts[index]!)
          | some _ => do
            let other ← conjunctionParts (oldRows.size - 1) (← mkAppM ``And.left #[h])
            pure (other, ← mkAppM ``And.right #[h])
        let generated ← conjunctionParts rows.size
          (← mkAppM ``Iff.mp #[← blockIff other, selected])
        mkAndIntroN (other.extract 0 index ++ generated ++ other.extract index other.size).toList)
      (fun h => do
        let parts ← conjunctionParts nextRows.size h
        let generated ← mkAndIntroN (parts.extract index (index + rows.size)).toList
        let before := parts.extract 0 index
        let after := parts.extract (index + rows.size) parts.size
        let selected ← mkAppM ``Iff.mpr #[← blockIff (before ++ after), generated]
        match auxiliary? with
        | none => mkAndIntroN (before ++ #[selected] ++ after).toList
        | some _ => mkAppM ``And.intro #[← mkAndIntroN (before ++ after).toList, selected])
    mkLambdaFVars #[point] proof
  let objectiveEq ← withLocalDeclD `point nextDomain fun point => do
    mkLambdaFVars #[point] (← mkEqRefl (mkApp objective point))
  let normalization ← mkAppM ``Morew.pointwiseEquiv
    #[natural, targetProblem, objectiveEq, feasibleIff]
  let equiv ← match primitive with
    | none => pure normalization
    | some primitive => mkAppM ``Morew.GlobalEquiv.trans #[primitive, normalization]
  let targetProblem ← instantiateMVars targetProblem
  let equiv ← instantiateMVars equiv
  if targetProblem.hasMVar || equiv.hasMVar then
    throwError "constraint replacement contains unresolved metavariables"
  checkWithKernel equiv
  return { targetProblem, equiv }

/-- Validate and apply a replacement using current retained constraints. -/
def applyReplacement (presentation : PresentationState) (index : Nat)
    (replacement : Rewrite.Plan.Result) : MetaM RewriteResult := do
  unless index < presentation.constraints.size do
    throwError "constraint replacement index is out of bounds"
  let oldRows := presentation.constraints.map (·.predicate)
  replacement.check oldRows[index]! (splice oldRows index #[])
  rewriteConstraintCore presentation index replacement.certificate replacement.auxiliary?
    replacement.nextDomain replacement.rowPredicates replacement.targetIff

/-- Replace a row using equivalence conditional on retained rows.
Reconstruct retained evidence in both directions. -/
def rewriteConstraintContextual (presentation : PresentationState) (index : Nat)
    (rows : Array Expr) (conditionalIff : Expr) : MetaM RewriteResult := do
  unless index < presentation.constraints.size do
    throwError "constraint replacement index is out of bounds"
  let oldProblem ← presentation.canonicalProblem
  let oldRows := presentation.constraints.map (·.predicate)
  let remainder := splice oldRows index #[]
  let nextRows := splice oldRows index rows
  let domain := presentation.domainType
  let expected ← withLocalDeclD `point domain fun point => do
    let hypothesis := mkAndN (applyRows remainder point).toList
    let conclusion := mkApp2 (mkConst ``Iff) (mkApp oldRows[index]! point)
      (mkAndN (applyRows rows point).toList)
    mkForallFVars #[point] (← mkArrow hypothesis conclusion)
  unless ← isDefEq (← inferType conditionalIff) expected do
    throwError "conditional conic certificate does not match the selected row and retained constraints"
  checkWithKernel conditionalIff
  let feasible ← mkFeasibleFunction domain nextRows
  let targetProblem ← mkAppM ``Morew.Problem.mk #[presentation.objective, feasible]
  let feasibleIff ← withLocalDeclD `point domain fun point => do
    let proof ← proveIff (mkAndN (applyRows oldRows point).toList)
      (mkAndN (applyRows nextRows point).toList) (fun h => do
        let parts ← conjunctionParts oldRows.size h
        let other := splice parts index #[]
        let block := mkApp2 conditionalIff point (← mkAndIntroN other.toList)
        let generated ← conjunctionParts rows.size
          (← mkAppM ``Iff.mp #[block, parts[index]!])
        mkAndIntroN (other.extract 0 index ++ generated ++ other.extract index other.size).toList)
      (fun h => do
        let parts ← conjunctionParts nextRows.size h
        let before := parts.extract 0 index
        let after := parts.extract (index + rows.size) parts.size
        let block := mkApp2 conditionalIff point (← mkAndIntroN (before ++ after).toList)
        let generated ← mkAndIntroN (parts.extract index (index + rows.size)).toList
        let selected ← mkAppM ``Iff.mpr #[block, generated]
        mkAndIntroN (before ++ #[selected] ++ after).toList)
    mkLambdaFVars #[point] proof
  let objectiveEq ← withLocalDeclD `point domain fun point => do
    mkLambdaFVars #[point] (← mkEqRefl (mkApp presentation.objective point))
  let equiv ← instantiateMVars (← mkAppM ``Morew.pointwiseEquiv
    #[oldProblem, targetProblem, objectiveEq, feasibleIff])
  if equiv.hasMVar then
    throwError "conditional constraint replacement contains unresolved metavariables"
  checkWithKernel equiv
  return { targetProblem, equiv }

end Morew.Elab.Reformulation.Replace
