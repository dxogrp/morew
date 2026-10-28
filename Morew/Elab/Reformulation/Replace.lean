/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Presentation
import Morew.Elab.Rewrite.Decomposition
import Morew.Elab.Rewrite.Plan
import Morew.Transform

/-!
# Exact replacement of ordered constraint rows

Shared proof assembly for targeted conic and NLP rewrites. This layer applies
checked replacement rows to a typed problem; command-level naming and
presentation updates belong to `Morew.Reformulation.Replace`. Conjunction proofs preserve the
boundaries of unselected rows, even when a row itself contains a conjunction.
-/

namespace Morew.Elab.Reformulation.Replace

open Lean Lean.Meta
open Morew.Elab.Reformulation

private theorem unitTargetIff {X : Type u} (source : X → Prop)
    (target : X → Unit → Prop)
    (h : ∀ x, source x ↔ ∃ a, target x a) :
    ∀ x, source x ↔ target x () := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (h x).mp hx
    cases a
    exact ha
  · intro hx
    exact (h x).mpr ⟨(), hx⟩

private theorem existsUnitIff (target : Unit → Prop) : (∃ a, target a) ↔ target () := by
  constructor
  · rintro ⟨⟨⟩, h⟩
    exact h
  · exact fun h => ⟨(), h⟩

private def conjunction (propositions : Array Expr) : Expr :=
  Rewrite.Decomposition.conjunction propositions.toList

open Morew.Elab.Rewrite.Decomposition (conjunctionProof conjunctionParts)

private def proveIff (lhs rhs : Expr)
    (forward backward : Expr → MetaM Expr) : MetaM Expr := do
  let forward ← withLocalDeclD `h lhs fun h => do
    mkLambdaFVars #[h] (← forward h)
  let backward ← withLocalDeclD `h rhs fun h => do
    mkLambdaFVars #[h] (← backward h)
  mkAppM ``Iff.intro #[forward, backward]

private def splice (entries : Array α) (index : Nat) (replacement : Array α) : Array α :=
  entries.extract 0 index ++ replacement ++ entries.extract (index + 1) entries.size

private def applyRows (rows : Array Expr) (point : Expr) : Array Expr :=
  rows.map (mkApp · point)

private def feasibleFunction (domain : Expr) (rows : Array Expr) : MetaM Expr :=
  withLocalDeclD `point domain fun point => do
    mkLambdaFVars #[point] (conjunction (applyRows rows point))

private def makeDecomposition (presentation : PresentationState) (index : Nat)
    (targetProblem : Expr) : MetaM Expr := do
  let rows := presentation.constraints.map (·.predicate)
  let remainder := splice rows index #[]
  let remainderFunction ← feasibleFunction presentation.domainType remainder
  let source := rows[index]!
  let feasible ← mkAppM ``Morew.Problem.feasible #[targetProblem]
  let proof ← withLocalDeclD `point presentation.domainType fun point => do
    let lhs := mkApp feasible point
    let rhs := mkApp2 (mkConst ``And)
      (mkApp remainderFunction point) (mkApp source point)
    let proof ← proveIff lhs rhs (fun h => do
      let parts ← conjunctionParts rows.size h
      mkAppM ``And.intro
        #[← conjunctionProof (splice parts index #[]), parts[index]!]) (fun h => do
      let other ← conjunctionParts remainder.size (← mkAppM ``And.left #[h])
      let selected ← mkAppM ``And.right #[h]
      conjunctionProof (other.extract 0 index ++ #[selected] ++
        other.extract index other.size))
    mkLambdaFVars #[point] proof
  mkAppM ``Morew.ConstraintDecomposition.mk #[remainderFunction, proof]

/-- The canonical problem and its exact equivalence from the old presentation. -/
structure RewriteResult where
  /-- Explicit canonical problem containing the ordered replacement rows. -/
  targetProblem : Expr
  /-- `GlobalEquivalence` from the old canonical problem to `targetProblem`. -/
  equivalence : Expr

/-- Assemble an exact selected-row replacement from a checked lift and ordered
target rows. `targetIff` identifies the lift target with their conjunction. -/
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
  let feasible ← feasibleFunction nextDomain nextRows
  let targetProblem ← mkAppM ``Morew.Problem.mk #[objective, feasible]
  let (natural, primitive) ← match auxiliary? with
    | none => pure (oldProblem, none)
    | some _ => do
      let decomposition ← makeDecomposition presentation index oldProblem
      let (natural, primitive) ← match certificate with
        | .exact lift => do
          let natural ← mkAppM ``Morew.Problem.liftConstraint #[oldProblem, lift, decomposition]
          let primitive ← mkAppM ``Morew.exactConstraintLiftEquivalence
            #[oldProblem, lift, decomposition]
          pure (natural, primitive)
        | .contextual _ target sourceIffExists => do
          let natural ← mkAppM ``Morew.Problem.liftConstraintConditional
            #[oldProblem, decomposition, target]
          let primitive ← mkAppM ``Morew.conditionalConstraintLiftEquivalence
            #[oldProblem, decomposition, target, sourceIffExists]
          pure (natural, primitive)
      pure (natural, some primitive)
  let naturalFeasible ← mkAppM ``Morew.Problem.feasible #[natural]
  let feasibleIff ← withLocalDeclD `point nextDomain fun point => do
    let blockIff := fun (retained : Array Expr) => do
      match auxiliary? with
      | none =>
        let sourceIff ← match certificate with
          | .exact lift => do
            let target ← mkAppM ``Morew.ExactConstraintLift.target #[lift]
            let exact ← mkAppM ``Morew.ExactConstraintLift.source_iff_exists #[lift]
            let unitIff ← mkAppM ``unitTargetIff #[source, target, exact]
            pure (mkApp unitIff point)
          | .contextual _ target sourceIffExists => do
            let exact := mkApp2 sourceIffExists point (← conjunctionProof retained)
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
        conjunctionProof (other.extract 0 index ++ generated ++ other.extract index other.size))
      (fun h => do
        let parts ← conjunctionParts nextRows.size h
        let generated ← conjunctionProof (parts.extract index (index + rows.size))
        let before := parts.extract 0 index
        let after := parts.extract (index + rows.size) parts.size
        let selected ← mkAppM ``Iff.mpr #[← blockIff (before ++ after), generated]
        match auxiliary? with
        | none => conjunctionProof (before ++ #[selected] ++ after)
        | some _ => mkAppM ``And.intro #[← conjunctionProof (before ++ after), selected])
    mkLambdaFVars #[point] proof
  let objectiveEq ← withLocalDeclD `point nextDomain fun point => do
    mkLambdaFVars #[point] (← mkEqRefl (mkApp objective point))
  let normalization ← mkAppM ``Morew.pointwiseEquivalence
    #[natural, targetProblem, objectiveEq, feasibleIff]
  let equivalence ← match primitive with
    | none => pure normalization
    | some primitive => mkAppM ``Morew.GlobalEquivalence.trans #[primitive, normalization]
  let targetProblem ← instantiateMVars targetProblem
  let equivalence ← instantiateMVars equivalence
  if targetProblem.hasMVar || equivalence.hasMVar then
    throwError "constraint replacement contains unresolved metavariables"
  checkWithKernel equivalence
  return { targetProblem, equivalence }

/-- Validate and apply either kind of checked replacement. Retained evidence is
always reconstructed from the current presentation with the selected row removed. -/
def applyReplacement (presentation : PresentationState) (index : Nat)
    (replacement : Rewrite.Plan.Result) : MetaM RewriteResult := do
  unless index < presentation.constraints.size do
    throwError "constraint replacement index is out of bounds"
  let oldRows := presentation.constraints.map (·.predicate)
  replacement.check oldRows[index]! (splice oldRows index #[])
  rewriteConstraintCore presentation index replacement.certificate replacement.auxiliary?
    replacement.nextDomain replacement.rowPredicates replacement.targetIff

/-- Replace a selected row using a pointwise equivalence conditional on exactly
the retained rows. The remainder is reconstructed in both directions; no
assumption about the selected source row may escape into the reverse proof. -/
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
    let hypothesis := conjunction (applyRows remainder point)
    let conclusion := mkApp2 (mkConst ``Iff) (mkApp oldRows[index]! point)
      (conjunction (applyRows rows point))
    mkForallFVars #[point] (← mkArrow hypothesis conclusion)
  unless ← isDefEq (← inferType conditionalIff) expected do
    throwError "conditional conic certificate does not match the selected row and retained constraints"
  checkWithKernel conditionalIff
  let feasible ← feasibleFunction domain nextRows
  let targetProblem ← mkAppM ``Morew.Problem.mk #[presentation.objective, feasible]
  let feasibleIff ← withLocalDeclD `point domain fun point => do
    let proof ← proveIff (conjunction (applyRows oldRows point))
      (conjunction (applyRows nextRows point)) (fun h => do
        let parts ← conjunctionParts oldRows.size h
        let other := splice parts index #[]
        let block := mkApp2 conditionalIff point (← conjunctionProof other)
        let generated ← conjunctionParts rows.size
          (← mkAppM ``Iff.mp #[block, parts[index]!])
        conjunctionProof (other.extract 0 index ++ generated ++ other.extract index other.size))
      (fun h => do
        let parts ← conjunctionParts nextRows.size h
        let before := parts.extract 0 index
        let after := parts.extract (index + rows.size) parts.size
        let block := mkApp2 conditionalIff point (← conjunctionProof (before ++ after))
        let generated ← conjunctionProof (parts.extract index (index + rows.size))
        let selected ← mkAppM ``Iff.mpr #[block, generated]
        conjunctionProof (before ++ #[selected] ++ after))
    mkLambdaFVars #[point] proof
  let objectiveEq ← withLocalDeclD `point domain fun point => do
    mkLambdaFVars #[point] (← mkEqRefl (mkApp presentation.objective point))
  let equivalence ← instantiateMVars (← mkAppM ``Morew.pointwiseEquivalence
    #[oldProblem, targetProblem, objectiveEq, feasibleIff])
  if equivalence.hasMVar then
    throwError "conditional constraint replacement contains unresolved metavariables"
  checkWithKernel equivalence
  return { targetProblem, equivalence }

end Morew.Elab.Reformulation.Replace
