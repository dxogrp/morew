import PTran.Elab.Reformulation.Runner

/-!
# Exact replacement of ordered constraint rows

Internal proof assembly for targeted rewrites. Conjunction proofs preserve the
boundaries of unselected rows, even when a row itself contains a conjunction.
-/

namespace PTran.Elab.Conic

open Lean Lean.Meta
open PTran.Elab.Reformulation

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

private def conjunction (propositions : Array Expr) : Expr :=
  if propositions.isEmpty then mkConst ``True
  else propositions.pop.toList.foldr (mkApp2 (mkConst ``And)) propositions.back!

private def conjunctionProof (proofs : Array Expr) : MetaM Expr := do
  if proofs.isEmpty then return mkConst ``True.intro
  let mut result := proofs.back!
  for proof in proofs.pop.toList.reverse do
    result ← mkAppM ``And.intro #[proof, result]
  return result

private def conjunctionParts (count : Nat) (proof : Expr) : MetaM (Array Expr) := do
  if count == 0 then return #[]
  let mut result := #[]
  let mut rest := proof
  for _ in [:count - 1] do
    result := result.push (← mkAppM ``And.left #[rest])
    rest ← mkAppM ``And.right #[rest]
  return result.push rest

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
  let feasible ← mkAppM ``PTran.Problem.feasible #[targetProblem]
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
  mkAppM ``PTran.ConstraintDecomposition.mk #[remainderFunction, proof]

/-- The canonical problem and its exact equivalence from the old presentation. -/
structure RewriteResult where
  /-- Explicit canonical problem containing the ordered replacement rows. -/
  targetProblem : Expr
  /-- `GlobalEquivalence` from the old canonical problem to `targetProblem`. -/
  equivalence : Expr

/-- Assemble an exact selected-row replacement from a checked lift and ordered
target rows. `targetIff` identifies the lift target with their conjunction. -/
def rewriteConstraint (presentation : PresentationState) (index : Nat)
    (lift : Expr) (auxiliary? : Option Expr) (nextDomain : Expr)
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
  let targetProblem ← mkAppM ``PTran.Problem.mk #[objective, feasible]
  let (natural, primitive) ← match auxiliary? with
    | none => pure (oldProblem, none)
    | some _ => do
      let decomposition ← makeDecomposition presentation index oldProblem
      let natural ← mkAppM ``PTran.Problem.liftConstraint #[oldProblem, lift, decomposition]
      let primitive ← mkAppM ``PTran.exactConstraintLiftEquivalence
        #[oldProblem, lift, decomposition]
      pure (natural, some primitive)
  let naturalFeasible ← mkAppM ``PTran.Problem.feasible #[natural]
  let feasibleIff ← withLocalDeclD `point nextDomain fun point => do
    let blockIff ← match auxiliary? with
      | none => do
        let target ← mkAppM ``PTran.ExactConstraintLift.target #[lift]
        let exact ← mkAppM ``PTran.ExactConstraintLift.source_iff_exists #[lift]
        let unitIff ← mkAppM ``unitTargetIff #[source, target, exact]
        mkAppM ``Iff.trans #[mkApp unitIff point, mkApp targetIff point]
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
        let generated ← conjunctionParts rows.size (← mkAppM ``Iff.mp #[blockIff, selected])
        conjunctionProof (other.extract 0 index ++ generated ++ other.extract index other.size))
      (fun h => do
        let parts ← conjunctionParts nextRows.size h
        let generated ← conjunctionProof (parts.extract index (index + rows.size))
        let selected ← mkAppM ``Iff.mpr #[blockIff, generated]
        let before := parts.extract 0 index
        let after := parts.extract (index + rows.size) parts.size
        match auxiliary? with
        | none => conjunctionProof (before ++ #[selected] ++ after)
        | some _ => mkAppM ``And.intro #[← conjunctionProof (before ++ after), selected])
    mkLambdaFVars #[point] proof
  let objectiveEq ← withLocalDeclD `point nextDomain fun point => do
    mkLambdaFVars #[point] (← mkEqRefl (mkApp objective point))
  let normalization ← mkAppM ``PTran.pointwiseEquivalence
    #[natural, targetProblem, objectiveEq, feasibleIff]
  let equivalence ← match primitive with
    | none => pure normalization
    | some primitive => mkAppM ``PTran.GlobalEquivalence.trans #[primitive, normalization]
  let targetProblem ← instantiateMVars targetProblem
  let equivalence ← instantiateMVars equivalence
  if targetProblem.hasMVar || equivalence.hasMVar then
    throwError "constraint replacement contains unresolved metavariables"
  checkWithKernel equivalence
  return { targetProblem, equivalence }

end PTran.Elab.Conic
