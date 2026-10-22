import PTran.Elab.Conic.Plan

/-!
# Persistent certified conic forms

Build affine cone data for the complete current typed problem. The stored
representation proves equality of objective and feasibility, independently of
the reformulation runner's source-to-target optimization certificate.

For abstract function indices, certification accepts `Finite` evidence. Ordinary
norm-dependent field notation follows mathlib's `Fintype` prerequisites; callers
with only `Finite ι` can install `letI := Fintype.ofFinite ι` when using the data.
-/

namespace PTran.Elab.Conic

open Lean Lean.Meta
open Reformulation

private theorem problemEq {X : Type u} {V : Type v} (p q : PTran.Problem X V)
    (objective : ∀ x, p.objective x = q.objective x)
    (feasible : ∀ x, p.feasible x ↔ q.feasible x) : p = q := by
  cases p with
  | mk po pf =>
    cases q with
    | mk qo qf =>
      exact congrArg₂ PTran.Problem.mk (funext objective)
        (funext fun x => propext (feasible x))

private theorem emptyRows {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : X) :
    (∀ i : Fin 0, (Fin.elim0 i : PTran.Conic.Constraint X).Holds x) ↔ True :=
  Fin.forall_fin_zero

private def prependRow {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : Nat} (row : PTran.Conic.Constraint X)
    (rest : Fin n → PTran.Conic.Constraint X) : Fin (n + 1) → PTran.Conic.Constraint X :=
  Fin.cons row rest

private theorem consRows {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : Nat} (row : PTran.Conic.Constraint X)
    (rest : Fin n → PTran.Conic.Constraint X) (x : X) :
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
  let rowType ← mkAppOptM ``PTran.Conic.Constraint #[some domain, none, none]
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

private def buildFormCore (presentation : PresentationState) (config : Affine.Config) :
    MetaM (Except Affine.AffineError Expr) := do
  for expression in #[presentation.domainType, presentation.valueType, presentation.objective] ++
      presentation.binders.map (·.type) ++ presentation.constraints.map (·.predicate) do
    if ← Plan.unresolved expression then
      return .error {
        expression
        reason := ← addMessageContext "conic form: unresolved metavariables in typed presentation"
      }
  let canonical ← presentation.canonicalProblem
  let objective ← match ← reifyObjective presentation config with
    | .error error => return .error error
    | .ok result => pure result
  let mut blocks := #[]
  for entry in presentation.constraints do
    let (predicates, decomposition) ← try
      decomposePredicate entry.predicate
    catch error =>
      return .error {
        expression := entry.predicate
        reason := ← addMessageContext m!"constraint `{entry.name}`: {error.toMessageData}"
      }
    let mut rows := #[]
    for predicate in predicates do
      match ← normalizeRow predicate config (some entry.name) with
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
      | .minimize => ``PTran.ObjectiveSense.minimize
      | .maximize => ``PTran.ObjectiveSense.maximize
    let data ← mkAppM ``PTran.Conic.Data.mk
      #[sense, objective.map, mkNatLit rows.size, constraints]
    let represented ← mkAppM ``PTran.Conic.Data.toProblem #[data]
    let equality ← mkAppM ``problemEq
      #[represented, canonical, objective.pointwiseEquality, feasibleIff]
    let form ← instantiateMVars (← mkAppM ``PTran.Conic.Form.mk #[data, equality])
    let expected ← mkAppM ``PTran.Conic.Form #[canonical]
    unless ← isDefEq (← inferType form) expected do
      throwError "conic form does not represent the current canonical problem"
    if form.hasMVar then
      throwError "conic form contains unresolved metavariables"
    checkWithKernel form
    return form
  -- A declaration inferred directly from this expression must support ordinary
  -- `.data` projections. Keep its explicit instances, while exposing aliases in
  -- the domain so later typeclass search can recognize the structural space.
  let formType ← inferType form
  let domain ← Space.structuralDomain presentation.domainType
  let publicType := mkAppN formType.getAppFn (formType.getAppArgs.set! 0 domain)
  let form ← mkAppOptM ``id #[some publicType, some form]
  checkWithKernel form
  return .ok form

/-- Certify the complete current typed problem as persistent affine cone data.
Conjunction leaves retain presentation order; literal `True` contributes no
rows. The returned form represents `presentation.canonicalProblem` exactly and
retains the explicit objective sense, including maximizing declarations. -/
def buildForm (presentation : PresentationState) (config : Affine.Config := {}) :
    MetaM (Except Affine.AffineError Expr) :=
  Affine.withIsolatedMVars do
    try
      let mut instances := #[]
      for source in #[presentation.objective] ++ presentation.constraints.map (·.predicate) do
        for inst in ← Affine.sourceFiniteInstances source do
          unless instances.contains inst do
            instances := instances.push inst
      Plan.withScopedFiniteInstances
        (fun result oldVars newVars => result.map (·.replaceFVars oldVars newVars))
        instances.toList (buildFormCore presentation config)
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext m!"conic form: {error.toMessageData}"
      }

end PTran.Elab.Conic
