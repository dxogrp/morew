import Morew.Elab.Conic.Form
import MorewTest.Affine.Support

/-!
# Whole-problem conic forms

Persistent forms retain exact objective and feasibility equality. Typed checks
exercise nested conjunctions, empty tables, maximizing sense, finite indexing,
and independence from unrelated ambient vector-space instances.
-/

namespace MorewTest.Conic.Form

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Morew

noncomputable section

private def presentationFor (source : Expr) (sense : ObjectiveSense := .minimize)
    (noConstraints : Bool := false) : MetaM Elab.Reformulation.PresentationState := do
  let type ← whnf (← inferType source)
  unless type.isAppOfArity ``Problem 2 do throwError "expected a problem"
  let domain := type.getAppArgs[0]!
  let feasible ← mkAppM ``Problem.feasible #[source]
  return {
    sense
    domainType := domain
    valueType := type.getAppArgs[1]!
    binders := #[{ name := `x, type := domain }]
    objective := ← mkAppM ``Problem.objective #[source]
    constraints := if noConstraints then #[] else #[{ name := `bounds, predicate := feasible }]
  }

private def requireForm (presentation : Elab.Reformulation.PresentationState)
    (certifiedRows : Array (Option (Array Elab.Conic.RowResult)) := #[]) : MetaM Expr := do
  match ← Elab.Conic.buildForm presentation {} certifiedRows with
  | .error error => throwError "expected conic form: {error.reason}"
  | .ok form =>
    if form.hasMVar || form.hasSorry then throwError "incomplete conic form"
    checkWithKernel form
    return form

elab "form_for% " source:term : term => do
  let source ← MorewTest.Affine.elaborate source
  requireForm (← presentationFor source)

elab "max_form_for% " source:term : term => do
  let source ← MorewTest.Affine.elaborate source
  requireForm (← presentationFor source .maximize)

def nested : Problem ℝ ℝ where
  objective x := 2 * x + 1
  feasible x := (True ∧ x = 3) ∧ ((x ≥ 1 ∧ True) ∧ x ≤ 5)

def nestedForm : Conic.Form nested := form_for% nested

-- Inferred declarations retain the builder's explicit instance expressions.
-- Ordinary field notation must still synthesize their compatible structures.
def inferredNestedForm := form_for% nested

example : inferredNestedForm.data.rowCount = 3 := rfl
example : inferredNestedForm.data.sense = .minimize := rfl
example (x : ℝ) : inferredNestedForm.data.objective x = 2 * x + 1 := by
  exact congrArg (fun p : Problem ℝ ℝ => p.objective x) inferredNestedForm.represents

example : nestedForm.data.rowCount = 3 := rfl
example : nestedForm.data.sense = .minimize := rfl
example : nestedForm.data.toProblem = nested := nestedForm.represents
example : IsConic nested := nestedForm.isConic
example (x : ℝ) : nestedForm.data.objective x = 2 * x + 1 := by
  exact congrArg (fun p : Problem ℝ ℝ => p.objective x) nestedForm.represents
example (x : ℝ) :
    (∀ i, (nestedForm.data.constraints i).Holds x) ↔ nested.feasible x := by
  change nestedForm.data.toProblem.feasible x ↔ nested.feasible x
  rw [nestedForm.represents]

def maximizing : Problem (ℝ × ℝ) (OrderDual ℝ) where
  objective x := (x.1 - 2 * x.2 : ℝ)
  feasible x := x.1 ≤ x.2 ∧ True

def maximizingForm : Conic.Form maximizing := max_form_for% maximizing

def inferredMaximizingForm := max_form_for% maximizing

example : inferredMaximizingForm.data.sense = .maximize := rfl
example : inferredMaximizingForm.data.rowCount = 1 := rfl

example : maximizingForm.data.sense = .maximize := rfl
example : maximizingForm.data.rowCount = 1 := rfl
example : maximizingForm.data.toProblem = maximizing := maximizingForm.represents

def vacuous : Problem (Fin 2 → Fin 3 → ℝ) ℝ where
  objective _ := 4
  feasible _ := (True ∧ True) ∧ True

def vacuousForm : Conic.Form vacuous := form_for% vacuous

example : vacuousForm.data.rowCount = 0 := rfl
example : vacuousForm.data.toProblem = vacuous := vacuousForm.represents

def inferredVectorForm (n : Nat) := form_for% (show Problem (Fin n → ℝ) ℝ from
  ⟨fun _ => 0, fun x => x ≤ fun _ => 1⟩)

example (n : Nat) : (inferredVectorForm n).data.rowCount = 1 := rfl
example (n : Nat) (x : Fin n → ℝ) : (inferredVectorForm n).data.objective x = 0 := rfl

def inferredMatrixForm := form_for% (show Problem (Matrix (Fin 2) (Fin 3) ℝ) ℝ from
  ⟨fun x => x 0 1, fun x => x 0 1 ≤ 1⟩)

example : inferredMatrixForm.data.rowCount = 1 := rfl
example (x : Matrix (Fin 2) (Fin 3) ℝ) : inferredMatrixForm.data.objective x = x 0 1 := rfl

def inferredEuclideanForm (n : Nat) := form_for%
  (show Problem (EuclideanSpace ℝ (Fin n) × ℝ) ℝ from
    ⟨fun x => x.2, fun x => (x.2, WithLp.ofLp x.1) ∈
      (Conic.Cone.secondOrder n).carrier⟩)

example (n : Nat) : (inferredEuclideanForm n).data.rowCount = 1 := rfl

def inferredIndexForm (ι : Type) [Fintype ι] (i : ι) :=
  form_for% (show Problem (ι → ℝ) ℝ from ⟨fun x => x i, fun x => x i ≤ 1⟩)

example (ι : Type) [Fintype ι] (i : ι) : (inferredIndexForm ι i).data.rowCount = 1 := rfl

def inferredFiniteForm (ι : Type) [Finite ι] (i : ι) :=
  form_for% (show Problem (ι → ℝ) ℝ from ⟨fun x => x i, fun x => x i ≤ 1⟩)

-- Mathlib's ordinary finite-function norm instances require an enumeration at
-- the point of use; the form itself needs only a finiteness proof.
example (ι : Type) [Finite ι] (i : ι) :
    letI := Fintype.ofFinite ι
    (inferredFiniteForm ι i).data.rowCount = 1 := rfl

namespace AliasedFiniteIndex

def IndexAlias := Fin 2
def VectorAlias := IndexAlias → ℝ

local instance : Finite IndexAlias := by
  change Finite (Fin 2)
  infer_instance
local instance : Fintype IndexAlias := Fintype.ofFinite IndexAlias

def first : IndexAlias := (0 : Fin 2)

def source : Problem VectorAlias ℝ where
  objective x := x first
  feasible x := x first ≤ 1

-- Expose the vector alias while retaining the index alias and its enumeration.
-- Both ordinary projections must work directly on the inferred declaration.
def inferredForm := form_for% source

example : inferredForm.data.rowCount = 1 := rfl
example : inferredForm.data.toProblem = source := inferredForm.represents

end AliasedFiniteIndex

private def assertForm (termSyntax : TSyntax `term) (count : Nat)
    (parameterCount : Nat := 0) (noConstraints : Bool := false) : TermElabM Unit := do
  let expression ← MorewTest.Affine.elaborate termSyntax
  lambdaBoundedTelescope expression parameterCount fun parameters source => do
    let presentation ← presentationFor source (noConstraints := noConstraints)
    let form ← requireForm presentation
    let data ← mkProjection form `data
    let rowCount ← whnf (← mkProjection data `rowCount)
    unless ← isDefEq rowCount (mkNatLit count) do
      throwError "expected {count} rows, got {rowCount}"
    let canonical ← presentation.canonicalProblem
    let type ← inferType form
    unless ← isDefEq type.getAppArgs.back! canonical do
      throwError "form represents a different problem"
    for parameter in parameters do
      let type ← whnf (← inferType parameter)
      if type.isAppOf ``NormedAddCommGroup || type.isAppOf ``NormedSpace ||
          type.isAppOf ``AddCommGroup || type.isAppOf ``_root_.Module then
        if form.containsFVar parameter.fvarId! then
          throwError "conic form captured an unrelated ambient vector-space instance"
    let closed ← mkLambdaFVars parameters form
    if closed.hasFVar || closed.hasMVar then
      throwError "temporary canonical instances escaped the form"
    checkWithKernel closed

run_cmd Lean.Elab.Command.liftTermElabM do
  assertForm (← `(show Problem ℝ ℝ from ⟨fun x => x, fun _ => True⟩)) 0
    (noConstraints := true)
  assertForm (← `(fun (n : Nat) => show Problem (Fin n → ℝ) ℝ from
    ⟨fun _ => 0, fun _ => True⟩)) 0 1 (noConstraints := true)
  assertForm (← `(fun (ι : Type) [Finite ι] (i : ι) =>
    show Problem ((ι → ℝ) × ℝ) ℝ from
    ⟨fun x => x.1 i + x.2, fun x => x.1 i ≤ x.2⟩)) 1 3
  assertForm (← `(fun (n : Nat) => show Problem (EuclideanSpace ℝ (Fin n) × ℝ) ℝ from
    ⟨fun x => x.2, fun x => (x.2, WithLp.ofLp x.1) ∈
      (Conic.Cone.secondOrder n).carrier⟩)) 1 1
  assertForm (← `(fun [NormedAddCommGroup ℝ] [NormedSpace ℝ ℝ] =>
    show Problem (ℝ × ℝ) ℝ from ⟨fun x => x.1 + x.2, fun x => x.1 ≤ x.2⟩)) 1 2
  assertForm (← `(fun [AddCommGroup (Matrix (Fin 2) (Fin 3) ℝ)]
      [Module ℝ (Matrix (Fin 2) (Fin 3) ℝ)] =>
    show Problem (Matrix (Fin 2) (Fin 3) ℝ) ℝ from
    ⟨fun x => x 0 1, fun x => x 0 1 ≥ 0⟩)) 1 2

-- Independent denominator evidence survives conjunction splitting.
run_cmd Lean.Elab.Command.liftTermElabM do
  assertForm (← `(fun (c : ℝ) (hc : c ≠ 0) =>
    show Problem ℝ ℝ from ⟨fun x => x, fun x =>
      let localEvidence : c ≠ 0 := hc
      (x / c ≤ 2 ∧ True) ∧ x ≥ 0⟩)) 2 2
  assertForm (← `(fun (ι : Type) (enumeration : Fintype ι) (i : ι) =>
    show Problem (ι → ℝ) ℝ from
      ⟨fun x => x i, fun x =>
        letI : Fintype ι := enumeration
        x i ≤ Fintype.card ι⟩)) 1 3

-- A finiteness proof exposed by one source leaf supplies the canonical domain
-- instances for the constant objective and for other, evidence-free leaves.
run_cmd Lean.Elab.Command.liftTermElabM do
  assertForm (← `(fun (ι : Type) (evidence : Finite ι ∧ True) (i : ι) =>
    show Problem (ι → ℝ) ℝ from
      ⟨fun _ => 0, fun x =>
        (let finiteEvidence : Finite ι := evidence.1; x i ≤ 1) ∧ 0 ≤ x i⟩)) 2 3

-- Multiple named entries preserve their boundaries in the exact represented
-- predicate even when each contributes a different number of stored rows.
run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← MorewTest.Affine.elaborate (← `(show Problem ℝ ℝ from
    ⟨fun x => x, fun _ => True⟩))
  let initial ← presentationFor source
  let first ← MorewTest.Affine.elaborate (← `(fun x : ℝ => True ∧ x ≤ 3))
  let middle ← MorewTest.Affine.elaborate (← `(fun _ : ℝ => True))
  let last ← MorewTest.Affine.elaborate (← `(fun x : ℝ => (0 ≤ x ∧ x = 1) ∧ True))
  let presentation := { initial with constraints := #[
    { name := `upper, predicate := first },
    { name := `empty, predicate := middle },
    { name := `lower, predicate := last }] }
  let form ← requireForm presentation
  let data ← mkProjection form `data
  unless ← isDefEq (← mkProjection data `rowCount) (mkNatLit 3) do
    throwError "wrong number of rows across named blocks"

-- A planner may certify a row while source-local evidence is available, then
-- retain only the bare predicate. The cached certificate must remain usable
-- after the local let is removed, without rediscovering its nonzero proof.
run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (c : ℝ) (hc : True ∧ c ≠ 0) =>
    show Problem ℝ ℝ from ⟨fun x => x, fun x =>
      let localEvidence : c ≠ 0 := hc.2
      x / c ≤ 2⟩))
  lambdaBoundedTelescope expression 2 fun parameters source => do
    let initial ← presentationFor source
    let predicate := initial.constraints[0]!.predicate
    let .ok row ← Elab.Conic.normalizeRow predicate
      | throwError "source-local nonzero evidence did not certify the original row"
    let bare ← withLocalDeclD `point initial.domainType fun point => do
      mkLambdaFVars #[point] (← Elab.Affine.reduceStructure (mkApp predicate point))
    let empty ← MorewTest.Affine.elaborate (← `(fun _ : ℝ => True))
    let presentation := { initial with constraints := #[
      { name := `bounds, predicate := bare }, { name := `empty, predicate := empty }] }
    let .error error ← Elab.Conic.buildForm presentation
      | throwError "bare predicate unexpectedly rediscovered source-local nonzero evidence"
    unless (← error.reason.toString).contains "nonzero evidence" do
      throwError "bare row failed for the wrong reason: {error.reason}"
    let form ← requireForm presentation #[some #[row], none]
    let data ← mkProjection form `data
    unless ← isDefEq (← mkProjection data `rowCount) (mkNatLit 1) do
      throwError "cached row changed the represented row count"
    let canonical ← presentation.canonicalProblem
    unless ← isDefEq (← inferType form).getAppArgs.back! canonical do
      throwError "cached row changed the represented problem"
    let closed ← mkLambdaFVars parameters form
    if closed.hasFVar || closed.hasMVar then
      throwError "source-local evidence escaped the cached form"
    checkWithKernel closed

private def rejectCachedForm (presentation : Elab.Reformulation.PresentationState)
    (certifiedRows : Array (Option (Array Elab.Conic.RowResult)))
    (fragment : String) : MetaM Unit := do
  let .error error ← Elab.Conic.buildForm presentation {} certifiedRows
    | throwError "invalid row cache received a conic form"
  unless (← error.reason.toString).contains fragment do
    throwError "missing cached-row diagnostic: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let source ← MorewTest.Affine.elaborate (← `(show Problem ℝ ℝ from
    ⟨fun x => x, fun x => x ≤ 1⟩))
  let presentation ← presentationFor source
  let predicate := presentation.constraints[0]!.predicate
  let rows ← Elab.Conic.Plan.certifyRows #[predicate]
  let wrong ← MorewTest.Affine.elaborate (← `(fun x : ℝ => 0 ≤ x))
  let wrongRows ← Elab.Conic.Plan.certifyRows #[wrong]
  rejectCachedForm presentation #[some wrongRows] "does not match its decomposed predicate"
  rejectCachedForm presentation #[some rows, none] "entry count"
  rejectCachedForm presentation #[some #[]] "decomposed predicate count"
  let some row := rows[0]? | throwError "missing certified fixture row"
  let unresolved ← mkFreshExprMVar (← inferType row.pointwiseIff)
  let incomplete := { row with pointwiseIff := unresolved }
  rejectCachedForm presentation #[some #[incomplete]] "unresolved metavariables"
  if ← unresolved.mvarId!.isAssigned then
    throwError "cached-row validation assigned a caller metavariable"

private def rejectForm (termSyntax : TSyntax `term) (fragment : String) : TermElabM Unit := do
  let source ← MorewTest.Affine.elaborate termSyntax
  let .error error ← Elab.Conic.buildForm (← presentationFor source)
    | throwError "unsupported problem received a conic form"
  unless (← error.reason.toString).contains fragment do
    throwError "missing diagnostic context: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  rejectForm (← `(show Problem ℝ ℝ from
    ⟨fun x => x * x, fun _ => True⟩)) "objective"
  rejectForm (← `(show Problem ℝ ℝ from
    ⟨fun x => x, fun x => (True ∧ x ≤ 1) ∧ x * x ≤ 4⟩)) "bounds"
  rejectForm (← `(show Problem ℝ ℝ from
    ⟨fun x => x, fun x => x < 1⟩)) "non-strict"

end

end MorewTest.Conic.Form
