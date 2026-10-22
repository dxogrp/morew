import PTran.Reformulation.Presentation
import PTran.Syntax
import PTran.Elab.Conic

/-!
# Canonicalization checkpoints and ordered row replacements

An explicit canonical problem must retain its row boundaries across later
substitution and objective-bound steps. A generated row family replaces the
selected row in place rather than moving to the end of the presentation.
-/

namespace PTranTest.Reformulation.CanonicalCheckpoint

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open PTran.Reformulation.Internal

noncomputable section

def InDomain (x : ℝ) : Prop := 0 < x

theorem inDomain_iff (x : ℝ) : InDomain x ↔ 0 < x := Iff.rfl

def source :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      grouped : x ≤ 3 ∧ 0 ≤ x
      positive : InDomain x

run_cmd Lean.Elab.Command.liftTermElabM do
  let some view := PTran.Syntax.getProblemView? (← getEnv) ``source
    | throwError "missing test source presentation"
  -- This term deliberately contains no reference to `source`. It models the
  -- explicit canonical checkpoint established by a constraint rewrite.
  let checkpoint ← `(PTran.Problem.mk
    (fun x : ℝ => Real.log x)
    (fun x : ℝ => (x ≤ 3 ∧ 0 ≤ x) ∧ InDomain x))
  let semantic ← `(PTran.Problem.epigraph
    (PTran.Problem.pullback $checkpoint (fun y : ℝ => Real.exp y)))
  let canonical ← canonicalTargetExpression ``source checkpoint view
    (({} : NameSet).insert `positive) semantic true
  let expected ← elabTerm (← `(PTran.Problem.mk
    (fun point : ℝ × ℝ => point.2)
    (fun point : ℝ × ℝ =>
      (Real.exp point.1 ≤ 3 ∧ 0 ≤ Real.exp point.1) ∧ point.1 ≤ point.2))) none
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq canonical (← instantiateMVars expected) do
    throwError "checkpoint normalization changed grouped rows or failed to remove aliased positivity"
  let semanticExpr ← elabTerm semantic none
  synthesizeSyntheticMVarsNoPostponing
  discard <| checkedPointwiseNormalization ``source
    (← instantiateMVars semanticExpr) canonical #[← `(inDomain_iff)]
  let nextView : PTran.Syntax.ProblemView := {
    view with
    binders := view.binders.push { name := `bound, typeSyntax := ← `(ℝ) }
    constraints := #[view.constraints[0]!, {
      name := `bound_row
      proposition := ← `(True)
    }]
  }
  let presentation ← typedPresentationFromExpression canonical nextView
  withLocalDeclD `point presentation.domainType fun point => do
    let first ← whnf (mkApp presentation.constraints[0]!.predicate point)
    unless first.isAppOfArity ``And 2 do
      throwError "checkpoint normalization split the interior of an unselected named row"

run_cmd Lean.Elab.Command.liftTermElabM do
  let some view := PTran.Syntax.getProblemView? (← getEnv) ``source
    | throwError "missing test source presentation"
  let base ← canonicalTargetExpression ``source (← `(source)) view {} (← `(source)) false
  let current ← typedPresentationFromExpression base view
  let selected := current.constraints[0]!
  let next := { current with constraints := #[
    { selected with name := `generated_1 },
    { selected with name := `generated_2 },
    current.constraints[1]!
  ] }
  let normalization ← checkedPointwiseNormalization ``source base base #[]
  let delta ← presentationDeltaBetween current next
    normalization.objectiveEquality normalization.feasibleIff
    #[{ index := 0, count := 2 }]
  let .ok actual := current.applyDelta delta
    | throwError "valid generated-row splice was rejected"
  unless actual.constraints.map (·.name) == #[`generated_1, `generated_2, `positive] do
    throwError "generated rows were appended instead of replacing the selected row"
  unless delta.constraintAdditions.isEmpty do
    throwError "a spliced row was also recorded as a tail addition"
  let invalid := { next with constraints := #[
    current.constraints[1]!, next.constraints[0]!, next.constraints[1]!
  ] }
  let rejected ← try
    discard <| presentationDeltaBetween current invalid
      normalization.objectiveEquality normalization.feasibleIff
      #[{ index := 0, count := 2 }]
    pure false
  catch _ => pure true
  unless rejected do
    throwError "a splice that moved an unselected row was accepted"

def constantSource :=
  problem (x : ℝ)
    minimize (0 : ℝ)
    subject to
      cap : x ≤ 2

run_cmd Lean.Elab.Command.liftTermElabM do
  let some view := PTran.Syntax.getProblemView? (← getEnv) ``constantSource
    | throwError "missing constant-objective source presentation"
  let canonical ← canonicalTargetExpression ``constantSource
    (← `(constantSource)) view {} (← `(constantSource)) false
  let objective ← mkAppM ``PTran.Problem.objective #[canonical]
  let objective ← simpOnly objective
  if (objective.find? fun expression => expression.isConstOf ``constantSource).isSome then
    throwError "a bare protected objective was restored as a source projection"
  let expected ← elabTerm (← `(fun _ : ℝ => (0 : ℝ))) none
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq objective (← instantiateMVars expected) do
    throwError "normalizing the bare protected objective changed its value"

end

/-! A constant generated row has no decision-dependent operand from which the
elaborator could infer its numeric type. Stable syntax must retain that type. -/
run_cmd do
  let original ← liftMacroM `(PTran.Problem.mk
    (fun x : ℝ => x) (fun _ : ℝ => (0 : ℝ) ≤ 2))
  let stable ← stabilizeTerm original
  Lean.Elab.Command.runTermElabM fun _ => do
    let expected ← elabTerm original none
    let actual ← elabTerm stable none
    synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    let actual ← instantiateMVars actual
    unless ← isDefEq expected actual do
      throwError "stabilizing a constant real row changed its numeric type"
    let feasible ← mkAppM ``PTran.Problem.feasible #[actual]
    let .ok row ← PTran.Elab.Conic.normalizeRow feasible
      | throwError "the stabilized constant row is no longer a real affine inequality"
    checkWithKernel row.pointwiseIff

namespace SectionCapture

class Datum where
  dimension : Nat

section

variable [Datum] [Datum]

/-! Retain the first anonymous instance deliberately. Replacing captured locals
with typeclass synthesis would silently select the second instance instead. -/
set_option linter.overlappingInstances false in
run_cmd do
  let exact ← Lean.Elab.Command.runTermElabM fun sectionFVars => do
    unless sectionFVars.size == 2 do
      throwError "expected two independent anonymous instances"
    exactExpressionSyntax sectionFVars[0]!
  let stable ← stabilizeTerm exact
  let exactDimensionType ← Lean.Elab.Command.runTermElabM fun sectionFVars => do
    let dimension := mkApp (mkConst ``Datum.dimension) sectionFVars[0]!
    exactExpressionSyntax (← mkAppM ``Fin #[dimension])
  let stableDimensionType ← stabilizeTerm exactDimensionType
  Lean.Elab.Command.runTermElabM fun sectionFVars => do
    for serialized in #[exact, stable] do
      let actual ← elabTerm serialized none
      synthesizeSyntheticMVarsNoPostponing
      unless (← instantiateMVars actual) == sectionFVars[0]! do
        throwError "serialized section reference selected a different anonymous instance"
    let actualDimensionType ← elabTerm stableDimensionType none
    synthesizeSyntheticMVarsNoPostponing
    let dimension := mkApp (mkConst ``Datum.dimension) sectionFVars[0]!
    let expectedDimensionType ← mkAppM ``Fin #[dimension]
    unless ← isDefEq (← instantiateMVars actualDimensionType) expectedDimensionType do
      throwError "stabilization changed an implicit captured section instance"

end
end SectionCapture

end PTranTest.Reformulation.CanonicalCheckpoint
