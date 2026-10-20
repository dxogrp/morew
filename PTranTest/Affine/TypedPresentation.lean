import PTran.Elab.Conic
import PTran.Elab.Reformulation.Presentation

/-!
# Affine recognition through typed presentation entries

Objective and constraint adapters consume typed entries, preserve both
optimization senses and the explicit order-dual type, and report objective
context without importing the surface syntax.
-/

assert_not_exists PTran.Syntax.ProblemView PTran.elabProblem PTran.elabPrintProblem

namespace PTranTest.Affine.TypedPresentation

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open PTran

noncomputable section

/-! Rows consume the typed predicates directly and retain the optimization
sense independently of the reducible real order-dual type. -/

private def checkPresentation (sense : ObjectiveSense) : TermElabM Unit := do
  let real := Lean.mkConst ``Real
  let valueType ← if sense == .maximize then mkAppM ``OrderDual #[real] else pure real
  let objective ← elabTerm (← `(fun x : ℝ => -x + 2)) none
  let predicate ← elabTerm (← `(fun x : ℝ => x + 1 ≤ 4)) none
  synthesizeSyntheticMVarsNoPostponing
  let presentation : PTran.Elab.Reformulation.PresentationState := {
    sense
    domainType := real
    valueType
    binders := #[{ name := `x, type := real }]
    objective := ← instantiateMVars objective
    constraints := #[{ name := `upper, predicate := ← instantiateMVars predicate }]
  }
  let canonical ← presentation.canonicalProblem
  check canonical
  match ← PTran.Elab.Conic.reifyObjective presentation with
  | .error error => throwError "typed presentation objective was not recognized: {error.reason}"
  | .ok objectiveResult => check objectiveResult.pointwiseEquality
  let entry := presentation.constraints[0]!
  let .ok row ← PTran.Elab.Conic.normalizeConstraint entry
    | throwError "typed presentation row was not recognized"
  check row.pointwiseIff
  unless presentation.sense == sense do
    throwError "normalization changed optimization sense"
  unless ← isDefEq presentation.valueType valueType do
    throwError "normalization changed objective-value type"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkPresentation .minimize
  checkPresentation .maximize
  let real := Lean.mkConst ``Real
  let objective ← elabTerm (← `(fun x : ℝ => (x, x))) none
  synthesizeSyntheticMVarsNoPostponing
  let presentation : PTran.Elab.Reformulation.PresentationState := {
    sense := .minimize
    domainType := real
    valueType := ← mkAppM ``Prod #[real, real]
    binders := #[{ name := `x, type := real }]
    objective := ← instantiateMVars objective
  }
  let .error error ← PTran.Elab.Conic.reifyObjective presentation
    | throwError "typed objective adapter accepted a vector-valued objective"
  unless (← error.reason.toString).contains "objective: expected a real-valued" do
    throwError "missing real-objective diagnostic"

end

end PTranTest.Affine.TypedPresentation
