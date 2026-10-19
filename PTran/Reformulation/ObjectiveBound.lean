import PTran.Reformulation.State

/-!
# Objective-bound steps

Proof-producing epigraph and hypograph planning and materialization.
-/

namespace PTran.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

private def materializeObjectiveBound (state : ReformState)
    (binder : TSyntax `ident)
    (expectedSense : PTran.Syntax.ObjectiveSense)
    (allocation : PTran.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let some binderName := allocation.findName? 0
    | throwErrorAt binder "internal error: missing objective-bound binder allocation"
  let some constraintName := allocation.findName? 1
    | throwErrorAt binder "internal error: missing objective-bound label allocation"
  let scopedBinderName ← withFreshMacroScope do
    MonadQuotation.addMacroScope binderName

  let valueType : TSyntax `term := ⟨state.presentationValueType⟩
  let newBinder : PTran.Syntax.BinderView := {
    name := scopedBinderName
    typeSyntax := valueType
  }
  let boundName := mkIdent scopedBinderName
  let oldObjective : TSyntax `term := ⟨state.view.objective⟩
  let proposition ← liftMacroM <| match expectedSense with
    | .minimize => `($oldObjective ≤ $boundName)
    | .maximize => `($boundName ≤ $oldObjective)
  let constraint : PTran.Syntax.ConstraintView := {
    name := constraintName
    proposition
  }
  let newView : PTran.Syntax.ProblemView := {
    state.view with
    binders := state.view.binders.push newBinder
    objective := boundName
    constraints := state.view.constraints.push constraint
  }

  let current := state.semantic
  let nextSemantic ← liftMacroM <| match expectedSense with
    | .minimize => `(PTran.Problem.epigraph $current)
    | .maximize => `(PTran.Problem.hypograph $current)
  let primitiveEquivalence ← liftMacroM <| match expectedSense with
    | .minimize => `(PTran.epigraphEquivalence $current)
    | .maximize => `(PTran.hypographEquivalence $current)
  let primitive ← liftMacroM <|
    liftCertificateEquivalence state.runner primitiveEquivalence
  let currentDomainType := state.semanticDomainType
  let valueType := state.semanticValueType
  let nextDomainType ← liftMacroM `($currentDomainType × $valueType)
  pure {
    view := newView
    semantic := nextSemantic
    semanticDomainType := nextDomainType
    primitiveCertificate := primitive
    simplifyExpLogTerms := state.simplifyExpLogTerms
    hasSubstitution := state.hasSubstitution
    removedConstraintNames := state.removedConstraintNames
    normalizationLemmas := state.normalizationLemmas
  }

/-- Plan an epigraph or hypograph step with its binder and constraint-label requests. -/
def prepareObjectiveBound (state : ReformState) (step : Lean.Syntax)
    (binder : TSyntax `ident) (explicitLabel? : Option (TSyntax `ident))
    (expectedSense : PTran.Syntax.ObjectiveSense) :
    CommandElabM SurfaceStepDraft := do
  unless state.view.sense == expectedSense do
    let expected := match expectedSense with
      | .minimize => "epigraph"
      | .maximize => "hypograph"
    let actual := match state.view.sense with
      | .minimize => "minimization"
      | .maximize => "maximization"
    throwErrorAt step "`{expected}` is not valid for a {actual} problem"
  let binderName := binder.getId
  let generatedName := Name.mkSimple <| match expectedSense with
    | .minimize => s!"epigraph_{binderName.eraseMacroScopes}"
    | .maximize => s!"hypograph_{binderName.eraseMacroScopes}"
  let constraintName := match explicitLabel? with
    | some label => label.getId.eraseMacroScopes
    | none => generatedName
  let binderRequest : PTran.Elab.Reformulation.NameRequest := {
    id := 0
    kind := .explicitDecisionBinder
    requested := binderName
    ref := binder.raw
  }
  let constraintRequest : PTran.Elab.Reformulation.NameRequest := {
    id := 1
    kind := if explicitLabel?.isSome then
      .explicitConstraintLabel
    else
      .fixedPublicDefault
    requested := constraintName
    ref := explicitLabel?.map (·.raw) |>.getD binder.raw
  }
  pure {
    nameRequests := #[binderRequest, constraintRequest]
    materialize := fun allocation =>
      materializeObjectiveBound state binder expectedSense allocation
  }

end PTran.Reformulation.Internal
