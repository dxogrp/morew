import Morew.Reformulation.Presentation

/-!
# Objective-bound steps

Proof-producing epigraph and hypograph planning and materialization.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

private def materializeObjectiveBound (state : ReformState)
    (binder : TSyntax `ident)
    (expectedSense : Morew.ObjectiveSense)
    (allocation : Morew.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let some binderName := allocation.findName? 0
    | throwErrorAt binder "internal error: missing objective-bound binder allocation"
  let some constraintName := allocation.findName? 1
    | throwErrorAt binder "internal error: missing objective-bound label allocation"
  let scopedBinderName ← withFreshMacroScope do
    MonadQuotation.addMacroScope binderName

  let (valueType, order, nextSemantic, nextDomainType, primitiveEquivalence) ←
    runTermElabM fun sectionVars => do
      withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
        let typed := state.typed.replaceFVars state.sectionFVars sectionVars
        let equivalenceName := match expectedSense with
          | .minimize => ``Morew.epigraphEquivalence
          | .maximize => ``Morew.hypographEquivalence
        let transformName := match expectedSense with
          | .minimize => ``Morew.Problem.epigraph
          | .maximize => ``Morew.Problem.hypograph
        let equivalence ← mkAppM equivalenceName #[typed.semantic]
        synthesizeSyntheticMVarsNoPostponing
        let equivalence ← instantiateMVars equivalence
        let equivalenceType ← whnf (← inferType equivalence)
        let next := equivalenceType.getAppArgs.back!
        unless next.isAppOfArity transformName 4 do
          throwError "internal error: objective-bound certificate has an unexpected target"
        -- A maximum removes exactly its outer OrderDual. The remaining value
        -- type can itself carry a dual order, which whnf would erase.
        let auxiliaryType := next.getArg! 1
        let order := next.getArg! 2
        let nextType ← whnf (← inferType next)
        pure (← presentationTypeSyntax auxiliaryType, ← exactExpressionSyntax order,
          ← exactExpressionSyntax next, ← exactExpressionSyntax nextType.getAppArgs[0]!,
          ← exactExpressionSyntax equivalence)
  let valueType : TSyntax `term := ⟨valueType⟩
  let newBinder : Morew.Syntax.BinderView := {
    name := scopedBinderName
    typeSyntax := valueType
  }
  let boundName := mkIdent scopedBinderName
  let oldObjective : TSyntax `term := ⟨state.view.objective⟩
  let lessEqual := mkCIdent ``LE.le
  let proposition ← liftMacroM <| match expectedSense with
    | .minimize => `(@$lessEqual $valueType $order $oldObjective $boundName)
    | .maximize => `(@$lessEqual $valueType $order $boundName $oldObjective)
  let constraint : Morew.Syntax.ConstraintView := {
    name := constraintName
    proposition
  }
  let newView : Morew.Syntax.ProblemView := {
    state.view with
    binders := state.view.binders.push newBinder
    objective := boundName
    constraints := state.view.constraints.push constraint
  }

  let primitive ← liftMacroM <|
    liftCertificateEquivalence state.runner primitiveEquivalence
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
    (expectedSense : Morew.ObjectiveSense) :
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
  let binderRequest : Morew.Elab.Reformulation.NameRequest := {
    id := 0
    kind := .explicitDecisionBinder
    requested := binderName
    ref := binder.raw
  }
  let constraintRequest : Morew.Elab.Reformulation.NameRequest := {
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

end Morew.Reformulation.Internal
