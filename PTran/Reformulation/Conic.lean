import PTran.Elab.Conic.Polyhedral
import PTran.Elab.Conic.SecondOrder
import PTran.Elab.Conic.Rewrite
import PTran.Reformulation.Presentation
import Lean.Meta.Closure

/-!
# Targeted exact conic rewriting

The surface handler selects one current presentation label, preflights the
generated name family, and materializes a checked in-place replacement.

`conic at label` recognizes whole upper bounds on absolute value, positive part,
maximum, finite `Finset.sup'`, and native one/infinity norms, and whole lower
bounds on minimum and finite `Finset.inf'`. Finite sets must be nonempty and
decision-independent. The ordinary norm of `Fin n → ℝ` is the infinity norm;
the one-norm is written `‖WithLp.toLp 1 v‖` for an ordinary finite real vector.

Coordinate bounds remain grouped vector inequalities, with one selectable name
per row. Names use the selected label's decoded final component followed by
`_conic_1`, `_conic_2`, and so on; a vector auxiliary uses `_aux`. The runner
freshens collisions numerically. The original selected label is consumed.

`conic at label using rule` accepts an existing exact-lift, graph, epigraph, or
hypograph representation of the entire predicate. Its inspectable target may
contain `True`, conjunctions, and affine scalar/vector equalities or non-strict
inequalities. Every generated row is certified independently of the objective
or other constraints. Supported SOC and rotated-SOC memberships are also valid
custom target rows.

Native Euclidean norms, scalar squares, and finite sums of squares become one
SOC or rotated-SOC membership row. Quotients of squares require a positive
constant lower margin on the denominator, obtained from an unchanged constraint
(or a directly proved positive constant denominator). Existing margin rows stay
in place. The command remains nonterminal and does not certify a whole problem
as conic.
-/

namespace PTran.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open PTran.Elab.Reformulation

private def rebaseExactPlan (result : PTran.Elab.Conic.Plan.Result)
    (oldVars newVars : Array Expr) : PTran.Elab.Conic.Plan.Result := {
  lift := result.lift.replaceFVars oldVars newVars
  auxiliary? := result.auxiliary?.map (·.replaceFVars oldVars newVars)
  nextDomain := result.nextDomain.replaceFVars oldVars newVars
  rowPredicates := result.rowPredicates.map (·.replaceFVars oldVars newVars)
  targetIff := result.targetIff.replaceFVars oldVars newVars
  certifiedRows := result.certifiedRows.map fun row => {
    constraint := row.constraint.replaceFVars oldVars newVars
    pointwiseIff := row.pointwiseIff.replaceFVars oldVars newVars
  }
}

private abbrev Prepared := Sum PTran.Elab.Conic.Plan.Result PTran.Elab.Conic.SecondOrder.Result

private def Prepared.replaceFVars (prepared : Prepared) (oldVars newVars : Array Expr) : Prepared :=
  match prepared with
  | .inl exact => .inl (rebaseExactPlan exact oldVars newVars)
  | .inr contextual => .inr (contextual.replaceFVars oldVars newVars)

private def Prepared.rowPredicates : Prepared → Array Expr
  | .inl exact => exact.rowPredicates
  | .inr contextual => contextual.rowPredicates

private def Prepared.auxiliary? : Prepared → Option Expr
  | .inl exact => exact.auxiliary?
  | .inr _ => none

private def Prepared.nextDomain : Prepared → Expr
  | .inl exact => exact.nextDomain
  | .inr contextual => contextual.domain

private def Prepared.certificate : Prepared → Expr
  | .inl exact => exact.lift
  | .inr contextual => contextual.conditionalIff

private def generatedStem (selector : TSyntax `ident) : CommandElabM String := do
  let .str _ stem := selector.getId.eraseMacroScopes
    | throwErrorAt selector "cannot derive a generated-name family from constraint `{selector.getId}`"
  if stem.isEmpty then
    throwErrorAt selector "cannot derive a generated-name family from an empty constraint label"
  return stem

-- A row predicate occurs repeatedly in the explicit types and arguments of
-- the conjunction proofs. Keep those predicates, then their containing lift
-- and problems, shared in the stored certificate instead of duplicating large
-- vector predicates at every use.
private partial def shareCertificate (certificate : Expr)
    (candidates : List (Name × Expr)) : MetaM Expr := do
  match candidates with
  | [] => pure certificate
  | (name, value) :: remaining =>
    withLetDecl name (← inferType value) value fun binding => do
      let replace := fun expression : Expr => expression.replace fun subexpression =>
        if subexpression == value then some binding else none
      let body ← shareCertificate (replace certificate)
        (remaining.map fun (name, value) => (name, replace value))
      mkLetFVars #[binding] body

private def materializeConic (state : ReformState) (index : Nat)
    (prepared : Prepared) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    -- Section proof parameters may still mention assigned instance variables.
    -- The kernel needs their instantiated local types as well as the term.
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared := prepared.replaceFVars preparedVars sectionFVars
    let replacement ← match prepared with
      | .inl result => do
        PTran.Elab.Conic.rewriteConstraint typed.presentation index
          result.lift result.auxiliary? result.nextDomain result.rowPredicates result.targetIff
      | .inr contextual => do
        PTran.Elab.Conic.rewriteConstraintContextual typed.presentation index
          contextual.rowPredicates contextual.conditionalIff
    let exact ← mkAppM ``PTran.GlobalEquivalence.trans
      #[typed.normalization.equivalence, replacement.equivalence]
    let primitive ← state.runner.liftEquivalence exact
    let primitive ← instantiateMVars primitive
    let predicates := typed.presentation.constraints.map (·.predicate) ++
      prepared.rowPredicates
    let candidates := predicates.toList.zipIdx.map fun (predicate, index) =>
      (Name.mkSimple s!"conic_row_{index}", predicate)
    let primitive ← shareCertificate primitive (candidates ++ [
      (`conic_certificate, prepared.certificate),
      (`conic_source, typed.canonical),
      (`conic_target, replacement.targetProblem)])
    checkWithKernel primitive
    -- Store the checked proof data once before the syntax round trip. Later
    -- steps and the final declaration then refer to this constant instead of
    -- re-elaborating its conjunction proofs. The closure retains section
    -- parameters; the enclosing command transaction rolls it back on failure.
    let primitiveName ← mkAuxDeclName (kind := `_conicCertificate)
    let primitive ← mkAuxDefinitionFor primitiveName primitive (zetaDelta := true)
      (compile := false)
    modifyEnv (addNoncomputable · primitiveName)
    let mut binders := state.view.binders
    if let some auxiliary := prepared.auxiliary? then
      let some name := allocation.findName? 0
        | throwError "internal error: missing conic auxiliary allocation"
      let name ← withFreshMacroScope do MonadQuotation.addMacroScope name
      binders := binders.push {
        name
        typeSyntax := ← presentationTypeSyntax auxiliary
      }
    let mut rows := #[]
    for i in [:prepared.rowPredicates.size] do
      let some name := allocation.findName? (i + 1)
        | throwError "internal error: missing conic row allocation"
      rows := rows.push { name, proposition := (← `(True)).raw : PTran.Syntax.ConstraintView }
    let template := {
      state.view with
      binders
      constraints := state.view.constraints.extract 0 index ++ rows ++
        state.view.constraints.extract (index + 1) state.view.constraints.size
    }
    let targetProblem ← simpOnly replacement.targetProblem
    let rendered ← problemViewFromExpression targetProblem template
    let view := { template with constraints := template.constraints.mapIdx fun i row =>
      if index ≤ i && i < index + rows.size then rendered.constraints[i]! else row }
    let semantic ← exactExpressionSyntax targetProblem
    let primitiveCertificate ← exactExpressionSyntax primitive
    return {
      view
      semantic
      semanticDomainType := ← exactExpressionSyntax prepared.nextDomain
      primitiveCertificate
      simplifyExpLogTerms := state.simplifyExpLogTerms
      hasSubstitution := state.hasSubstitution
      removedConstraintNames := {}
      normalizationLemmas := state.normalizationLemmas
      checkpoint? := some { semantic, view }
      constraintSplice? := some { index, count := rows.size }
    }

/-- Select and certify a whole-constraint rewrite, deferring named
materialization until the runner has allocated its generated family. -/
def prepareConic (state : ReformState) (step : Syntax)
    (selector : TSyntax `ident) (rule? : Option (TSyntax `term)) :
    CommandElabM SurfaceStepDraft := withRef step do
  let some index := state.view.constraints.findIdx? fun constraint =>
      sameUserName constraint.name selector.getId
    | throwErrorAt selector "unknown or stale constraint label `{selector.getId.eraseMacroScopes}`"
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let rule? ← rule?.mapM fun ruleSyntax => do
      try
        let rule ← elabTerm ruleSyntax none
        synthesizeSyntheticMVarsNoPostponing
        let rule ← instantiateMVars rule
        if rule.hasMVar then throwError "exact rule contains unresolved metavariables"
        return rule
      catch
        | .error _ message =>
          throwErrorAt ruleSyntax
            "constraint `{selector.getId.eraseMacroScopes}`: failed to elaborate exact rule: {message}"
        | exception => throw exception
    let predicate := presentation.constraints[index]!.predicate
    let result : Except PTran.Elab.Affine.AffineError Prepared ←
      if rule?.isNone && (← PTran.Elab.Conic.SecondOrder.isCandidate predicate) then do
        let retained := presentation.constraints.extract 0 index ++
          presentation.constraints.extract (index + 1) presentation.constraints.size
        PTran.Elab.Conic.SecondOrder.planReplacement predicate (retained.map (·.predicate))
      else do
        let result ← PTran.Elab.Conic.Polyhedral.plan predicate rule?
        pure (result.map Sum.inl)
    match result with
    | .error error =>
      throwErrorAt selector "constraint `{selector.getId.eraseMacroScopes}`: {error.reason}"
    | .ok result => pure (result, sectionFVars)
  let stem ← generatedStem selector
  let mut nameRequests := #[]
  if prepared.auxiliary?.isSome then
    nameRequests := nameRequests.push {
      id := 0
      kind := .generatedBinderFamily
      requested := Name.mkSimple (stem ++ "_aux")
      ref := selector.raw
    }
  for i in [:prepared.rowPredicates.size] do
    nameRequests := nameRequests.push {
      id := i + 1
      kind := .generatedRowFamily
      requested := Name.mkSimple s!"{stem}_conic_{i + 1}"
      ref := selector.raw
    }
  return {
    nameRequests
    materialize := materializeConic state index prepared preparedVars
  }

end PTran.Reformulation.Internal
