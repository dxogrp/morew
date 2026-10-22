import PTran.Elab.Conic.Terminal
import PTranTest.Affine.Support

/-!
# Whole-problem conic planner tests

Check provenance, exact group splitting, retained margins, auxiliary pullbacks,
and whole-plan rollback through the typed API alone.
-/

namespace PTranTest.Conic.Terminal

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open PTran.Elab.Reformulation
open PTran.Elab.Conic
open PTranTest.Affine

private def makePresentation (objectiveSyntax : TSyntax `term)
    (rows : Array (Name × TSyntax `term))
    (sense : PTran.ObjectiveSense := .minimize) : TermElabM PresentationState := do
  let objective ← elaborate objectiveSyntax
  let .forallE _ domain value _ ← whnf (← inferType objective)
    | throwError "test objective is not a function"
  let constraints ← rows.mapM fun (name, rowSyntax) => do
    return { name, predicate := ← elaborate rowSyntax : ConstraintEntry }
  return {
    sense
    domainType := domain
    valueType := value
    binders := #[{ name := `point, type := domain }]
    objective
    constraints
  }

private def checkPlan (source : PresentationState) : MetaM Terminal.Result := do
  let result ← match ← Terminal.plan source with
    | .ok result => pure result
    | .error error => throwError "expected successful terminal conic plan: {error.reason}"
  let before ← source.canonicalProblem
  let after ← result.presentation.canonicalProblem
  let expected ← mkAppM ``PTran.GlobalEquivalence #[before, after]
  unless ← isDefEq (← inferType result.equivalence) expected do
    throwError "terminal equivalence has the wrong endpoints"
  let formType ← whnf (← inferType result.form)
  unless formType.getAppFn.isConstOf ``PTran.Conic.Form do
    throwError "terminal form has the wrong type"
  unless ← isDefEq formType.getAppArgs.back! after do
    throwError "terminal form does not represent the final canonical problem"
  for expression in #[result.equivalence, result.form] do
    if expression.hasMVar || expression.hasSorry then
      throwError "terminal planning returned incomplete proof evidence"
    checkWithKernel expression
  unless result.rowOrigins.size == result.presentation.constraints.size do
    throwError "terminal row provenance does not match the presentation"
  unless result.presentation.binders.size == source.binders.size + result.auxiliaries.size do
    throwError "terminal auxiliary inventory does not match the presentation"
  for index in [:source.binders.size] do
    unless result.presentation.binders[index]!.name == source.binders[index]!.name &&
        result.presentation.binders[index]!.type == source.binders[index]!.type do
      throwError "terminal planning changed an original decision binder"
  return result

/-! All-conic groups retain their original labels and boundaries, including
empty conjunctions; maximization sense is retained independently of the type. -/
run_cmd liftTermElabM do
  let source ← makePresentation (← `(fun x : ℝ => 2 * x + 1)) #[
    (`grouped, ← `(fun x : ℝ => x ≤ 3 ∧ (True ∧ 0 ≤ x))),
    (`empty, ← `(fun _ : ℝ => True))
  ] .maximize
  let result ← checkPlan source
  unless result.replacedIndices.isEmpty && result.auxiliaries.isEmpty do
    throwError "already-conic groups were replaced"
  unless result.presentation.constraints.map (·.name) == #[`grouped, `empty] do
    throwError "already-conic group names changed"
  unless result.rowOrigins == #[0, 1] && result.presentation.sense == .maximize do
    throwError "already-conic planning lost provenance or sense"
  let sense ← mkAppM ``PTran.Conic.Data.sense
    #[← mkAppM ``PTran.Conic.Form.data #[result.form]]
  unless ← isDefEq sense (mkConst ``PTran.ObjectiveSense.maximize) do
    throwError "terminal conic data lost maximization sense"

run_cmd liftTermElabM do
  let source ← makePresentation (← `(fun _ : ℝ => (4 : ℝ))) #[]
  let result ← checkPlan source
  unless result.presentation.constraints.isEmpty && result.rowOrigins.isEmpty do
    throwError "empty feasibility acquired a row"

/-! A nonlinear conjunction splits once, exposing its own affine margin as a
retained sibling. Other conic groups remain intact throughout later rewrites. -/
run_cmd liftTermElabM do
  let source ← makePresentation (← `(fun p : ℝ × ℝ => p.2)) #[
    (`logGroup, ← `(fun p : ℝ × ℝ => p.2 ≤ Real.log p.1 ∧ 1 ≤ p.1)),
    (`absolute, ← `(fun p : ℝ × ℝ => |p.2| ≤ 4)),
    (`square, ← `(fun p : ℝ × ℝ => p.1 ^ 2 ≤ p.2)),
    (`keep, ← `(fun p : ℝ × ℝ => 0 ≤ p.1 ∧ p.2 ≤ 8))
  ]
  let result ← checkPlan source
  unless result.rowOrigins == #[0, 0, 1, 1, 2, 3] do
    throwError "mixed terminal rewriting changed row provenance or order: {result.rowOrigins}"
  unless result.replacedIndices == #[0, 1, 2] do
    throwError "mixed terminal rewriting lost the original replacement inventory"
  unless result.presentation.constraints.back!.name == `keep do
    throwError "mixed terminal rewriting renamed an already-conic group"

/-! An initially unsupported domain obligation can become available after a
later exact polyhedral rewrite; the planner restarts and revisits earlier rows. -/
run_cmd liftTermElabM do
  let source ← makePresentation (← `(fun p : ℝ × ℝ => p.2)) #[
    (`logarithm, ← `(fun p : ℝ × ℝ => p.2 ≤ Real.log p.1)),
    (`margin, ← `(fun p : ℝ × ℝ => min p.1 (2 : ℝ) ≥ 1))
  ]
  let result ← checkPlan source
  unless result.rowOrigins == #[0, 1, 1] && result.replacedIndices == #[0, 1] do
    throwError "deferred domain planning did not preserve source row order"

/-! Each subsequent auxiliary lifts all earlier rows and the objective through
the new product domain, while append provenance remains deterministic. -/
run_cmd liftTermElabM do
  let source ← makePresentation (← `(fun p : ℝ × ℝ => p.2)) #[
    (`first, ← `(fun p : ℝ × ℝ => PTran.Fn.softplus p.1 ≤ p.2)),
    (`second, ← `(fun p : ℝ × ℝ => PTran.Fn.softplus (-p.1) ≤ p.2)),
    (`keep, ← `(fun p : ℝ × ℝ => 0 ≤ p.2))
  ]
  let result ← checkPlan source
  unless result.auxiliaries.map (·.1) == #[0, 1] do
    throwError "terminal auxiliaries were not appended in rewrite order"
  unless result.rowOrigins == #[0, 0, 1, 1, 2] do
    throwError "terminal auxiliary rewrites lost original row provenance"
  unless result.presentation.constraints.back!.name == `keep do
    throwError "terminal auxiliary pullback renamed an untouched row"

/-! Accepted affine certificates survive the original source's independent
proof-let scope. Later auxiliary lifts must pull back these maps and proofs,
including the stored leaves of an untouched conjunction, without recognizing
the now evidence-free predicates again. -/
run_cmd liftTermElabM do
  let expressions ← elaborate (← `(fun (c : ℝ) (h : c ≠ 0 ∧ True) =>
    ((fun p : ℝ × ℝ => let hn : c ≠ 0 := h.1; |p.1 / c| ≤ p.2),
     (fun p : ℝ × ℝ => let hn : c ≠ 0 := h.1; p.1 / c ≤ 10 ∧ -5 ≤ p.1 / c),
     (fun p : ℝ × ℝ => let hn : c ≠ 0 := h.1; PTran.Fn.softplus (p.1 / c) ≤ p.2),
     (fun p : ℝ × ℝ => let hn : c ≠ 0 := h.1; PTran.Fn.softplus (-(p.1 / c)) ≤ p.2))))
  lambdaBoundedTelescope expressions 2 fun parameters predicates => do
    let absolute ← mkAppM ``Prod.fst #[predicates]
    let rest ← mkAppM ``Prod.snd #[predicates]
    let grouped ← mkAppM ``Prod.fst #[rest]
    let losses ← mkAppM ``Prod.snd #[rest]
    let firstLoss ← mkAppM ``Prod.fst #[losses]
    let secondLoss ← mkAppM ``Prod.snd #[losses]
    let .ok (.inl direct) ← Automatic.planUnique absolute
      | throwError "source-local evidence did not certify the exact rule"
    for predicate in direct.rowPredicates do
      let .error _ ← normalizeRow predicate
        | throwError "fixture unexpectedly retained discoverable nonzero evidence"
    let base ← makePresentation (← `(fun p : ℝ × ℝ => p.2)) #[]
    let auxiliaryRows : Array ConstraintEntry := #[
      { name := `firstLoss, predicate := firstLoss },
      { name := `secondLoss, predicate := secondLoss }]
    for auxiliaryCount in [:3] do
      let constraints : Array ConstraintEntry := #[
          { name := `absolute, predicate := absolute },
          { name := `grouped, predicate := grouped }] ++ auxiliaryRows.extract 0 auxiliaryCount
      let source := { base with constraints }
      let result ← checkPlan source
      unless result.auxiliaries.size == auxiliaryCount do
        throwError "retained evidence test did not exercise all auxiliary pullbacks"
      unless result.presentation.constraints[2]!.name == `grouped do
        throwError "retained evidence changed the already-conic group"
      let data ← mkAppM ``PTran.Conic.Form.data #[result.form]
      unless ← isDefEq (← mkAppM ``PTran.Conic.Data.rowCount #[data])
          (mkNatLit (4 + 2 * auxiliaryCount)) do
        throwError "retained certificates lost structural rows"
      let closed ← mkLambdaFVars parameters result.form
      if closed.hasFVar || closed.hasMVar then
        throwError "source-local evidence escaped the completed form"
      checkWithKernel closed

/-! Only the first row exposes finiteness evidence. The constant objective,
nonlinear rows, and an auxiliary pullback all reuse its recovered
canonical domain instances. -/
run_cmd liftTermElabM do
  let expression ← elaborate (← `(fun (ι : Type) (evidence : Finite ι ∧ True) (i : ι) =>
    ((fun _ : ι → ℝ => (0 : ℝ)),
     (fun x : ι → ℝ => let finiteEvidence : Finite ι := evidence.1; x i ≤ 1),
     (fun x : ι → ℝ => |x i| ≤ 2),
     (fun x : ι → ℝ => PTran.Fn.softplus (x i) ≤ 3))))
  lambdaBoundedTelescope expression 3 fun parameters expressions => do
    let objective ← mkAppM ``Prod.fst #[expressions]
    let rows ← mkAppM ``Prod.snd #[expressions]
    let bound ← mkAppM ``Prod.fst #[rows]
    let nonlinear ← mkAppM ``Prod.snd #[rows]
    let absolute ← mkAppM ``Prod.fst #[nonlinear]
    let loss ← mkAppM ``Prod.snd #[nonlinear]
    let .ok _ ← normalizeRow bound
      | throwError "source-local finite evidence did not certify the original row"
    let .forallE _ domain value _ ← whnf (← inferType objective)
      | throwError "finite-domain objective is not a function"
    let auxiliaryRows : Array ConstraintEntry := #[
      { name := `loss, predicate := loss }]
    for auxiliaryCount in [:2] do
      let source : PresentationState := {
        sense := .minimize
        domainType := domain
        valueType := value
        binders := #[{ name := `point, type := domain }]
        objective
        constraints := #[
          { name := `bound, predicate := bound },
          { name := `absolute, predicate := absolute }] ++ auxiliaryRows.extract 0 auxiliaryCount
      }
      let result ← checkPlan source
      unless result.auxiliaries.size == auxiliaryCount do
        throwError "source-local finite evidence did not survive all auxiliary pullbacks"
      let expectedOrigins := #[0, 1, 1] ++ (#[2, 2].extract 0 (2 * auxiliaryCount))
      unless result.rowOrigins == expectedOrigins do
        throwError "finite-domain planning changed source row provenance"
      let data ← mkProjection result.form `data
      unless ← isDefEq (← mkProjection data `rowCount)
          (mkNatLit (3 + 2 * auxiliaryCount)) do
        throwError "finite-domain planning lost certified rows"
      for certificate in #[result.form, result.equivalence] do
        let closed ← mkLambdaFVars parameters certificate
        if closed.hasFVar || closed.hasMVar || closed.hasSorry then
          throwError "source-local finite evidence escaped the completed certificate"
        checkWithKernel closed

/-! Failures identify the original source entry and restore any auxiliary
declarations introduced during earlier successful planning attempts. -/
run_cmd liftTermElabM do
  let source ← makePresentation (← `(fun p : ℝ × ℝ => p.2)) #[
    (`firstBad, ← `(fun p : ℝ × ℝ => p.2 ≤ Real.log p.1)),
    (`canLower, ← `(fun p : ℝ × ℝ => PTran.Fn.softplus p.1 ≤ p.2)),
    (`laterBad, ← `(fun p : ℝ × ℝ => p.1 < p.2))
  ]
  let before ← getEnv
  let .error error ← Terminal.plan source
    | throwError "unsupported terminal problem was accepted"
  let message ← error.reason.toString
  unless message.contains "firstBad" && message.contains "conic at firstBad using rule" do
    throwError "terminal planning did not report the earliest remaining failure: {message}"
  unless (← getEnv).constants.toList.length == before.constants.toList.length do
    throwError "failed terminal planning leaked auxiliary declarations"

run_cmd liftTermElabM do
  let source ← makePresentation (← `(fun x : ℝ => x ^ 2)) #[
    (`unsupported, ← `(fun x : ℝ => x < 0))
  ]
  let .error error ← Terminal.plan source
    | throwError "nonaffine terminal objective was accepted"
  let message ← error.reason.toString
  unless message.contains "objective" && message.contains "epigraph" do
    throwError "terminal objective failure was not actionable: {message}"
  let maximum := { source with sense := .maximize }
  let .error error ← Terminal.plan maximum
    | throwError "nonaffine maximization objective was accepted"
  let message ← error.reason.toString
  unless message.contains "hypograph t" && !message.contains "epigraph t" do
    throwError "terminal maximization diagnostic used the wrong objective bound: {message}"

run_cmd liftTermElabM do
  let dimension ← mkFreshExprMVar (mkConst ``Nat)
  let index ← mkAppM ``Fin #[dimension]
  let domain ← mkArrow index (mkConst ``Real)
  let zero ← elaborate (← `((0 : ℝ)))
  let objective ← withLocalDeclD `point domain fun point =>
    mkLambdaFVars #[point] zero
  let source : PresentationState := {
    sense := .minimize
    domainType := domain
    valueType := mkConst ``Real
    binders := #[{ name := `point, type := domain }]
    objective
  }
  let .error _ ← Terminal.plan source
    | throwError "terminal planning specialized an unresolved decision dimension"
  if ← dimension.mvarId!.isAssigned then
    throwError "terminal planning assigned a caller metavariable"

end PTranTest.Conic.Terminal
