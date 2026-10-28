/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Terminal
import MorewTest.NLP.DomainSupport
import MorewTest.Environment

/-!
# Complete NLP planning and retained evidence

These tests inspect exact equivalence endpoints, source-row provenance, cached
proof scopes, domain retries, finite auxiliaries, and failure isolation without
depending on the command renderer.
-/

namespace MorewTest.NLP.Terminal

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew.Elab.Reformulation
open Morew.Elab.NLP
open scoped ENNReal

private def presentation (objective : TSyntax `term)
    (rows : Array (Name × TSyntax `term)) : TermElabM PresentationState := do
  let objective ← Domain.elaborate objective
  let .forallE _ domain value _ ← whnf (← inferType objective)
    | throwError "expected a function objective"
  let constraints ← rows.mapM fun (name, row) => do
    return { name, predicate := ← Domain.elaborate row : ConstraintEntry }
  return {
    sense := .minimize, domainType := domain, valueType := value
    objective, constraints, binders := #[{ name := `point, type := domain }] }

private def checked (source : PresentationState) : MetaM Morew.Elab.NLP.Terminal.Result := do
  let before ← getMCtx
  let result ← match ← Morew.Elab.NLP.Terminal.plan source with
    | .ok result => pure result
    | .error error => throwError "expected terminal NLP certification: {error.reason}"
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "terminal planning leaked scratch metavariables"
  let target ← result.presentation.canonicalProblem
  let expected ← mkAppM ``Morew.GlobalEquivalence #[← source.canonicalProblem, target]
  unless ← isDefEq (← inferType result.equivalence) expected do
    throwError "terminal equivalence has wrong endpoints"
  let formType ← whnf (← inferType result.form)
  unless formType.isAppOfArity ``Morew.NLP.Form 5 &&
      (← isDefEq formType.getAppArgs.back! target) do
    throwError "terminal form represents a different problem"
  for proof in #[result.form, result.equivalence] do
    if proof.hasMVar || proof.hasSorry then throwError "terminal certificate is incomplete"
    checkWithKernel proof
  return result

private def count (result : Morew.Elab.NLP.Terminal.Result) (expected : Nat) : MetaM Unit := do
  let data ← mkProjection result.form `data
  unless ← isDefEq (← mkProjection data `rowCount) (mkNatLit expected) do
    throwError "terminal form has the wrong scalar row count"

run_cmd liftTermElabM do
  let source ← presentation (← `(fun x : ℝ => Real.log x + x ^ 4)) #[
    (`group, ← `(fun x : ℝ => |Real.log x| ≤ 3 ∧ 1 ≤ x)),
    (`keep, ← `(fun x : ℝ => True ∧ x ≤ 10))]
  let result ← checked source
  unless result.rowOrigins == #[0, 0, 0, 1] && result.replacedIndices == #[0] do
    throwError "nonlinear group did not split in source order"
  unless result.presentation.constraints.back!.name == `keep do
    throwError "smooth group was renamed"
  count result 4
  let source ← presentation (← `(fun x : ℝ => x ^ 2)) #[
    (`single, ← `(fun x : ℝ => True ∧ |x| ≤ 3 ∧ True))]
  let result ← checked source
  unless result.rowOrigins == #[0, 0] && result.replacedIndices == #[0] do
    throwError "single nonlinear leaf surrounded by True was not lowered"
  count result 2

-- A later exact rule exposes the positivity needed by an earlier bound and
-- the objective. Domain conditions are derived, never appended as new guards.
run_cmd liftTermElabM do
  let source ← presentation (← `(fun x : ℝ => Real.log x)) #[
    (`first, ← `(fun x : ℝ => |Real.log x| ≤ 3)),
    (`margin, ← `(fun x : ℝ => 1 ≤ min x 2))]
  let result ← checked source
  unless result.rowOrigins == #[0, 0, 1, 1] && result.replacedIndices == #[0, 1] do
    throwError "terminal retry lost original row ordering"
  count result 4
  let source ← presentation (← `(fun x : ℝ => Real.log x)) #[
    (`smoothGroup, ← `(fun x : ℝ => Real.log x ≤ 3 ∧ x ≤ 100)),
    (`margin, ← `(fun x : ℝ => 1 ≤ min x 2))]
  let result ← checked source
  unless result.replacedIndices == #[1] &&
      result.presentation.constraints[0]!.name == `smoothGroup do
    throwError "deferred smooth group was split unnecessarily"
  count result 4

-- An unproductive domain search can reach its local cap before a later exact
-- rule exposes the margin. It must fail cleanly so terminal planning can retry.
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let source ← presentation
    (← `(fun p : (ℝ × ℝ) × (Fin 1 → ℝ) => Real.log p.1.1)) #[
      (`first, ← `(fun p : (ℝ × ℝ) × (Fin 1 → ℝ) => |Real.log p.1.1| ≤ p.1.2)),
      (`margin, ← `(fun p : (ℝ × ℝ) × (Fin 1 → ℝ) => 1 ≤ min p.1.1 2)),
      (`norm1, ← `(fun p : (ℝ × ℝ) × (Fin 1 → ℝ) => ‖WithLp.toLp 1 p.2‖ ≤ p.1.2)),
      (`norm2, ← `(fun p : (ℝ × ℝ) × (Fin 1 → ℝ) =>
        ‖WithLp.toLp 1 (fun i => 2 * p.2 i)‖ ≤ p.1.2))]
  let feasible ← mkAppM ``Morew.Problem.feasible #[← source.canonicalProblem]
  let environment ← getEnv
  let context ← getMCtx
  let .error _ ← Rows.certifyRows feasible #[source.constraints[0]!.predicate]
    | throwError "unexpected evidence before lowering the margin"
  unless context.mvarCounter == (← getMCtx).mvarCounter &&
      context.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "exhausted domain search leaked metavariables"
  if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
    throwError "exhausted domain search leaked {name}"
  let result ← checked source
  unless result.rowOrigins == #[0, 0, 1, 1, 2, 2, 2, 3, 3, 3] &&
      result.auxiliaries.map (·.1) == #[2, 3] do
    throwError "retry after exhausted domain search changed row or auxiliary origins"
  count result 10

-- The private evidence cap is recoverable, but a tighter caller budget and
-- recursion limits still terminate the attempt without leaking scratch state.
run_cmd liftTermElabM do
  withLocalDeclD `point (mkConst ``Real) fun point => do
    let required ← mkAppM ``LT.lt #[← Domain.elaborate (← `((0 : ℝ))), point]
    for recursion in [false, true] do
      let context ← getMCtx
      let environment ← getEnv
      let initial ← IO.getNumHeartbeats
      let propagated ← tryCatchRuntimeEx
        (withTheReader Core.Context (fun context =>
          if recursion then { context with maxRecDepth := 1 }
          else { context with initHeartbeats := initial, maxHeartbeats := 1 }) do
          discard <| Domain.Evidence.prove? point required
          pure false)
        fun exception =>
          if (if recursion then exception.isMaxRecDepth else exception.isMaxHeartbeat) then
            pure true
          else throw exception
      unless propagated do throwError "domain evidence swallowed a caller resource limit"
      unless context.mvarCounter == (← getMCtx).mvarCounter &&
          context.lmvarCounter == (← getMCtx).lmvarCounter do
        throwError "caller resource exhaustion leaked metavariables"
      if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
        throwError "caller resource exhaustion leaked {name}"

-- A constant nonsmooth head is a smooth constant. Its two syntactically
-- applicable rewrite rules must not force an unnecessary ambiguity failure.
run_cmd liftTermElabM do
  let source ← presentation (← `(fun x : ℝ => x ^ 2)) #[
    (`constant, ← `(fun _ : ℝ => max (0 : ℝ) 1 ≤ min 2 3))]
  let result ← checked source
  unless result.replacedIndices.isEmpty do throwError "smooth constant was rewritten"
  count result 1

-- Independent nonzero evidence is scoped inside the accepted original row.
-- Both later L1 auxiliaries must retain the accepted residual and proof data.
run_cmd liftTermElabM do
  let expressions ← Domain.elaborate (← `(fun (c : ℝ) (h : c ≠ 0 ∧ True) =>
    ((fun v : Fin 1 → ℝ => let nonzero : c ≠ 0 := h.1; v 0 / c ≤ 10),
     (fun v : Fin 1 → ℝ => ‖WithLp.toLp 1 v‖ ≤ 2),
     (fun v : Fin 1 → ℝ => ‖WithLp.toLp 1 (fun i => 2 * v i)‖ ≤ 3))))
  lambdaBoundedTelescope expressions 2 fun parameters expressions => do
    let bound ← mkAppM ``Prod.fst #[expressions]
    let norms ← mkAppM ``Prod.snd #[expressions]
    let first ← mkAppM ``Prod.fst #[norms]
    let second ← mkAppM ``Prod.snd #[norms]
    let base ← presentation (← `(fun v : Fin 1 → ℝ => v 0 ^ 2)) #[]
    let source := { base with constraints := #[
      { name := `bound, predicate := bound },
      { name := `first, predicate := first },
      { name := `second, predicate := second }] }
    let result ← checked source
    unless result.auxiliaries.map (·.1) == #[1, 2] &&
        result.presentation.constraints[0]!.name == `bound do
      throwError "auxiliary insertion changed retained source rows"
    count result 7
    let closed ← mkLambdaFVars parameters result.form
    if closed.hasFVar || closed.hasMVar then throwError "source proof scope escaped the form"
    checkWithKernel closed

private def reject (source : PresentationState) (fragment : String) : MetaM Unit := do
  let environment ← getEnv
  let context ← getMCtx
  let .error error ← Morew.Elab.NLP.Terminal.plan source
    | throwError "unsupported terminal NLP was accepted"
  unless (← error.reason.toString).contains fragment do
    throwError "unexpected terminal diagnostic: {error.reason}"
  unless context.mvarCounter == (← getMCtx).mvarCounter &&
      context.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "failed terminal planning leaked metavariables"
  if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
    throwError "failed planning leaked {name}"

private def wrapped (x : ℝ) : Prop := x ≤ 3
private def helper (x : ℝ) : ℝ := x ^ 2

run_cmd liftTermElabM do
  for row in #[← `(fun x : ℝ => wrapped x),
      ← `(fun x : ℝ => helper x ≤ 3),
      ← `(fun x : ℝ => |max x 0| ≤ 3),
      ← `(fun x : ℝ => ∀ t : ℝ, x ≤ t),
      ← `(fun x : ℝ => ∀ _i : Fin 0, x < 1)] do
    reject (← presentation (← `(fun x : ℝ => x ^ 2)) #[(`bad, row)]) "bad"
  reject (← presentation (← `(fun x : ℝ => |x|)) #[]) "epigraph"
  reject (← presentation (← `(fun _ : ℝ => Real.log (-1))) #[]) "domain"
  reject (← presentation (← `(fun p : ℝ × (Fin 1 → ℝ) => p.1)) #[
    (`firstBad, ← `(fun p : ℝ × (Fin 1 → ℝ) => Real.log p.1 ≤ 2)),
    (`canLower, ← `(fun p : ℝ × (Fin 1 → ℝ) => ‖WithLp.toLp 1 p.2‖ ≤ 3)),
    (`laterBad, ← `(fun p : ℝ × (Fin 1 → ℝ) => p.1 < 0))]) "firstBad"

run_cmd liftTermElabM do
  let dimension ← mkFreshExprMVar (mkConst ``Nat)
  let domain ← mkArrow (← mkAppM ``Fin #[dimension]) (mkConst ``Real)
  let zero ← Domain.elaborate (← `((0 : ℝ)))
  let objective ← withLocalDeclD `point domain fun point => mkLambdaFVars #[point] zero
  let source : PresentationState := {
    sense := .minimize, domainType := domain, valueType := mkConst ``Real
    objective, binders := #[{ name := `point, type := domain }] }
  reject source "fully elaborated"
  if ← dimension.mvarId!.isAssigned then throwError "terminal validation chose a caller dimension"

end MorewTest.NLP.Terminal
