import PTran.Elab.Conic.Automatic
import PTranTest.Affine.Support
import Lean.Meta.Tactic.AuxLemma

/-!
# Certified exact-rule selection

Direct selection deliberately tests affine constant overlaps before the
terminal caller's affine-first shortcut. Other cases distinguish failed
candidate heads from certified rules and retain the targeted dispatch policy.
-/

namespace PTranTest.Conic.Automatic

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open PTran.Elab.Conic PTranTest.Affine

private def checkPrepared (source : Expr) (result : Plan.Prepared) : MetaM Nat := do
  let (predicates, rows) ← match result with
    | .inl exact => do
      discard <| Plan.checkLift source exact.lift
      checkWithKernel exact.targetIff
      pure (exact.rowPredicates, exact.certifiedRows)
    | .inr contextual => do
      checkWithKernel contextual.conditionalIff
      pure (contextual.rowPredicates, contextual.certifiedRows)
  unless predicates.size == rows.size do throwError "missing certified replacement rows"
  for row in rows do
    for expression in #[row.constraint, row.pointwiseIff] do
      if expression.hasMVar || expression.hasSorry then
        throwError "incomplete automatic certificate"
      checkWithKernel expression
  return rows.size

private def expectUnique (stx : TSyntax `term) (count : Nat)
    (retained : Array Expr := #[]) : TermElabM Unit := do
  let source ← elaborate stx
  let before ← getMCtx
  let result ← Automatic.planUnique source retained
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "automatic selection leaked scratch metavariables"
  let .ok result := result
    | match result with
      | .error error => throwError "expected a unique exact rule: {error.reason}"
      | .ok _ => throwError "unreachable selection result"
  unless (← checkPrepared source result) == count do
    throwError "unexpected automatic row count"

private def expectAmbiguous (stx : TSyntax `term) (names : Array String) :
    TermElabM Unit := do
  let source ← elaborate stx
  -- These overlaps are valid affine rows and should be bypassed by terminal
  -- conversion. They still exercise actual distinct native exact rules here.
  let .ok _ ← normalizeRow source | throwError "ambiguity fixture is not already affine"
  let before ← getMCtx
  let environment ← getEnv
  let .error error ← Automatic.planUnique source
    | throwError "multiple exact rules were accepted as a unique match"
  let message ← error.reason.toString
  unless message.contains "ambiguous exact conic rules" do
    throwError "expected ambiguity, got {message}"
  for name in names do
    unless message.contains name do throwError "ambiguity omitted rule {name}: {message}"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "ambiguous selection leaked scratch metavariables"
  for (name, _) in (← getEnv).constants.toList do
    unless environment.contains name do
      throwError "ambiguous selection leaked auxiliary declaration {name}"
  let .ok result ← Automatic.planFirst source
    | throwError "targeted first-success policy rejected a certified overlap"
  discard <| checkPrepared source result

run_cmd liftTermElabM do
  expectAmbiguous (← `(fun _ : ℝ => Real.exp 0 ≤ Real.log 2))
    #["exponential upper bound", "logarithmic lower bound"]
  expectAmbiguous (← `(fun _ : ℝ => max (0 : ℝ) 1 ≤ min 2 3))
    #["maximum upper bound", "minimum lower bound"]
  expectUnique (← `(fun p : ℝ × ℝ => |(2 : ℝ)| ≤ min p.1 p.2)) 2
  let fallback ← elaborate (← `(fun p : ℝ × ℝ => |(2 : ℝ)| ≤ min p.1 p.2))
  let .error _ ← Automatic.planFirst fallback
    | throwError "targeted polyhedral branch selection changed"
  expectUnique (← `(fun x : ℝ => x ^ 2 ≤ Real.log 2)) 1
  expectUnique (← `(fun x : ℝ => |x| ≤ Real.exp 2)) 2
  expectUnique (← `(fun x : ℝ => Real.exp x ≤ 3)) 1
  -- The default exponential attempt can itself fall back to le_log. It must
  -- not count as an additional rule alongside the explicit logarithm attempt.
  expectUnique (← `(fun t : ℝ => t ≤ Real.log 2)) 1
  let margin ← elaborate (← `(fun x : ℝ => 1 ≤ x))
  expectUnique (← `(fun x : ℝ => Real.exp 0 ≤ Real.log x)) 1 #[margin]
  expectUnique (← `(fun p : ℝ × ℝ => PTran.Fn.softplus p.1 ≤ p.2)) 2
  expectUnique (← `(fun p : ℝ × ℝ => Real.log (1 + Real.exp p.1) ≤ p.2)) 2
  expectUnique (← `(fun t : ℝ => PTran.Fn.relativeEntropy 0 2 ≤ t)) 1

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : ℝ × ℝ => p.2 ≤ Real.log p.1))
  let .error error ← Automatic.planUnique source
    | throwError "logarithm without a retained margin was accepted"
  unless (← error.reason.toString).contains "positive constant margin" do
    throwError "automatic selection lost its domain diagnostic: {error.reason}"
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => Real.exp x ≤ c))
  let hole ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  let .error _ ← Automatic.planUnique (mkApp builder hole)
    | throwError "automatic selection accepted unresolved input"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "failed selection leaked scratch metavariables"
  if ← hole.mvarId!.isAssigned then throwError "automatic selection assigned a caller hole"

/-- Evidence-generated auxiliary declarations survive only an accepted plan. -/
private def checkEvidenceLifetime (stx : TSyntax `term) (success : Bool) :
    TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression 2 fun parameters source => do
    let generated ← IO.mkRef (#[] : Array Name)
    let config : PTran.Elab.Affine.Config := {
      nonzeroEvidence? := some fun obligation => do
        let proof ← mkAppM ``And.left #[parameters[1]!]
        unless ← isDefEq (← inferType proof) obligation do return none
        let proof ← mkLambdaFVars parameters proof
        let name ← mkAuxLemma [] (← inferType proof) proof (cache := false)
        generated.modify (·.push name)
        return some (mkAppN (mkConst name) parameters)
    }
    let result ← Automatic.planUnique source #[] config
    match result with
    | .ok result =>
      unless success do throwError "nonlinear replacement was accepted"
      discard <| checkPrepared source result
    | .error error =>
      if success then throwError "evidence-backed replacement failed: {error.reason}"
    let names ← generated.get
    if names.isEmpty then throwError "test did not exercise evidence-generated declarations"
    for name in names do
      unless (← getEnv).contains name == success do
        throwError "automatic selection mishandled auxiliary declaration {name}"

run_cmd liftTermElabM do
  checkEvidenceLifetime (← `(fun (c : ℝ) (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => |x / c| ≤ 1)) true
  checkEvidenceLifetime (← `(fun (c : ℝ) (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => max (x / c) (x * x) ≤ 1)) false

end PTranTest.Conic.Automatic
