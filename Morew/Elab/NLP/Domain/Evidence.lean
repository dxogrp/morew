/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Affine
import Morew.Elab.NLP.Space
import Morew.NLP.Domain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Meta.Check

/-!
# Evidence admitted for open nonlinear evaluation domains

Source feasibility consists only of native closed real comparisons, conjunctions,
and `True`. Domain proof search sees those rows, already established child-domain
facts, and decision-independent parameter hypotheses. Other local hypotheses are
hidden from tactics, including positivity's local-context search.
-/

namespace Morew.Elab.NLP.Domain.Evidence

open Lean Lean.Meta Qq

/-- A rejected source feasibility leaf, numbered from zero in traversal order. -/
structure AdmissionError where
  /-- The position of the unsupported leaf in the source conjunction. -/
  rowIndex : Nat
  /-- The unsupported, structurally reduced proposition. -/
  expression : Expr
  /-- Its type, captured before temporary decision binders leave scope. -/
  type : Expr
  /-- Explanation carrying the leaf's local pretty-printing context. -/
  reason : MessageData

private partial def hasPlaceholders (expression : Expr) : StateT FVarIdSet MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasSorry then return true
  for id in (collectFVars {} expression).fvarIds do
    unless (← get).contains id do
      modify (·.insert id)
      if let some declaration := (← getLCtx).find? id then
        if ← hasPlaceholders declaration.type then return true
        if let some value := declaration.value? (allowNondep := true) then
          if ← hasPlaceholders value then return true
  return false

private def complete (expression : Expr) : MetaM Bool := do
  return !(← Affine.hasUnresolved expression) &&
    !(← (hasPlaceholders expression).run' {})

private def admissionFailure (index : Nat) (expression : Expr) (reason : MessageData) :
    MetaM AdmissionError := do
  return {
    rowIndex := index
    expression := expression
    type := ← inferType expression
    reason := ← addMessageContext
      m!"unsupported feasibility row {index}: {expression}; {reason}" }

private partial def admitBody (point expression : Expr) (index : Nat) :
    MetaM (Except AdmissionError Nat) := do
  let expression ← Affine.reduceStructure expression
    (opaqueProblemDependencies? := some point)
  if expression.isAppOfArity ``And 2 then
    let args := expression.getAppArgs
    match ← admitBody point args[0]! index with
    | .error error => return .error error
    | .ok next => return ← admitBody point args[1]! next
  if expression.isConstOf ``True then return .ok (index + 1)
  let args := expression.getAppArgs
  if expression.isAppOfArity ``Eq 3 then
    if ← isDefEq args[0]! q(ℝ) then return .ok (index + 1)
  if expression.isAppOfArity ``LE.le 4 || expression.isAppOfArity ``GE.ge 4 then
    if ← isDefEq args[0]! q(ℝ) then
      let left : Q(ℝ) := args[2]!
      let right : Q(ℝ) := args[3]!
      let expected : Expr := if expression.isAppOf ``GE.ge then q($left ≥ $right)
        else q($left ≤ $right)
      if ← isDefEq args[1]! expected.getAppArgs[1]! then
        return .ok (index + 1)
  return .error (← admissionFailure index expression
    "expected canonical closed real ≤, ≥, or = comparisons joined by And, or True")

/-- Validate the entire feasibility predicate, even when no expression sources are supplied.

Named predicates stay opaque. Strict inequalities, disequalities, quantifiers,
and altered order instances cannot serve as source rows.
-/
def admit (feasible : Expr) : MetaM (Except AdmissionError Unit) :=
  Affine.withIsolatedMVars do
    try
      unless ← complete feasible do
        return .error (← admissionFailure 0 feasible
          "unresolved metavariables or placeholders are not supported")
      let type ← whnf (← inferType feasible)
      let .forallE _ decision result _ := type
        | return .error (← admissionFailure 0 feasible "expected a predicate X → Prop")
      withLocalDeclD `point decision fun point => do
        unless ← isDefEq (result.instantiate1 point) q(Prop) do
          return .error (← admissionFailure 0 feasible "expected a predicate X → Prop")
        match ← admitBody point (mkApp feasible point) 0 with
        | .ok _ => return .ok ()
        | .error error => return .error error
    catch exception =>
      return .error (← admissionFailure 0 feasible exception.toMessageData)

/-- Project all conjunction leaves from an admitted source-feasibility proof.
Local structural lets are reduced without unfolding named predicates.
-/
partial def rowFacts (point feasibleProof : Expr) : MetaM (Array Expr) := do
  let type ← Affine.reduceStructure (← inferType feasibleProof)
    (opaqueProblemDependencies? := some point)
  if type.isAppOfArity ``And 2 then
    let left ← rowFacts point (← mkAppM ``And.left #[feasibleProof])
    let right ← rowFacts point (← mkAppM ``And.right #[feasibleProof])
    return left ++ right
  if type.isConstOf ``True then return #[]
  -- Preserve the admitted structural view for tactics that do not unfold
  -- named model containers when inspecting a proof's type.
  return #[← mkAppOptM ``id #[some type, some feasibleProof]]

-- Domain membership unfolds to conjunctions. Unlike row admission, these are
-- already proved facts supplied by the caller, so inspecting their definition
-- cannot add a premise to feasibility.
private partial def splitFacts (proof : Expr) : MetaM (Array Expr) := do
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``And 2 then
    return (← splitFacts (← mkAppM ``And.left #[proof])) ++
      (← splitFacts (← mkAppM ``And.right #[proof]))
  if type.isConstOf ``True then return #[]
  return #[proof]

private def attempt? (action : MetaM Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let proof ← instantiateMVars (← action)
    unless ← complete proof do throwError "incomplete domain evidence"
    return some proof
  catch _ =>
    saved.restore
    setEnv saved.core.env
    return none

private def simpContext (facts : Array Expr := #[]) : MetaM Simp.Context := do
  let mut theorems : SimpTheorems := {}
  for name in [``Real.exp_pos, ``Real.exp_ne_zero, ``Real.log_exp, ``Real.log_one,
      ``Finset.notMem_empty, ``Set.mem_setOf_eq, ``Set.mem_univ,
      ``zero_add, ``add_zero, ``zero_mul, ``mul_zero,
      ``one_mul, ``mul_one, ``neg_zero, ``and_true, ``true_and] do
    theorems ← theorems.addConst name
  let mut sets : SimpTheoremsArray := #[theorems]
  for fact in facts do
    sets ← sets.addTheorem (.other (← mkFreshUserName `domainFact)) fact
  Simp.mkContext (config := { contextual := false }) (simpTheorems := sets)

private def simplifiedFact (context : Simp.Context) (fact : Expr) : MetaM Expr := do
  let (result, _) ← simp (← inferType fact) context
  match result.proof? with
  | some equality => mkEqMP equality fact
  | none => mkAppOptM ``id #[some result.expr, some fact]

-- Specialize independent parameter families only at existing independent
-- locals, and discharge their premises only with already approved facts.
-- Source rows themselves never introduce universal hypotheses.
private def specialize (candidates pool : Array Expr) (proof : Expr) :
    Nat → MetaM (Array Expr)
  | 0 => pure #[]
  | fuel + 1 => do
    let type ← whnf (← inferType proof)
    let .forallE _ argument _ _ := type | return #[]
    let choices := if ← isProp argument then pool else candidates
    let mut result := #[]
    for choice in choices do
      if result.size ≥ 32 then break
      if ← isDefEq (← inferType choice) argument then
        let application := mkApp proof choice
        let leaves ← splitFacts application
        result := result ++ leaves
        for leaf in leaves do
          result := result ++ (← specialize candidates pool leaf fuel)
    return result

private def arithmetic (target : Expr) (facts : Array Expr) : MetaM Expr := do
  let goal ← mkFreshExprMVar target
  let linarithConfig : Mathlib.Tactic.Linarith.LinarithConfig := {}
  Mathlib.Tactic.Linarith.linarith true facts.toList
    { linarithConfig with
      preprocessors := linarithConfig.preprocessors.concat
        Mathlib.Tactic.Linarith.nlinarithExtras } goal.mvarId!
  instantiateMVars goal

private def search (target : Expr) (facts : Array Expr) : MetaM Expr := do
  for fact in facts do
    if ← isDefEq (← inferType fact) target then return fact
    if (← whnf (← inferType fact)).isConstOf ``False then
      return ← mkFalseElim target fact
  if let some proof ← attempt? do
      let ⟨true, proof⟩ ← Mathlib.Meta.NormNum.deriveBool target
        | throwError "numerical domain condition is false"
      pure proof then
    return proof
  if let some proof ← attempt? (Mathlib.Meta.Positivity.solve target) then return proof
  if let some proof ← attempt? do
      let goal ← mkFreshExprMVar target
      let (remaining, _) ← simpTarget goal.mvarId! (← simpContext facts)
      if let some remaining := remaining then
        remaining.assign (← arithmetic (← remaining.getType) facts)
      instantiateMVars goal then
    return proof
  if let some proof ← attempt? do
      let goal ← mkFreshExprMVar target
      let [condition] ← goal.mvarId!.apply (← mkConst' ``Real.log_pos)
        | throwError "not positivity of a logarithm"
      condition.assign (← arithmetic (← condition.getType) facts)
      instantiateMVars goal then
    return proof
  arithmetic target facts

private def withFacts (remaining : List Expr) (facts : Array Expr)
    (action : Array Expr → MetaM Expr) : MetaM Expr := do
  match remaining with
  | [] => action facts
  | proof :: rest =>
    mapLetDeclZeta (← mkFreshUserName `domainEvidence) (← inferType proof) proof fun binding =>
      withFacts rest (facts.push binding) action

private def canonicalInstances : List Expr :=
  [q((inferInstance : Field ℝ)), q((inferInstance : LinearOrder ℝ)),
   q((inferInstance : IsStrictOrderedRing ℝ)), q((inferInstance : LE ℝ)),
   q((inferInstance : LT ℝ)), q((inferInstance : HAdd ℝ ℝ ℝ)),
   q((inferInstance : HSub ℝ ℝ ℝ)), q((inferInstance : HMul ℝ ℝ ℝ)),
   q((inferInstance : HDiv ℝ ℝ ℝ)), q((inferInstance : Neg ℝ)),
   q((inferInstance : Inv ℝ)), q((inferInstance : HPow ℝ ℕ ℝ)),
   q((inferInstance : HPow ℝ ℝ ℝ))]

private def proveCore (point target : Expr) (facts : Array Expr) : MetaM Expr := do
  unless ← complete target do throwError "incomplete domain target"
  let mut approved := #[]
  for fact in facts do
    unless ← complete fact do throwError "incomplete supplied domain evidence"
    approved := approved ++ (← splitFacts fact)
  let original ← getLCtx
  let mut context := original
  let mut candidates := #[]
  for declaration in original do
    if ← isProp declaration.type then
      context := context.setKind declaration.fvarId .implDetail
      if !declaration.isImplementationDetail &&
          !(← Affine.depends point declaration.toExpr) && (← complete declaration.toExpr) then
        approved := approved ++ (← splitFacts declaration.toExpr)
    else if !declaration.isImplementationDetail &&
        !(← Affine.depends point declaration.toExpr) && (← complete declaration.toExpr) then
      candidates := candidates.push declaration.toExpr
  let parameterPool := approved
  for candidate in candidates do
    let type ← whnf (← inferType candidate)
    if type.isAppOfArity ``Fin 1 then
      if ← isDefEq type.getAppArgs[0]! q((0 : ℕ)) then
        return ← mkAppOptM ``Fin.elim0 #[some target, some candidate]
  for fact in parameterPool do
    approved := approved ++ (← specialize candidates parameterPool fact 4)
  -- Clear ambient instance registrations as well as hiding unapproved proofs.
  -- Original declarations remain available for the types of approved facts.
  withLCtx context #[] do
    withFacts canonicalInstances #[] fun _ => do
      Space.withCanonicalSpaces #[← inferType point] do
        let simple ← simpContext
        let simplified ← approved.mapM (simplifiedFact simple)
        -- A known positivity fact may simplify to True but still supply the
        -- strict margin needed to combine another row with arithmetic.
        withFacts (approved ++ simplified).toList #[] fun facts => search target facts

/-- Try bounded, kernel-checked domain evidence from approved source-row and child facts.

Independent parameter hypotheses and finite-index membership hypotheses are
available. Unapproved decision-dependent hypotheses are never searched. The
2,000,000 internal-heartbeat cap preserves any tighter caller limit, and failure
restores state. No unresolved metavariables or placeholders can escape.
-/
def prove? (point target : Expr) (facts : Array Expr := #[]) : MetaM (Option Expr) := do
  let result : Except Unit Expr ← Affine.withIsolatedMVars do
    try
      let context ← readThe Core.Context
      let localLimit := (← IO.getNumHeartbeats) - context.initHeartbeats + 2_000_000
      let limit := if context.maxHeartbeats == 0 then localLimit
        else min context.maxHeartbeats localLimit
      return ← withTheReader Core.Context
          (fun context => { context with maxHeartbeats := limit }) do
        let proof ← instantiateMVars (← proveCore point target facts)
        unless (← complete proof) && (← isDefEq (← inferType proof) target) do
          return .error ()
        checkWithKernel proof
        return .ok proof
    catch _ => return .error ()
  return result.toOption

end Morew.Elab.NLP.Domain.Evidence
