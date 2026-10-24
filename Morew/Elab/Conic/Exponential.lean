/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Exponential
import Morew.Elab.Atom
import Morew.Elab.Conic.Domain

/-!
# Checked exponential-cone replacements

Whole native exponential and logarithmic bounds and the supported finite
composite formulas are matched without expanding arbitrary user helpers.
Domain evidence comes from independent constants or unchanged lower-margin
rows. Finite exponential families are certified as single quantified rows.
-/

namespace Morew.Elab.Conic.Exponential

open Lean Lean.Meta Qq

/-- Exact exponential rules; named and native composite spellings share one identity. -/
inductive Rule where
  | exponential | logarithm | logSumExp | softplus | relativeEntropy
  deriving BEq, Repr

/-- Stable order for exhaustive certification, including both inequality orientations. -/
def rules : Array Rule :=
  #[.exponential, .logSumExp, .softplus, .relativeEntropy, .logarithm]

private def conjunction (rows : Array Expr) : Expr :=
  if rows.isEmpty then mkConst ``True
  else rows.pop.toList.foldr (mkApp2 (mkConst ``And)) rows.back!

private def operationCandidate (expression : Expr) : MetaM Bool := do
  let expression ← Affine.reduceStructure expression
  if expression.isAppOfArity ``Morew.Fn.logSumExp 2 ||
      expression.isAppOfArity ``Morew.Fn.softplus 1 ||
      expression.isAppOfArity ``Morew.Fn.relativeEntropy 2 then return true
  if let some atom ← Atom.recognizeAtom? expression then
    if atom.kind == .exp || atom.kind == .log then return true
  if expression.isAppOfArity ``HMul.hMul 6 then
    let right ← Affine.reduceStructure expression.getAppArgs[5]!
    if let some atom ← Atom.recognizeAtom? right then return atom.kind == .log
  return false

/-- Identify candidate exponential families without changing caller metavariables. -/
def isCandidate (predicate : Expr) : MetaM Bool := do
  let saved ← saveState
  try
    if ← Plan.unresolved predicate then return false
    withNewMCtxDepth do
      let domain ← Plan.predicateDomain predicate
      withLocalDeclD `point domain fun point => do
        let body ← Affine.reduceStructure (mkApp predicate point)
        if body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``GE.ge 4 ||
            body.isAppOfArity ``Eq 3 then
          let args := body.getAppArgs
          return (← operationCandidate args[args.size - 2]!) ||
            (← operationCandidate args.back!)
        return false
  finally saved.restore

private def sameOperation (actual expected : Expr) (operands : Nat) : MetaM Unit := do
  unless actual.getAppFn == expected.getAppFn &&
      actual.getAppNumArgs == expected.getAppNumArgs do
    throwError "unsupported native exponential operation {actual}"
  for a in actual.getAppArgs.toList.take (actual.getAppNumArgs - operands),
      b in expected.getAppArgs.toList.take (expected.getAppNumArgs - operands) do
    unless ← isDefEq a b do
      throwError "unsupported instance in native exponential operation {actual}"

private def sides (proof : Expr) : MetaM (Expr × Expr) := do
  let type ← inferType proof
  unless type.isAppOfArity ``Iff 2 do throwError "internal error: expected an equivalence"
  return (type.getAppArgs[0]!, type.getAppArgs[1]!)

private theorem dimensionPositive (n : Nat) [Nonempty (Fin n)] : 0 < n :=
  Fin.pos_iff_nonempty.mpr inferInstance

private theorem dimensionPositiveOfNe (n : Nat) (h : n ≠ 0) : 0 < n :=
  Nat.pos_of_ne_zero h

private def nonemptyEvidence (point dimension : Expr) : MetaM Expr := do
  if (← Affine.depends point dimension) || (← Plan.unresolved dimension) then
    throwError "log-sum-exp rewrite was not certified: dimension must be decision-independent"
  let n : Q(Nat) := dimension
  let goal : Q(Prop) := q(0 < $n)
  let nonzero : Q(Prop) := q($n ≠ 0)
  for declaration in ← getLCtx do
    let evidence := declaration.toExpr
    if (← Affine.depends point evidence) || (← Plan.unresolved evidence) then continue
    if ← isDefEq declaration.type goal then return evidence
    if ← isDefEq declaration.type nonzero then
      return ← mkAppM ``dimensionPositiveOfNe #[dimension, evidence]
  let saved ← saveState
  try
    let proof ← mkAppOptM ``dimensionPositive #[some dimension, none]
    if ← Plan.unresolved proof then throwError "unresolved finite nonemptiness"
    unless ← isDefEq (← inferType proof) goal do
      throwError "finite nonemptiness did not establish the required dimension bound"
    checkWithKernel proof
    return proof
  catch _ => saved.restore
  -- Numeral proofs are bounded; symbolic arithmetic is deliberately excluded.
  if let some value ← getNatValue? (← Affine.reduceStructure dimension) then
    if value > 0 && value ≤ 100000 then
      let proof ← mkDecideProof goal
      checkWithKernel proof
      return proof
  throwError "log-sum-exp rewrite was not certified: missing independent nonempty dimension evidence (0 < {dimension})"

private def signEvidence (point value : Expr) (retained : Array Expr)
    (remainderProof : Expr) (strict : Bool) (atom : String) : MetaM Expr := do
  if let some proof ← Domain.signFromRetained? point value retained remainderProof strict then
    return proof
  if strict then
    throwError "{atom} rewrite was not certified: missing positive constant margin; required an independent ε with 0 < ε and a retained constraint ε ≤ {value}"
  throwError "{atom} rewrite was not certified: missing nonnegative constant margin; required an independent ε with 0 ≤ ε and a retained constraint ε ≤ {value}"

private def logSumExpProof (point vector bound : Expr) : MetaM Expr := do
  let type ← whnf (← inferType vector)
  let .forallE _ index _ _ := type
    | throwError "log-sum-exp rewrite was not certified: expected a finite real vector"
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 do
    throwError "log-sum-exp rewrite was not certified: expected full Fin n indexing"
  let positive ← nonemptyEvidence point index.getAppArgs[0]!
  mkAppM ``Morew.Conic.Exponential.logSumExp_le_iff #[vector, bound, positive]

private def formula (name : Name) (arguments : Array Expr) : MetaM Expr := do
  let application ← mkAppM name arguments
  let definition ← getConstInfo name
  return (mkAppN definition.value! application.getAppArgs).headBeta

-- Only unfold our own definitions to compare the exact native formulas and
-- their canonical operation instances. Source helper applications stay opaque.
private def rawCompositeProof? (point operation bound : Expr) (retained : Array Expr)
    (remainderProof : Expr) : MetaM (Option (Rule × Expr)) := do
  if operation.isAppOfArity ``Real.log 1 then
    let inner ← Affine.reduceStructure operation.getAppArgs[0]!
    if inner.isAppOfArity ``Finset.sum 5 then
      let args := inner.getAppArgs
      unless (← whnf args[0]!).isAppOfArity ``Fin 1 do
        throwError "log-sum-exp rewrite was not certified: expected a sum over all of Fin n"
      let vector ← withLocalDeclD `i args[0]! fun i => do
        let summand ← Affine.reduceStructure (mkApp args[4]! i)
        let some atom ← Atom.recognizeAtom? summand
          | throwError "log-sum-exp rewrite was not certified: expected a native exponential summand"
        unless atom.kind == .exp do
          throwError "log-sum-exp rewrite was not certified: expected a native exponential summand"
        mkLambdaFVars #[i] atom.operands[0]!
      let expected ← formula ``Morew.Fn.logSumExp #[vector]
      sameOperation inner expected.getAppArgs[0]! 2
      unless ← isDefEq inner expected.getAppArgs[0]! do
        throwError "log-sum-exp rewrite was not certified: expected a sum over all of Fin n with canonical instances"
      return some (.logSumExp, ← logSumExpProof point vector bound)
    if inner.isAppOfArity ``HAdd.hAdd 6 then
      let args := inner.getAppArgs
      let right ← Affine.reduceStructure args[5]!
      if let some atom ← Atom.recognizeAtom? right then
        if atom.kind == .exp then
          let expected ← formula ``Morew.Fn.softplus #[atom.operands[0]!]
          sameOperation inner expected.getAppArgs[0]! 2
          unless ← isDefEq inner expected.getAppArgs[0]! do
            throwError "softplus rewrite was not certified: expected exactly Real.log (1 + Real.exp a)"
          return some (.softplus, ← mkAppM ``Morew.Conic.Exponential.softplus_le_iff
            #[atom.operands[0]!, bound])
  if operation.isAppOfArity ``HMul.hMul 6 then
    let numerator := operation.getAppArgs[4]!
    let right ← Affine.reduceStructure operation.getAppArgs[5]!
    if right.isAppOfArity ``Real.log 1 then
      let quotient ← Affine.reduceStructure right.getAppArgs[0]!
      if quotient.isAppOfArity ``HDiv.hDiv 6 then
        let denominator := quotient.getAppArgs[5]!
        let expected ← formula ``Morew.Fn.relativeEntropy #[numerator, denominator]
        sameOperation operation expected 2
        let expectedQuotient := expected.getAppArgs[5]!.getAppArgs[0]!
        sameOperation quotient expectedQuotient 2
        unless ← isDefEq operation expected do
          throwError "relative-entropy rewrite was not certified: expected exactly a * Real.log (a / b)"
        let nonnegative ← signEvidence point numerator retained remainderProof false "relative-entropy numerator"
        let positive ← signEvidence point denominator retained remainderProof true "relative-entropy denominator"
        return some (.relativeEntropy, ← mkAppM ``Morew.Conic.Exponential.relativeEntropy_le_iff
          #[numerator, denominator, bound, nonnegative, positive])
  return none

private def logarithmProof (point left right : Expr) (retained : Array Expr)
    (remainderProof : Expr) : MetaM Expr := do
  let some atom ← Atom.recognizeAtom? right
    | throwError "exponential rewrite was not certified: unsupported atom or inequality polarity"
  unless atom.kind == .log do
    throwError "exponential rewrite was not certified: expected an exponential upper bound or logarithmic lower bound"
  let positive ← signEvidence point atom.operands[0]! retained remainderProof true "logarithm"
  mkAppM ``Morew.Conic.Exponential.le_log_iff #[atom.operands[0]!, left, positive]

private def automaticProof (point body : Expr) (retained : Array Expr)
    (remainderProof : Expr) (preferLog : Bool) (selected? : Option Rule := none) :
    MetaM Expr := do
  let body ← Affine.reduceStructure body
  let ge := body.isAppOfArity ``GE.ge 4
  unless ge || body.isAppOfArity ``LE.le 4 do
    throwError "exponential rewrite was not certified: expected the supported inequality polarity, not equality or another context"
  let args := body.getAppArgs
  unless (← isDefEq args[0]! q(ℝ)) &&
      (← isDefEq args[1]! (mkConst ``Real.instLE)) do
    throwError "exponential rewrite was not certified: unsupported scalar or order instance"
  let left ← Affine.reduceStructure args[if ge then 3 else 2]!
  let right ← Affine.reduceStructure args[if ge then 2 else 3]!
  let lowerProof : MetaM (Rule × Expr) := do
    return (.logarithm, ← logarithmProof point left right retained remainderProof)
  let (matched, proof) ← if preferLog then
      lowerProof
    else if left.isAppOfArity ``Morew.Fn.logSumExp 2 then
      pure (.logSumExp, ← logSumExpProof point left.getAppArgs[1]! right)
    else if left.isAppOfArity ``Morew.Fn.softplus 1 then
      pure (.softplus, ← mkAppM ``Morew.Conic.Exponential.softplus_le_iff
        #[left.getAppArgs[0]!, right])
    else if left.isAppOfArity ``Morew.Fn.relativeEntropy 2 then do
      let a := left.getAppArgs[0]!
      let b := left.getAppArgs[1]!
      let ha ← signEvidence point a retained remainderProof false "relative-entropy numerator"
      let hb ← signEvidence point b retained remainderProof true "relative-entropy denominator"
      pure (.relativeEntropy, ← mkAppM ``Morew.Conic.Exponential.relativeEntropy_le_iff
        #[a, b, right, ha, hb])
    else if let some proof ← rawCompositeProof? point left right retained remainderProof then
      pure proof
    else if let some atom ← Atom.recognizeAtom? left then do
      if atom.kind == .exp then
        pure (.exponential, ← mkAppM ``Morew.Conic.Exponential.exp_le_iff
          #[atom.operands[0]!, right])
      else lowerProof
    else lowerProof
  if let some selected := selected? then
    unless matched == selected do
      throwError "the selected exponential rule does not match this predicate"
  let (source, _) ← sides proof
  unless ← isDefEq source body do
    throwError "exponential rewrite was not certified: the native rule does not match the complete selected bound"
  return proof

private def withRowDiagnostics {α : Type} (source : Expr) (action : MetaM α) : MetaM α := do
  try action
  catch error =>
    throwError "exponential rewrite was not certified for {source}: {error.toMessageData}"

private def planCore (source : Expr) (retained : Array Expr)
    (config : Affine.Config) (preferLog : Bool) (selected? : Option Rule := none) :
    MetaM (Except Affine.AffineError Plan.Prepared) :=
  Affine.withIsolatedMVars do
    try
      if ← Plan.unresolved source then throwError "unresolved metavariables in selected predicate"
      let domain ← Plan.predicateDomain source
      for row in retained do
        if ← Plan.unresolved row then throwError "unresolved metavariables in retained constraints"
        unless ← isDefEq (← Plan.predicateDomain row) domain do
          throwError "retained constraint has a different decision domain"
      let mut instances ← Affine.sourceFiniteInstances source
      for row in retained do instances := instances ++ (← Affine.sourceFiniteInstances row)
      let result ← Plan.withScopedFiniteInstances Plan.Prepared.replaceFVars instances.toList do
        withLocalDeclD `point domain fun point =>
          Plan.withScopedEvidence Plan.Prepared.replaceFVars point (mkApp source point) do
            withLocalDeclD `retained (conjunction (retained.map (mkApp · point))) fun evidence => do
              let proof ← automaticProof point (mkApp source point)
                (retained.map (mkApp · point)) evidence preferLog selected?
              let (_, target) ← sides proof
              if ← Affine.depends evidence target then
                throwError "generated exponential row depends on feasibility evidence"
              if target.isAppOfArity ``Exists 2 then
                if ← Affine.depends evidence proof then
                  throwError "finite exponential lift unexpectedly depends on retained evidence"
                let args := target.getAppArgs
                if ← Affine.depends point args[0]! then
                  throwError "the auxiliary type depends on a decision variable"
                let target ← mkLambdaFVars #[point] args[1]!
                let pointwise ← mkLambdaFVars #[point] proof
                let lift ← mkAppM ``Morew.ExactConstraintLift.mk #[args[0]!, target, pointwise]
                let lift ← Plan.checkLift source lift
                return .inl (← withRowDiagnostics source (Plan.finish source domain lift config))
              let rowPredicates := #[← instantiateMVars (← mkLambdaFVars #[point] target)]
              let certifiedRows ← withRowDiagnostics source (Plan.certifyRows rowPredicates config)
              let conditionalIff ← instantiateMVars (← mkLambdaFVars #[point, evidence] proof)
              if ← Plan.unresolved conditionalIff then
                throwError "exponential certificate contains unresolved metavariables"
              checkWithKernel conditionalIff
              Plan.prepareContextual source retained { domain, rowPredicates, certifiedRows, conditionalIff }
      return .ok result
    catch error =>
      return .error { expression := source, reason := ← addMessageContext error.toMessageData }

/-- Certify an exponential replacement, using only the supplied retained entries
for decision-dependent domains. The selected row must be excluded from them.

Each orientation is accepted only after certifying all its rows. An independent
exponential expression can itself be an affine logarithmic lower bound, so a
failed upper-bound attempt must not hide a successful logarithmic rewrite. -/
def plan (source : Expr) (retained : Array Expr := #[])
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError Plan.Prepared) := do
  match ← planCore source retained config false with
  | .ok result => return .ok result
  | .error error =>
    match ← planCore source retained config true with
    | .ok result => return .ok result
    | .error _ => return .error error

/-- Certify exactly one native rule, without treating a lower-log fallback as
another upper rule or counting a composite's alternate spelling twice. -/
def planRule (rule : Rule) (source : Expr) (retained : Array Expr := #[])
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError Plan.Prepared) :=
  planCore source retained config (rule == .logarithm) (some rule)

end Morew.Elab.Conic.Exponential
