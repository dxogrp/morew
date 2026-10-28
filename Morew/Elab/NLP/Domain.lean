/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Smooth
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Inferred open domains with certified feasible inclusion

`certify feasible sources` checks the whole feasibility predicate, infers a
common open evaluation domain, and returns C² proofs for the original functions
and a proof that every feasible point belongs to that domain. The admitted rows
are canonical real closed comparisons, conjunctions, and `True`. The original
predicate and functions are never rewritten.

Decision spaces are real scalars, products, and finite real vectors, as in the
global certifier. This space validation also applies to empty source arrays.

Native log, square root, and fixed real powers require positive arguments;
inverse and division require nonzero denominators. These requirements also apply
to constants. Unknown constant helper calls retain requirements from supported
scalar, product, and finite-vector arguments, without unfolding helper bodies.
Ordinary function arguments, proof arguments, and unsupported value spaces remain
opaque. This policy is deliberately stricter than `Smooth.certifyGlobal`'s
constant-function rule.

Decision-dependent value helpers expand on demand under the shared source
budget configured by `morew.smooth.*`. Native recognition and domain obligations
still apply to their bodies. Independent helper bodies and whole predicates
remain opaque, and each supplied source starts a fresh expansion session.

Finite sums use precisely their supplied support. Nested restricted operations
use continuity on their child domains. Inclusion proofs use admitted constraints,
independent parameter evidence, and previously established domain conditions;
no condition is added to feasibility. Failed attempts restore caller state.

This internal API covers exactly the supplied functions, in input order. A caller
building a complete NLP form must separately establish that these functions cover
the objective and every residual. There is no modeling command or row normalization
here. An empty source array still validates the entire predicate and returns the
unrestricted domain. Smoothness asserts no convexity.
-/

namespace Morew.Elab.NLP.Domain

open Lean Lean.Meta Qq

/-- Diagnostics retain the source/row position and the typed local obstruction. -/
structure DomainError where
  /-- The original function or feasibility predicate. -/
  source : Expr
  /-- The supplied function's position, when failure concerns a function. -/
  sourceIndex? : Option Nat := none
  /-- The conjunction leaf's position, when admission of a row fails. -/
  rowIndex? : Option Nat := none
  /-- The local expression where certification stopped. -/
  expression : Expr
  /-- Its type in the captured local context. -/
  type : Expr
  /-- The failure class, shared with the recursive smoothness traversal. -/
  kind : Smooth.SmoothFailureKind
  /-- The exact missing domain condition, if feasibility inclusion failed. -/
  obligation? : Option Expr := none
  /-- An explanation with the decision and finite-index contexts attached. -/
  reason : MessageData

instance : ToMessageData DomainError := ⟨(·.reason)⟩

/-- Checked domain data for exactly the caller's supplied functions. -/
structure DomainResult where
  /-- A common evaluation set in the original decision space. -/
  domain : Expr
  /-- A proof that the common evaluation set is open. -/
  domainIsOpen : Expr
  /-- C² certificates on the common domain, in input order. -/
  smooth : Array Expr
  /-- A proof of `∀ x, feasible x → x ∈ domain`. -/
  feasibleMemDomain : Expr

private def convertError (index : Nat) (error : Smooth.SmoothError) : DomainError := {
  source := error.source, sourceIndex? := some index
  expression := error.expression, type := error.type, kind := error.kind
  obligation? := error.obligation?, reason := error.reason
}

private def certifyCore (feasible : Expr) (sources : Array Expr)
    (facts? : Option Evidence.FactsProvider := none) :
    MetaM (Except DomainError DomainResult) := do
  if facts?.isNone then
    if let .error error ← Evidence.admit feasible then
      return .error {
        source := feasible, rowIndex? := some error.rowIndex
        expression := error.expression, type := error.type
        kind := .unsupportedRow, reason := error.reason
      }
  else if !(← Evidence.complete feasible) then
    return .error {
      source := feasible, expression := feasible, type := ← inferType feasible
      kind := .unresolved
      reason := ← addMessageContext m!"feasibility contains unresolved expressions or placeholders"
    }
  let .forallE _ decision _ _ ← whnf (← inferType feasible)
    | throwError "expected a feasibility predicate"
  let opened : Except MessageData Expr ← try
    pure (.ok (← Space.withCanonicalSpaces #[decision] <|
      mkAppOptM ``Morew.NLP.Domain.univ_open #[some decision, none]))
    catch exception => pure (.error exception.toMessageData)
  if let .error reason := opened then
    return .error {
      source := feasible, expression := feasible, type := ← inferType feasible
      kind := .unsupportedSpace
      reason := ← addMessageContext m!"unsupported decision space {decision}: {reason}"
    }
  let .ok domainIsOpen := opened | unreachable!
  let mut result : DomainResult := {
    domain := ← mkAppOptM ``Set.univ #[some decision]
    domainIsOpen := domainIsOpen
    smooth := #[]
    feasibleMemDomain := ← mkAppM ``Morew.NLP.Domain.univ_includes #[feasible]
  }
  for index in [:sources.size] do
    let source := sources[index]!
    if ← Expr.hasUnresolved source then
      return .error {
        source, sourceIndex? := some index, expression := source, type := ← inferType source
        kind := .unresolved
        reason := ← addMessageContext m!"source {index} contains unresolved expressions"
      }
    unless ← isDefEq (← inferType source) (← mkArrow decision (mkConst ``Real)) do
      return .error {
        source, sourceIndex? := some index, expression := source, type := ← inferType source
        kind := .unsupportedSpace
        reason := ← addMessageContext m!"source {index} must have type {decision} → ℝ"
      }
    let outcome ← Smooth.certifyOnFeasible feasible source #[result.feasibleMemDomain] facts?
    if let .error error := outcome then return .error (convertError index error)
    let .ok child := outcome | unreachable!
    if result.smooth.isEmpty then
      result := {
        domain := child.domain
        domainIsOpen := child.isOpen
        smooth := #[child.smooth]
        feasibleMemDomain := child.included
      }
    else
      let domain ← mkAppM ``Morew.NLP.Domain.inter #[result.domain, child.domain]
      let left ← mkAppM ``Morew.NLP.Domain.inter_left #[result.domain, child.domain]
      let right ← mkAppM ``Morew.NLP.Domain.inter_right #[result.domain, child.domain]
      let mut smooth := #[]
      for i in [:result.smooth.size] do
        smooth := smooth.push (← Space.withCanonicalSpaces #[decision] <|
          mkAppM ``Morew.NLP.Domain.restrict
            #[sources[i]!, result.domain, domain, result.smooth[i]!, left])
      smooth := smooth.push (← Space.withCanonicalSpaces #[decision] <|
        mkAppM ``Morew.NLP.Domain.restrict #[source, child.domain, domain, child.smooth, right])
      result := {
        domain
        domainIsOpen := ← Space.withCanonicalSpaces #[decision] <|
          mkAppM ``Morew.NLP.Domain.inter_open
            #[result.domain, child.domain, result.domainIsOpen, child.isOpen]
        smooth
        feasibleMemDomain := ← mkAppM ``Morew.NLP.Domain.inter_includes
          #[feasible, result.domain, child.domain, result.feasibleMemDomain, child.included]
      }
  let expectedOpen ← Space.withCanonicalSpaces #[decision] <|
    mkAppM ``IsOpen #[result.domain]
  unless ← isDefEq (← inferType result.domainIsOpen) expectedOpen do
    throwError "domain certificate does not establish openness of the returned set"
  let expectedInclusion ← withLocalDeclD `point decision fun point => do
    let membership ← mkAppM ``Membership.mem #[result.domain, point]
    mkForallFVars #[point] (← mkArrow (mkApp feasible point) membership)
  unless ← isDefEq (← inferType result.feasibleMemDomain) expectedInclusion do
    throwError "domain certificate changed the original feasibility predicate"
  for i in [:sources.size] do
    let expected ← Space.withCanonicalSpaces #[decision] <|
      mkAppM ``ContDiffOn #[q(ℝ), q((2 : WithTop ℕ∞)), sources[i]!, result.domain]
    unless ← isDefEq (← inferType result.smooth[i]!) expected do
      throwError "domain certificate changed source {i} or its analytic instances"
  for proof in result.smooth ++ #[result.domainIsOpen, result.feasibleMemDomain] do
    if proof.hasSorry || (← Expr.hasUnresolved proof) then
      throwError "domain certificate contains unresolved evidence or a placeholder"
    checkWithKernel proof
  return .ok result

/-- Infer an open common domain and kernel-check smoothness and feasible inclusion.

The result covers precisely `sources`, not an implicitly discovered whole model.
Failures restore metavariables and auxiliary declarations. Existing source rows
are evidence only: no new domain condition is added to their predicate.
-/
def certify (feasible : Expr) (sources : Array Expr) :
    MetaM (Except DomainError DomainResult) :=
  State.withIsolatedMVars do
    try
      certifyCore feasible sources
    catch exception =>
      return .error {
        source := feasible, expression := feasible, type := ← inferType feasible
        kind := .invalidInstance
        reason := ← addMessageContext exception.toMessageData
      }

/-- Internal certification using checked projections of a separately admitted row
grammar. The provider receives the actual feasibility proof; all returned analytic
and inclusion certificates are checked against that unchanged predicate. -/
def certifyWithEvidence (feasible : Expr) (sources : Array Expr)
    (facts : Evidence.FactsProvider) : MetaM (Except DomainError DomainResult) :=
  State.withIsolatedMVars do
    try
      certifyCore feasible sources (some facts)
    catch exception =>
      return .error {
        source := feasible, expression := feasible, type := ← inferType feasible
        kind := .invalidInstance
        reason := ← addMessageContext exception.toMessageData
      }

end Morew.Elab.NLP.Domain
