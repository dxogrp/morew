/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Polyhedral
import Morew.Elab.Conic.SecondOrder
import Morew.Elab.Conic.Exponential

/-!
# Automatic exact-rule selection

Targeted rewriting retains its first-certified-success policy. Terminal lowering
uses exhaustive certification after checking whether a row is already affine.
Each speculative attempt isolates metavariables; the enclosing transaction also
rolls back successful proof dependencies when selection is ambiguous.
-/

namespace Morew.Elab.Conic.Automatic

open Lean Lean.Meta

/-- Identities of independent native rule attempts. Second-order operation heads
and norm carriers select disjoint variants within their respective attempts. -/
inductive RuleId where
  | polyhedral (rule : Polyhedral.Rule)
  | secondOrder
  | exponential (rule : Exponential.Rule)
  deriving BEq, Repr

/-- Readable identities for diagnostics, independent of theorem pretty-printing. -/
def RuleId.description : RuleId → String
  | .polyhedral .absolute => "absolute-value upper bound"
  | .polyhedral .positivePart => "positive-part upper bound"
  | .polyhedral .maximum => "maximum upper bound"
  | .polyhedral .minimum => "minimum lower bound"
  | .polyhedral .supremum => "finite-supremum upper bound"
  | .polyhedral .infimum => "finite-infimum lower bound"
  | .polyhedral .norm => "polyhedral norm upper bound"
  | .secondOrder => "second-order upper bound"
  | .exponential .exponential => "exponential upper bound"
  | .exponential .logarithm => "logarithmic lower bound"
  | .exponential .logSumExp => "log-sum-exp upper bound"
  | .exponential .softplus => "softplus upper bound"
  | .exponential .relativeEntropy => "relative-entropy upper bound"

/-- Preserve targeted rewriting's family order and certified fallback behavior. -/
def planFirst (predicate : Expr) (retained : Array Expr := #[])
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError Plan.Prepared) :=
  Affine.withIsolatedMVars do
    let mut candidateError? := none
    if ← Exponential.isCandidate predicate then
      match ← Exponential.plan predicate retained config with
      | .ok result => return .ok result
      | .error error => candidateError? := some error
    if ← SecondOrder.isCandidate predicate then
      match ← SecondOrder.planReplacement predicate retained config with
      | .ok result => return .ok result
      | .error error =>
        if candidateError?.isNone then candidateError? := some error
    match ← Polyhedral.plan predicate none config with
    | .ok result => return .ok (.inl result)
    | .error error => return .error (candidateError?.getD error)

/-- Certify every applicable native exact rule and require a unique success.

The terminal caller first normalizes already-affine rows. This function itself
does not perform that shortcut: constant inequalities can therefore exhibit
real rule ambiguity when this lower-level interface is called directly.
Candidate heads and failed obligations never count as successful matches.
No custom rules are searched, and no objective or nested expression is lifted. -/
def planUnique (predicate : Expr) (retained : Array Expr := #[])
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError Plan.Prepared) :=
  Affine.withIsolatedMVars do
    let mut successes : Array (RuleId × Plan.Prepared) := #[]
    if ← Exponential.isCandidate predicate then
      for rule in Exponential.rules do
        if let .ok result ← Exponential.planRule rule predicate retained config then
          successes := successes.push (.exponential rule, result)
    if ← SecondOrder.isCandidate predicate then
      if let .ok result ← SecondOrder.planReplacement predicate retained config then
        successes := successes.push (.secondOrder, result)
    for rule in Polyhedral.rules do
      if let .ok result ← Polyhedral.planRule rule predicate config then
        successes := successes.push (.polyhedral rule, .inl result)
    if let [(_, result)] := successes.toList then
      return .ok result
    if successes.size > 1 then
      let descriptions := successes.toList.map fun (rule, _) => rule.description
      return .error {
        expression := predicate
        reason := ← addMessageContext
          m!"ambiguous exact conic rules: {String.intercalate ", " descriptions}"
      }
    -- Reuse the established, source-specific diagnostic rather than reporting
    -- a rejected attempt for an unrelated operation earlier in the rule table.
    match ← planFirst predicate retained config with
    | .error error => return .error error
    | .ok _ => return .error {
        expression := predicate
        reason := "internal error: exhaustive conic selection omitted a certified rule"
      }

end Morew.Elab.Conic.Automatic
