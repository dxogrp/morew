/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import Morew.Reformulation.Replace
import Morew.Elab.Expr

/-!
# Targeted exact conic rewriting

The surface handler selects one current presentation label, preflights the
generated name family, and materializes a checked in-place replacement.

Automatic selection uses `@[morew_conic]` declarations, including the shipped
rules. It requires one fully certified result; multiple successful declarations
are reported by fully qualified name. Registration and import order do not
choose a winner. `using ruleName` selects that declaration alone and infers its
parameters from the row, whether or not it is registered. Applied certificate
terms retain ordinary Lean elaboration, and explicit failures never fall back
to another rule.

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
custom target rows, as are exponential memberships and grouped finite
families of exponential memberships.

Native Euclidean norms, scalar squares, and finite sums of squares become one
SOC or rotated-SOC membership row. Quotients of squares require a positive
constant lower margin on the denominator, obtained from an unchanged constraint
(or a directly proved positive constant denominator). Existing margin rows stay
in place. The command remains nonterminal and does not certify a whole problem
as conic.

Exponential upper bounds and logarithmic lower bounds become exponential-cone
memberships. Logarithms require a positive constant lower margin on their
argument. Relative-entropy upper bounds retain a nonnegative numerator margin
and a positive denominator margin, including zero numerators. Finite nonempty
log-sum-exp and softplus use one finite auxiliary vector, one grouped family of
exponential memberships, and one sum bound. Domain evidence is taken only from
independent constants or retained entries; no selected constraint proves its
own domain.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew.Elab.Reformulation

private abbrev Prepared := Morew.Elab.Conic.Plan.Prepared

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

private def conicStyle : Replace.Style := {
  family := "conic", diagnostic := "conic", certificateKind := `_conicCertificate
}

private def materializeConic (state : ReformState) (index : Nat)
    (prepared : Prepared) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    -- Section proof parameters may still mention assigned instance variables.
    -- The kernel needs their instantiated local types as well as the term.
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared : Prepared :=
      Morew.Elab.Conic.Plan.Prepared.replaceFVars prepared preparedVars sectionFVars
    let replacement ← match prepared with
      | .inl result => do
        Morew.Elab.Reformulation.Replace.rewriteConstraint typed.presentation index
          result.lift result.auxiliary? result.nextDomain result.rowPredicates result.targetIff
      | .inr contextual => do
        Morew.Elab.Reformulation.Replace.rewriteConstraintContextual typed.presentation index
          contextual.rowPredicates contextual.conditionalIff
    Replace.finish conicStyle state typed index {
      auxiliary? := prepared.auxiliary?
      nextDomain := prepared.nextDomain
      rowPredicates := prepared.rowPredicates
      certificate := prepared.certificate
      replacement
    } allocation

/-- Select and certify a whole-constraint rewrite, deferring named
materialization until the runner has allocated its generated family. -/
def prepareConic (state : ReformState) (step : Syntax)
    (selector : TSyntax `ident) (rule? : Option (TSyntax `term)) :
    CommandElabM SurfaceStepDraft := withRef step do
  let index ← Replace.findConstraint state selector
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let (rule?, declaration?) ← Replace.elaborateRule selector rule?
    let predicate := presentation.constraints[index]!.predicate
    let result : Except Morew.Elab.Expr.Error Prepared ←
      Morew.Elab.Conic.Plan.withPresentationFiniteInstances
        Morew.Elab.Conic.Plan.Prepared.replaceFVars presentation do
        if let some name := declaration? then do
          let retained := presentation.constraints.extract 0 index ++
            presentation.constraints.extract (index + 1) presentation.constraints.size
          Morew.Elab.Conic.Rewrite.planDeclaration predicate name (retained.map (·.predicate))
        else if let some rule := rule? then do
          let retained := presentation.constraints.extract 0 index ++
            presentation.constraints.extract (index + 1) presentation.constraints.size
          Morew.Elab.Conic.Rewrite.planExplicit predicate rule (retained.map (·.predicate))
        else do
          let retained := presentation.constraints.extract 0 index ++
            presentation.constraints.extract (index + 1) presentation.constraints.size
          Morew.Elab.Conic.Rewrite.planUnique predicate (retained.map (·.predicate))
    match result with
    | .error error =>
      throwErrorAt selector "constraint `{selector.getId.eraseMacroScopes}`: {error.reason}"
    | .ok result => pure (result, sectionFVars)
  return {
    nameRequests := ← Replace.nameRequests conicStyle selector
      prepared.auxiliary?.isSome prepared.rowPredicates.size
    materialize := materializeConic state index prepared preparedVars
  }

end Morew.Reformulation.Internal
