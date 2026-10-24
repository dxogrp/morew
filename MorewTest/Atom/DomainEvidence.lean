/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Atom.Support

/-!
# Atom consumer domain evidence
-/

namespace MorewTest.Atom.DomainEvidence

open Lean Lean.Meta Lean.Elab.Term
open Morew Morew.Elab.Atom

/-! A consuming rule owns domain conditions, independently of recognition. -/

private def mockLogConsumer (expression : Expr) (evidence? : Option Expr := none) :
    MetaM Expr := do
  let some atom ← recognizeAtom? expression
    | throwError "mock logarithm consumer requires a recognized operation"
  unless atom.kind == .log do
    throwError "mock logarithm consumer requires a logarithm"
  let obligation ← mkLT (← mkNumeral (mkConst ``Real) 0) atom.operands[0]!
  let proof ← mkFreshExprMVar obligation
  if let some evidence := evidence? then
    unless ← isDefEq (← inferType evidence) obligation do
      throwError "provided evidence does not establish logarithm positivity"
    proof.mvarId!.assign evidence
  return proof

open Real in
run_cmd Lean.Elab.Command.liftTermElabM do
  let qualified ← elaborate (← `(fun x : ℝ => Real.log x))
  let unqualified ← elaborate (← `(fun x : ℝ => log x))
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let first ← mockLogConsumer (qualified.beta #[x])
    let second ← mockLogConsumer (unqualified.beta #[x])
    let expected ← mkLT (← mkNumeral (mkConst ``Real) 0) x
    unless ← isDefEq (← inferType first) expected do
      throwError "qualified logarithm has the wrong domain obligation"
    unless ← isDefEq (← inferType second) expected do
      throwError "unqualified logarithm has the wrong domain obligation"
    if (← first.mvarId!.isAssigned) || (← second.mvarId!.isAssigned) then
      throwError "missing domain evidence was silently supplied"
    withLocalDeclD `positive expected fun positive => do
      for expression in #[qualified.beta #[x], unqualified.beta #[x]] do
        let proof ← mockLogConsumer expression (some positive)
        unless (← instantiateMVars proof) == positive do
          throwError "the logarithm consumer did not use the supplied evidence"

end MorewTest.Atom.DomainEvidence
