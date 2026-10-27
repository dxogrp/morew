/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Automatic
import Morew.Elab.Atom

/-!
# Checked exponential-cone replacements

This focused interface uses the public registry and the same checked retained
margin policy as complete conic discovery. Native and named formulas remain
separate representation declarations, with no helper unfolding.
-/

namespace Morew.Elab.Conic.Exponential

open Lean Lean.Meta

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
    if ← Morew.Elab.Rewrite.Plan.unresolved predicate then return false
    withNewMCtxDepth do
      let domain ← Morew.Elab.Rewrite.Plan.predicateDomain predicate
      withLocalDeclD `point domain fun point => do
        let body ← Affine.reduceStructure (mkApp predicate point)
        if body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``GE.ge 4 ||
            body.isAppOfArity ``Eq 3 then
          let args := body.getAppArgs
          return (← operationCandidate args[args.size - 2]!) ||
            (← operationCandidate args.back!)
        return false
  finally saved.restore

/-- Certify a unique registered exponential replacement. -/
def plan (source : Expr) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Affine.AffineError Plan.Prepared) :=
  Automatic.planUnique source retained provider ((`Morew.Conic.Exponential).isPrefixOf ·)

end Morew.Elab.Conic.Exponential
