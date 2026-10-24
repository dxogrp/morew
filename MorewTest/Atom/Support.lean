/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Atom
import Lean.Elab.Command

/-!
# Shared atom test assertions

Elaborate source terms and check recognition results without changing their heads,
operands, or metadata. This module also supplies the named-helper fixture shared
by recognition-boundary and surface tests.
-/

namespace MorewTest.Atom

open Lean Lean.Meta Lean.Elab.Term
open Morew Morew.Elab.Atom

def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

def assertAtom (term : TSyntax `term) (kind : AtomKind)
    (operandIndices : Array Nat) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaTelescope expression fun binders body => do
    let some atom ← recognizeAtom? body
      | throwError "expected an atom in {body}"
    unless atom.kind == kind do
      throwError "recognized the wrong operation in {body}"
    unless atom.original == body do
      throwError "recognition changed the original expression"
    unless atom.operands == operandIndices.map (binders[·]!) do
      throwError "recognition changed the operands or their order in {body}"

def assertUnsupported (term : TSyntax `term) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaTelescope expression fun _ body => do
    if (← recognizeAtom? body).isSome then
      throwError "unexpectedly recognized unsupported expression {body}"

noncomputable abbrev exponentialAlias (x : ℝ) : ℝ := Real.exp x

end MorewTest.Atom
