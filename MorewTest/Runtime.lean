/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import Morew.Affine
import Morew.Substitution
import Morew.Rewrite.Polyhedral
import Morew.Fn.Norm
import Morew.Elab.Atom
import Morew.Elab.Expr
import Morew.Elab.Expansion
import Morew.Elab.Reformulation.Names
import Morew.Elab.State
meta import Morew.Elab.Atom
meta import Morew.Elab.Expansion

/-! Ordinary runtime consumers of mathematical constructors, recovery maps, and reusable helpers. -/

namespace MorewTest.Runtime

open Morew

def translation (offset : ℝ) : Affine.Certified (fun x : ℝ => x + offset) :=
  Affine.Certified.add (Affine.Certified.id ℝ) (Affine.Certified.const ℝ offset)

example (offset x : ℝ) : (translation offset).map x = x + offset := rfl

def recoverShift (offset value : ℝ) : ℝ :=
  (Substitution.addRight (fun _ : Unit => offset)).preimage () ⟨value, True.intro⟩

example (offset value : ℝ) : recoverShift offset value + offset = value :=
  sub_add_cancel value offset

def absoluteRepresentation : EpigraphRepr (fun x : ℝ => |x|) :=
  Rewrite.absEpigraph

example (x bound : ℝ) :
    |x| ≤ bound ↔ ∃ auxiliary, absoluteRepresentation.target x bound auxiliary :=
  absoluteRepresentation.source_iff_exists x bound

def distanceInf {n : Nat} (x y : Fin n → ℝ) : ℝ :=
  Fn.normInf (x - y)

example {n : Nat} (x y : Fin n → ℝ) : 0 ≤ distanceInf x y :=
  Fn.normInf_nonneg (x - y)

-- Reusable name and expression-state helpers also compile in ordinary consumers.
def allocateNames : Except Elab.Reformulation.NamePreflightError
    Elab.Reformulation.NameAllocation :=
  Elab.Reformulation.preflightNameRequests {} #[
    { id := 0, kind := .generatedBinderFamily, requested := `value },
    { id := 1, kind := .explicitDecisionBinder, requested := `value }]

def isolateExpressions (action : Lean.MetaM (Except String Lean.Expr)) :
    Lean.MetaM (Except String Lean.Expr) :=
  Elab.State.withIsolatedMVars action

def withExpressionInstances (instances : List Lean.Expr) (action : Lean.MetaM Lean.Expr) :
    Lean.MetaM Lean.Expr :=
  Elab.State.withInstances `instance instances action

-- Atom recognition, structural reduction, and expansion budgets are reusable outside elaborators.
def recognizeOperation (expression : Lean.Expr) :
    Lean.MetaM (Option Elab.Atom.AtomApplication) :=
  Elab.Atom.recognizeAtom? expression

def hoistProjection (expression : Lean.Expr) : Lean.Expr :=
  Elab.Expr.hoistProjectionLets expression

def canExpand (depth steps nodes : Nat) : Bool :=
  Elab.Expansion.enabled {
    depth, steps, nodes
    depthOption := `depth, stepsOption := `steps, nodesOption := `nodes
    label := "runtime"
  }

#guard canExpand 1 1 1 && !canExpand 0 1 1 && !canExpand 1 0 1 && !canExpand 1 1 0

#eval show Lean.MetaM Unit from do
  Lean.Meta.withLocalDeclD `x (Lean.mkConst ``Real) fun x => do
    let expression := Lean.mkApp (Lean.mkConst ``Real.exp) x
    let some atom ← recognizeOperation expression
      | throwError "failed to recognize the real exponential"
    unless atom.kind == .exp && atom.original == expression && atom.operands == #[x] do
      throwError "recognition changed the operation or its operand"
  if (← recognizeOperation (.sort .zero)).isSome then
    throwError "unexpectedly recognized a sort as a real operation"

end MorewTest.Runtime
