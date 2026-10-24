/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation
import Mathlib.Data.Nat.Basic

/-!
# Atomic reformulation presentation updates

Constraint removal, replacement, and addition preserve their specified order.
Malformed replacement batches are rejected before updating the presentation.
-/

namespace MorewTest.Reformulation.PresentationUpdates

open Lean
open Morew.Elab.Reformulation

private def expect (condition : Bool) (message : String) :
    Lean.Elab.Command.CommandElabM Unit :=
  unless condition do
    throwError message

private def placeholder : Expr := .const ``True.intro []

private def constraint (name : Name) : ConstraintEntry := {
  name
  predicate := placeholder
}

private def basePresentation : PresentationState := {
  sense := .minimize
  domainType := .const ``Nat []
  valueType := .const ``Nat []
  binders := #[{ name := `n, type := .const ``Nat [] }]
  objective := placeholder
  constraints := #[constraint `a, constraint `b, constraint `c]
}

private def replacement (index : Nat)
    (entries : Array ConstraintEntry) : ConstraintReplacement := {
  index
  entries
  pointwiseIff := placeholder
}

private def constraintNames (state : PresentationState) : Array Name :=
  state.constraints.map (·.name)

run_cmd do
  let .ok removed := basePresentation.applyDelta {
      constraintReplacements := #[replacement 1 #[]]
    }
    | throwError "zero-entry constraint replacement was rejected"
  expect (constraintNames removed == #[`a, `c])
    "zero-entry replacement did not remove exactly the selected constraint"

  let .ok replaced := basePresentation.applyDelta {
      constraintReplacements := #[replacement 1 #[constraint `x]]
    }
    | throwError "one-entry constraint replacement was rejected"
  expect (constraintNames replaced == #[`a, `x, `c])
    "one-entry replacement did not preserve surrounding order"

  let .ok expanded := basePresentation.applyDelta {
      constraintReplacements := #[replacement 1 #[constraint `x, constraint `y]]
    }
    | throwError "many-entry constraint replacement was rejected"
  expect (constraintNames expanded == #[`a, `x, `y, `c])
    "many-entry replacement did not splice entries in source order"

  let .ok replacedAndAdded := basePresentation.applyDelta {
      constraintReplacements := #[replacement 0 #[], replacement 1 #[constraint `x]]
      constraintAdditions := #[{
        entry := constraint `tail
        pointwiseIff := placeholder
      }]
    }
    | throwError "combined removal, replacement, and addition was rejected"
  expect (constraintNames replacedAndAdded == #[`x, `c, `tail])
    "removal, replacement, and addition did not preserve their specified order"

run_cmd do
  let duplicate : PresentationDelta := {
    constraintReplacements := #[
      replacement 0 #[constraint `x],
      replacement 0 #[constraint `y]
    ]
  }
  match basePresentation.applyDelta duplicate with
  | .error (.duplicateConstraintReplacement 0) => pure ()
  | _ => throwError "duplicate constraint replacements were not rejected"

  let outOfRange : PresentationDelta := {
    constraintReplacements := #[replacement 3 #[constraint `x]]
  }
  match basePresentation.applyDelta outOfRange with
  | .error (.constraintIndexOutOfBounds 3 3) => pure ()
  | _ => throwError "an out-of-range constraint replacement was not rejected"

end MorewTest.Reformulation.PresentationUpdates
