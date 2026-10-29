/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.PrettyPrinter

/-!
# Mathematical display recipes for finite power chains

These recipes are used only by the problem printer. Their syntax leaves retain
the names of the checked presentation; they are never reconstructed as terms.
-/

namespace Morew.Syntax

open Lean

/-- One of the fixed rows in a geometric-mean or inverse-product chain.
`membership` retains a terminal cone membership rather than displaying the
earlier comparison. All syntax leaves are closed presentation syntax. -/
inductive PowerChainRow where
  /-- Equality of the first auxiliary and input coordinates. -/
  | first (auxiliary source : Syntax) (membership : Bool)
  /-- The finite family joining consecutive prefix means. -/
  | step (auxiliary source : Syntax) (index : Name) (size : Syntax)
  /-- Nonnegativity of the last auxiliary. -/
  | nonnegative (auxiliary last : Syntax) (membership : Bool)
  /-- A lower bound on the last auxiliary. -/
  | bound (value auxiliary last : Syntax) (membership : Bool)
  /-- The final inverse-product power membership. -/
  | inverse (value auxiliary last exponent : Syntax)
  deriving Inhabited

private def coordinate (render : Syntax → CoreM Format) (vector : Syntax)
    (index : Format) : CoreM Format := do
  let vectorFormat ← render vector
  let vectorFormat := if vector.isIdent then vectorFormat else f!"({vectorFormat})"
  return f!"{vectorFormat}[{index}]"

private def operand (render : Syntax → CoreM Format) (value : Syntax) : CoreM Format := do
  let valueFormat ← render value
  -- Parentheses also protect conditional, lambda, and compound scalar leaves.
  return if value.isIdent || value.isOfKind numLitKind then valueFormat else f!"({valueFormat})"

private def powerMembership (x y z exponent : Format) : Format :=
  Format.group <| f!"({x}, {y}, {z}) ∈" ++
    Format.nest 2 (Format.line ++ f!"POW ({exponent})")

/-- Format one recognized chain row using the caller's ordinary syntax printer
for every retained leaf. Grouping leaves line wrapping to the active width. -/
def PowerChainRow.format (row : PowerChainRow)
    (render : Syntax → CoreM Format) : CoreM Format := do
  match row with
  | .first auxiliary source membership =>
      let left ← coordinate render auxiliary "0"
      let right ← coordinate render source "0"
      return if membership then f!"{left} - {right} ∈ " ++ "({0} : Set ℝ)"
        else f!"{left} = {right}"
  | .step auxiliary source index size =>
      let index ← render (mkIdent index)
      let size ← render size
      let left ← coordinate render auxiliary index
      let input ← coordinate render source f!"{index} + 1"
      let right ← coordinate render auxiliary f!"{index} + 1"
      let membership := powerMembership left input right f!"({index} + 1) / ({index} + 2)"
      return Format.group <| f!"∀ {index} : ℕ, {index} < {size} ⇒" ++
        Format.nest 2 (Format.line ++ membership)
  | .nonnegative auxiliary last membership =>
      let value ← coordinate render auxiliary (← render last)
      return if membership then f!"{value} ∈ ℝ₊" else f!"0 ≤ {value}"
  | .bound value auxiliary last membership =>
      let value ← operand render value
      let last ← coordinate render auxiliary (← render last)
      return if membership then f!"{last} - {value} ∈ ℝ₊" else f!"{value} ≤ {last}"
  | .inverse value auxiliary last exponent =>
      let value ← operand render value
      let last ← coordinate render auxiliary (← render last)
      return powerMembership value last "1" (← render exponent)

end Morew.Syntax
