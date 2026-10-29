/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Boundaries of readable finite-index cleanup

The presentation printer may abbreviate native finite indices, but ordinary
printing, exact replay, named expressions, and altered instances retain their
meaning. These direct tests complement the complete finite-chain workflows.
-/

namespace MorewTest.Reformulation.PresentationIndices

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew.Reformulation.Internal

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasSorry then
    throwError "presentation test contains an incomplete term"
  return expression

private def render (expression : Expr) (replay : Bool := false) :
    TermElabM (Syntax × String) := do
  let stx ← delabPresentationTerm expression #[] replay
  -- Direct syntax formatting marks frozen identifiers with a hygiene dagger;
  -- the stored presentation formatter omits it. It is irrelevant to spelling.
  return (stx, (← PrettyPrinter.ppTerm ⟨stx⟩).pretty.replace "✝" "")

private def checkReplay (expression : Expr) (stx : Syntax) : TermElabM Unit := do
  let rebuilt ← elabTermEnsuringType stx (← inferType expression)
  synthesizeSyntheticMVarsNoPostponing
  let rebuilt ← instantiateMVars rebuilt
  if rebuilt.hasMVar || rebuilt.hasSorry then
    throwError "presentation replay contains an incomplete term"
  unless ← isDefEq expression rebuilt do
    throwError "presentation replay changed its original expression"

private def check (term : TSyntax `term) (required : Array String)
    (forbidden : Array String := #[]) (readableReplay : Bool := false) : TermElabM Unit := do
  let expression ← elaborate term
  let (stx, text) ← render expression
  for fragment in required do
    unless text.contains fragment do
      throwError "presentation lost {fragment}: {text}"
  for fragment in forbidden do
    if text.contains fragment then
      throwError "presentation unexpectedly contains {fragment}: {text}"
  if readableReplay then checkReplay expression stx
  checkReplay expression (← render expression true).1

run_cmd liftTermElabM do
  check (← `(Fin (3 - 1))) #["Fin 2"] #[] true
  check (← `((⟨0, by decide⟩ : Fin 3))) #["0"] #["⟨"] true
  check (← `(fun j : Fin 2 => ((j.val : ℝ)))) #["j.val : ℝ"] #[] true
  -- None of the new presentation hooks may affect ordinary delaboration.
  let finiteType ← elaborate (← `(Fin (3 - 1)))
  let finiteIndex ← elaborate (← `((⟨0, by decide⟩ : Fin 3)))
  let cast ← elaborate (← `(fun j : Fin 2 => ((j.val : ℝ))))
  for (expression, marker) in #[(finiteType, "3 - 1"), (finiteIndex, "⟨"), (cast, "↑")] do
    let stx ← PrettyPrinter.delab expression
    let text := (← PrettyPrinter.ppTerm stx).pretty
    unless text.contains marker do
      throwError "ordinary pretty-printing unexpectedly used presentation cleanup: {text}"

def namedDimension : Nat := 3
def namedIndex : Nat := 1

run_cmd liftTermElabM do
  check (← `(Fin (namedDimension - 1))) #["namedDimension"] #["Fin 2"] true
  check (← `((⟨namedIndex, by decide⟩ : Fin 3))) #["namedIndex", "⟨"]
  check (← `((⟨0, by decide⟩ : Fin namedDimension))) #["⟨"]
  -- A constructor is not a modulo numeral, even in an inconsistent context.
  check (← `(fun h : False => (⟨3, False.elim h⟩ : Fin 2))) #["⟨3"]

@[instance_reducible] private def additionAsSubtraction : HSub Nat Nat Nat := ⟨Nat.add⟩
@[instance_reducible] private def subtractionAsAddition : HAdd Nat Nat Nat := ⟨Nat.sub⟩

run_cmd liftTermElabM do
  -- The wrong operation agrees at these operands; full-value equality alone
  -- must not authorize cleanup of its operation prefix.
  check (← `(Fin (@HSub.hSub Nat Nat Nat additionAsSubtraction 3 0)))
    #["additionAsSubtraction"] #["Fin 3"] true
  check (← `(Fin (@HAdd.hAdd Nat Nat Nat subtractionAsAddition 3 0)))
    #["3 + 0"] #["Fin 3"]

section AlteredNatNumeral
local instance : OfNat Nat 2 := ⟨3⟩

run_cmd liftTermElabM do
  -- The source uses native 3 and 1, but a freshly printed 2 would mean 3.
  check (← `(Fin (3 - 1))) #["3 - 1"] #["Fin 2"] true
end AlteredNatNumeral

section AlteredFinNumeral
local instance : OfNat (Fin 3) 0 := ⟨⟨1, by decide⟩⟩

run_cmd liftTermElabM do
  check (← `((⟨0, by decide⟩ : Fin 3))) #["⟨0"]
end AlteredFinNumeral

section AlteredNatCast
noncomputable local instance : NatCast ℝ := ⟨fun n => @Nat.cast ℝ Real.instNatCast n + 1⟩

run_cmd liftTermElabM do
  check (← `(fun j : Fin 2 => @Nat.cast ℝ Real.instNatCast j.val))
    #["↑"] #["j.val : ℝ"]
  check (← `(fun j : Fin 2 => ((j.val : ℝ)))) #["↑"] #["j.val : ℝ"]
end AlteredNatCast

section AlteredCoercion
noncomputable local instance : CoeHTCT Nat ℝ :=
  ⟨fun n => if n = 0 then 0 else @Nat.cast ℝ Real.instNatCast n + 1⟩

run_cmd liftTermElabM do
  -- Agreement at zero cannot justify replacing the original cast by a fresh
  -- coercion. The implementation must compare them on a fresh natural.
  check (← `(@Nat.cast ℝ Real.instNatCast (Fin.val (⟨0, by decide⟩ : Fin 2))))
    #["↑"] #[".val : ℝ"]
end AlteredCoercion

end MorewTest.Reformulation.PresentationIndices
