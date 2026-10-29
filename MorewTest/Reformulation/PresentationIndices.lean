/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Finite-index presentation boundaries

Preserve constructor and dimension syntax, and replay its meaning even when
numerals, arithmetic, coercions, or dependent types have specialized instances.
-/

namespace MorewTest.Reformulation.PresentationIndices

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Reformulation.Internal

private def elaborate (term : TSyntax `term) (expectedType? : Option Expr := none) :
    TermElabM Expr := do
  let expression ← elabTerm term expectedType?
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasSorry then
    throwError "presentation test contains an incomplete term"
  return expression

private def checkReplay (term : TSyntax `term) (required : Array String := #[]) :
    TermElabM Unit := do
  let expression ← elaborate term
  -- Complete ordinary printing supplies the proofs and types needed to replay
  -- readable constructors; generic presentation does not abbreviate them.
  withOptions (·.setBool `pp.proofs true |>.setBool `pp.structureInstanceTypes true
      |>.setBool `pp.funBinderTypes true) do
    for replay in #[false, true] do
      let stx ← delabPresentationTerm expression #[] replay
      if !replay then
        let text := (← PrettyPrinter.ppTerm ⟨stx⟩).pretty
        for fragment in required do
          unless text.contains fragment do
            throwError "presentation lost {fragment}: {text}"
      let rebuilt ← elaborate ⟨stx⟩ (some (← inferType expression))
      unless ← isDefEq expression rebuilt do
        throwError "presentation replay changed its original expression"

private def replayStored (declaration displayName exactName : Name) : CommandElabM Unit := do
  let some display := Morew.Syntax.getProblemDisplayView? (← getEnv) declaration
    | throwError "missing finite-index display presentation"
  let some exact := Morew.Syntax.getProblemView? (← getEnv) declaration
    | throwError "missing finite-index exact presentation"
  for (view, name) in #[(display, displayName), (exact, exactName)] do
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(def $(mkIdent name) := $term))

def namedDimension : Nat := 3
def namedIndex : Nat := 1

run_cmd liftTermElabM do
  checkReplay (← `(Fin (3 - 1))) #["3 - 1"]
  checkReplay (← `((⟨0, by decide⟩ : Fin 3))) #["⟨"]
  checkReplay (← `(Fin (namedDimension - 1))) #["namedDimension"]
  checkReplay (← `((⟨namedIndex, by decide⟩ : Fin 3))) #["namedIndex", "⟨"]
  -- A constructor is not a modulo numeral, even in an inconsistent context.
  checkReplay (← `(fun h : False => (⟨3, False.elim h⟩ : Fin 2))) #["⟨"]

section AlteredNumerals
local instance : OfNat Nat 2 := ⟨3⟩
local instance : OfNat (Fin 3) 0 := ⟨⟨1, by decide⟩⟩

run_cmd liftTermElabM do
  checkReplay (← `(Fin (3 - 1))) #["3 - 1"]
  checkReplay (← `((⟨0, by decide⟩ : Fin 3))) #["⟨"]
end AlteredNumerals

section AlteredFiniteInstances
local instance : OfNat (Fin 2) 0 := ⟨⟨1, by decide⟩⟩
local instance : Add (Fin 2) := ⟨fun _ _ => ⟨1, by decide⟩⟩

run_cmd liftTermElabM do
  -- Definitionally equal dimensions may select different instance entries.
  checkReplay (← `((⟨0, by decide⟩ : Fin (3 - 1)))) #["3 - 1", "⟨"]
  checkReplay (← `(fun i : Fin (3 - 1) => i + i)) #["3 - 1"]
  -- Replacing either constructor by castSucc/succ can change the Add instance.
  checkReplay (← `(fun j : Fin 1 =>
    (⟨j.val, by omega⟩ : Fin 2) + (⟨j.val, by omega⟩ : Fin 2)))
  checkReplay (← `(fun j : Fin 1 =>
    (⟨j.val + 1, by omega⟩ : Fin 2) + (⟨j.val + 1, by omega⟩ : Fin 2)))
end AlteredFiniteInstances

namespace DependentTypes
noncomputable section

structure Indexed (i : Fin 2) where
  value : Nat

local instance (i : Fin 2) : Add (Indexed i) := ⟨fun _ _ => ⟨0⟩⟩
local instance (priority := high) : Add (Indexed (⟨0, Nat.zero_lt_two⟩ : Fin 2)) :=
  ⟨fun _ _ => ⟨1⟩⟩

run_cmd liftTermElabM do
  -- A numeral's Fin type alone does not preserve dependent instance lookup.
  checkReplay (← `(fun u : ((i : Fin 2) → Indexed i) =>
    (u (⟨0, Nat.zero_lt_two⟩ : Fin 2) + u (⟨0, Nat.zero_lt_two⟩ : Fin 2)).value))
  checkReplay (← `(let index : Fin 2 := ⟨0, Nat.zero_lt_two⟩
    let entry : Indexed index := ⟨0⟩
    (entry + entry).value))

def source (u : (i : Fin 2) → Indexed i) :=
  problem (x : ℝ)
    let entry : Indexed (⟨0, Nat.zero_lt_two⟩ : Fin 2) := ⟨0⟩
    minimize x
    subject to
      retained : (u (⟨0, Nat.zero_lt_two⟩ : Fin 2) +
        u (⟨0, Nat.zero_lt_two⟩ : Fin 2)).value = 1
      retainedType : (entry + entry).value = 1
      bound : |x| ≤ 1

variable (u : (i : Fin 2) → Indexed i)

set_option pp.proofs true in
set_option pp.structureInstanceTypes true in
reformulation targeted : (source u) := by conic at bound

run_cmd replayStored ``targeted `displayReplay `exactReplay

example : displayReplay u = targeted u := rfl
example : exactReplay u = targeted u := rfl
example : (targeted u).feasible 0 := by
  change (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧ (0 : ℝ) ≤ 1 ∧ -(0 : ℝ) ≤ 1
  norm_num
example : (displayReplay u).feasible 0 := by
  change (1 : Nat) = 1 ∧ (1 : Nat) = 1 ∧ (0 : ℝ) ≤ 1 ∧ -(0 : ℝ) ≤ 1
  norm_num

end
end DependentTypes

namespace DependentCoercions
noncomputable section

local instance (priority := high) (j : Fin 2) : CoeDep Nat j.val ℝ := ⟨7⟩

-- Ordinary coercion notation can itself resynthesize CoeDep; retain the
-- explicit cast when testing readable replay under these altered instances.
set_option pp.coercions false

run_cmd liftTermElabM do
  -- Replacing the native cast by a fresh dependent coercion would produce 7.
  checkReplay (← `(fun j : Fin 2 => @Nat.cast ℝ Real.instNatCast j.val))
  checkReplay (← `(@Nat.cast ℝ Real.instNatCast (Fin.val (⟨0, by decide⟩ : Fin 2))))

def source (i : Fin 2) :=
  problem (x : ℝ)
    minimize x
    subject to
      retained : @Nat.cast ℝ Real.instNatCast i.val ≤ x
      bound : |x| ≤ 10

variable (i : Fin 2)

reformulation targeted : (source i) := by conic at bound

run_cmd replayStored ``targeted `displayReplay `exactReplay

example : displayReplay i = targeted i := rfl
example : exactReplay i = targeted i := rfl
example : (targeted 0).feasible 0 := by norm_num [targeted]
example : (displayReplay 0).feasible 0 := by norm_num [displayReplay]

end
end DependentCoercions

end MorewTest.Reformulation.PresentationIndices
