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

private def checkUntypedReplay (term : TSyntax `term) : TermElabM Unit := do
  let expression ← elaborate term
  for replay in #[false, true] do
    let (stx, _) ← render expression replay
    -- Supplying the original type would hide a missing Fin ascription on an
    -- arithmetic expression by preventing numeral defaulting to Nat.
    let rebuilt ← elaborate ⟨stx⟩
    unless ← isDefEq (← inferType expression) (← inferType rebuilt) do
      throwError "untyped presentation replay changed its original type"
    unless ← isDefEq expression rebuilt do
      throwError "untyped presentation replay changed its original expression"

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
  check (← `(Fin (3 - 1))) #["Fin (3 - 1)"] #["Fin 2"] true
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

run_cmd liftTermElabM do
  checkUntypedReplay (← `((⟨0, by decide⟩ : Fin 3) = (⟨1, by decide⟩ : Fin 3)))
  checkUntypedReplay (← `((⟨2, by decide⟩ : Fin 3) + (⟨2, by decide⟩ : Fin 3)))
  checkUntypedReplay (← `((⟨2, by decide⟩ : Fin 3) + (⟨2, by decide⟩ : Fin 3) =
    (⟨1, by decide⟩ : Fin 3)))
  checkUntypedReplay (← `(((⟨2, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3))))
  checkUntypedReplay (← `((fun p : Fin 3 => p + p = 1)
    (⟨2, by decide⟩ : Fin 3)))
  checkUntypedReplay (← `((fun p : Fin 3 × Fin 3 => p.1 + p.2 = 1)
    ((⟨2, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3))))
  check (← `((fun p : Fin 3 => p + p = 1) (⟨2, by decide⟩ : Fin 3)))
    #["(2 : Fin 3)"] #[] true
  check (← `((fun p : Fin 3 × Fin 3 => p.1 + p.2 = 1)
    ((⟨2, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3))))
    #["((2 : Fin 3), (2 : Fin 3))"] #[] true
  -- A surrounding lambda's binder annotation may disappear during printing.
  -- Its argument still needs a Fin ascription when replay has no expected type.
  check (← `(fun u : Fin 3 → ℝ => u (⟨0, by decide⟩ : Fin 3)))
    #["(0 : Fin 3)"] #["u 0"] true
  -- An external function's fixed explicit domain supplies the index type,
  -- both in a direct application and under a polymorphic equality.
  withLocalDeclD `u (← elaborate (← `(Fin 3 → ℝ))) fun u => do
    let application := mkApp u (← elaborate (← `((⟨0, by decide⟩ : Fin 3))))
    for expression in #[application, ← mkEq application application] do
      let (stx, text) ← render expression
      unless text.contains "u 0" && !text.contains "(0 : Fin 3)" do
        throwError "fixed-domain finite application lost compact printing: {text}"
      checkReplay expression stx
      checkReplay expression (← render expression true).1
  withOptions (·.setBool `pp.analyze true |>.setBool `pp.analyze.knowsType false) do
    -- The Fin cleanup must also preserve analyzer annotations on other terms.
    check (← `(fun x : ℝ => ((⟨0, by decide⟩ : Fin 3), x))) #["x : ℝ"] #[] true
    checkUntypedReplay (← `((⟨2, by decide⟩ : Fin 3) + (⟨2, by decide⟩ : Fin 3)))

namespace RetainedFiniteArithmetic

open Morew

noncomputable section

def source :=
  problem (x : ℝ)
    minimize x
    subject to
      retained : (⟨2, by decide⟩ : Fin 3) + (⟨2, by decide⟩ : Fin 3) =
        (⟨1, by decide⟩ : Fin 3)
      bound : |x| ≤ 1

reformulation targeted : source := by
  conic at bound

/--
info: problem (x : ℝ)
  minimize x
  subject to
    retained : (2 : Fin 3) + (2 : Fin 3) = (1 : Fin 3)
    bound_conic_1 : x ≤ 1
    bound_conic_2 : -x ≤ 1
-/
#guard_msgs in
#printp targeted

run_cmd do
  let some display := Morew.Syntax.getProblemDisplayView? (← getEnv) ``targeted
    | throwError "missing finite arithmetic display presentation"
  let some exact := Morew.Syntax.getProblemView? (← getEnv) ``targeted
    | throwError "missing finite arithmetic exact presentation"
  for (view, name) in #[(display, `displayReplay), (exact, `exactReplay)] do
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(def $(mkIdent name) := $term))

example : displayReplay = targeted := rfl
example : exactReplay = targeted := rfl
example : targeted.feasible 0 := by norm_num [targeted]; decide
example : displayReplay.feasible 0 := by norm_num [displayReplay]; decide
example : exactReplay.feasible 0 := by norm_num [exactReplay]; decide

end

end RetainedFiniteArithmetic

namespace RetainedFiniteTuple

open Morew

noncomputable section

def source :=
  problem (x : ℝ)
    minimize x
    subject to
      retained : (fun p : Fin 3 × Fin 3 => p.1 + p.2 = 1)
        ((⟨2, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3))
      bound : |x| ≤ 1

reformulation targeted : source := by
  conic at bound

/--
info: problem (x : ℝ)
  minimize x
  subject to
    retained : (fun p => p.1 + p.2 = 1) ((2 : Fin 3), (2 : Fin 3))
    bound_conic_1 : x ≤ 1
    bound_conic_2 : -x ≤ 1
-/
#guard_msgs in
#printp targeted

run_cmd do
  let some display := Morew.Syntax.getProblemDisplayView? (← getEnv) ``targeted
    | throwError "missing finite tuple display presentation"
  let some exact := Morew.Syntax.getProblemView? (← getEnv) ``targeted
    | throwError "missing finite tuple exact presentation"
  for (view, name) in #[(display, `displayReplay), (exact, `exactReplay)] do
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(def $(mkIdent name) := $term))

example : displayReplay = targeted := rfl
example : exactReplay = targeted := rfl
example : targeted.feasible 0 := by norm_num [targeted]; decide
example : displayReplay.feasible 0 := by norm_num [displayReplay]; decide
example : exactReplay.feasible 0 := by norm_num [exactReplay]; decide

end

end RetainedFiniteTuple

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

namespace AlteredNormalizedFinNumeral

open Morew
noncomputable section

local instance alteredFinZero : OfNat (Fin 2) 0 := ⟨⟨1, by decide⟩⟩

run_cmd liftTermElabM do
  -- Instance lookup on the original `Fin (3 - 1)` does not necessarily find
  -- an instance keyed by `Fin 2`. Retaining the original dimension in the
  -- displayed type keeps native constructors and existing numerals unchanged.
  withOptions (·.setBool `pp.proofs true |>.setBool `pp.structureInstanceTypes true) do
    checkUntypedReplay (← `((⟨0, by decide⟩ : Fin (3 - 1))))
    checkUntypedReplay (← `((⟨0, by decide⟩ : Fin (1 + 1))))
    checkUntypedReplay (← `((⟨0, by decide⟩ : Fin (Nat.succ 1))))
  withOptions (·.setBool `pp.numericTypes true) do
    checkUntypedReplay (← `((0 : Fin (3 - 1))))

def source :=
  problem (x : ℝ)
    minimize x
    subject to
      retained : (⟨0, by decide⟩ : Fin (3 - 1)).val = 0
      bound : |x| ≤ 1

-- Keep the original constructor proof replayable if a custom numeral prevents
-- cleanup. The new numeric spelling must not turn the retained row into 1 = 0.
set_option pp.proofs true in
set_option pp.structureInstanceTypes true in
reformulation targeted : source := by conic at bound

run_cmd do
  let some display := Morew.Syntax.getProblemDisplayView? (← getEnv) ``targeted
    | throwError "missing normalized finite numeral display presentation"
  let some exact := Morew.Syntax.getProblemView? (← getEnv) ``targeted
    | throwError "missing normalized finite numeral exact presentation"
  for (view, name) in #[(display, `displayReplay), (exact, `exactReplay)] do
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(def $(mkIdent name) := $term))

example : displayReplay = targeted := rfl
example : exactReplay = targeted := rfl
example : targeted.feasible 0 := by norm_num [targeted]
example : displayReplay.feasible 0 := by
  change (0 : Nat) = 0 ∧ (0 : ℝ) ≤ 1 ∧ -(0 : ℝ) ≤ 1
  norm_num

def numeralSource :=
  problem (x : ℝ)
    let i : Fin (3 - 1) := 0
    minimize x
    subject to
      retained : i.val = 0
      bound : |x| ≤ 1

reformulation numeralTargeted : numeralSource := by conic at bound

run_cmd do
  let some display := Morew.Syntax.getProblemDisplayView? (← getEnv) ``numeralTargeted
    | throwError "missing finite numeral definition display presentation"
  let some exact := Morew.Syntax.getProblemView? (← getEnv) ``numeralTargeted
    | throwError "missing finite numeral definition exact presentation"
  for (view, name) in #[(display, `numeralDisplayReplay), (exact, `numeralExactReplay)] do
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(def $(mkIdent name) := $term))

example : numeralDisplayReplay = numeralTargeted := rfl
example : numeralExactReplay = numeralTargeted := rfl
example : numeralTargeted.feasible 0 := by norm_num [numeralTargeted]
example : numeralDisplayReplay.feasible 0 := by
  change (0 : Nat) = 0 ∧ (0 : ℝ) ≤ 1 ∧ -(0 : ℝ) ≤ 1
  norm_num

end
end AlteredNormalizedFinNumeral

namespace AlteredNormalizedFinAddition

open Morew
noncomputable section

local instance : Add (Fin 2) := ⟨fun _ _ => ⟨1, by decide⟩⟩

def source :=
  problem (x : ℝ)
    let f : Fin (3 - 1) → Fin (3 - 1) := fun i => i + i
    minimize x
    subject to
      retained : (f 0).val = 0
      bound : |x| ≤ 1

reformulation targeted : source := by conic at bound

run_cmd do
  let some display := Morew.Syntax.getProblemDisplayView? (← getEnv) ``targeted
    | throwError "missing finite addition definition display presentation"
  let some exact := Morew.Syntax.getProblemView? (← getEnv) ``targeted
    | throwError "missing finite addition definition exact presentation"
  for (view, name) in #[(display, `displayReplay), (exact, `exactReplay)] do
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(def $(mkIdent name) := $term))

example : displayReplay = targeted := rfl
example : exactReplay = targeted := rfl
example : targeted.feasible 0 := by norm_num [targeted]
example : displayReplay.feasible 0 := by
  change (0 : Nat) = 0 ∧ (0 : ℝ) ≤ 1 ∧ -(0 : ℝ) ≤ 1
  norm_num

end
end AlteredNormalizedFinAddition

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
    #["@Nat.cast", "Real.instNatCast"] #[".val : ℝ"] true
end AlteredCoercion

section AlteredDependentCoercionNumeral
noncomputable local instance (priority := high) : CoeDep Nat (0 : Fin 2).val ℝ := ⟨7⟩

run_cmd liftTermElabM do
  -- This instance matches the displayed numeral, but neither a fresh natural
  -- nor the original constructor operand. The native cast must still mean zero.
  check (← `(@Nat.cast ℝ Real.instNatCast (Fin.val (⟨0, by decide⟩ : Fin 2))))
    #[] #[] true
end AlteredDependentCoercionNumeral

namespace AlteredDependentCoercionIndex

open Morew
noncomputable section

local instance (priority := high) (j : Fin 2) : CoeDep Nat j.val ℝ := ⟨7⟩

run_cmd liftTermElabM do
  -- A coercion depending on a finite index also escapes the fresh-Nat check
  -- when the index is bound inside the displayed lambda.
  check (← `(fun j : Fin 2 => @Nat.cast ℝ Real.instNatCast j.val)) #[] #[] true

def source (i : Fin 2) :=
  problem (x : ℝ)
    minimize x
    subject to
      retained : @Nat.cast ℝ Real.instNatCast i.val ≤ x
      bound : |x| ≤ 10

variable (i : Fin 2)

reformulation targeted : (source i) := by conic at bound

run_cmd do
  let some display := Morew.Syntax.getProblemDisplayView? (← getEnv) ``targeted
    | throwError "missing dependent-coercion display presentation"
  let some exact := Morew.Syntax.getProblemView? (← getEnv) ``targeted
    | throwError "missing dependent-coercion exact presentation"
  for (view, name) in #[(display, `displayReplay), (exact, `exactReplay)] do
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(def $(mkIdent name) := $term))

-- Replacing the native cast by the dependent coercion changes the retained row
-- to `7 ≤ x` and removes the replayed declaration's dependence on `i`.
example : displayReplay i = targeted i := rfl
example : exactReplay i = targeted i := rfl
example : (displayReplay 0).feasible 0 := by norm_num [displayReplay]

end
end AlteredDependentCoercionIndex

end MorewTest.Reformulation.PresentationIndices
