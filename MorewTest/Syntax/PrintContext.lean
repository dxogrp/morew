/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import Morew.Reformulation.Conic
import MorewTest.Syntax.PrintContextSource

/-!
# Reformulation printing after its elaboration scope changes

Cached displays must resolve to the checked problem in the scope of each `#printp`.
Printing preserves the reconstruction registry and compact proof policy.
-/

namespace MorewTest.Syntax.PrintContext

open Morew
open MorewTest.Syntax.PrintContextSupport

noncomputable section

namespace Shadowing

open Real

def source (a : ℝ) :=
  problem (x : ℝ)
    let cost := exp x
    minimize cost + a

section

variable (a : ℝ)

reformulation target : (source a) := by
  epigraph t

example : GlobalEquiv (source a) (target a) := target.equiv a

end

def mixed :=
  problem (x : ℝ)
    minimize (let exp := fun y : ℝ => y + 2; exp x) + exp x

reformulation mixedTarget : mixed := by
  epigraph t

def exp (x : ℝ) : ℝ := x + 37

example (a x t : ℝ) : (target a).feasible (x, t) ↔ Real.exp x + a ≤ t := Iff.rfl
example (x t : ℝ) : mixedTarget.feasible (x, t) ↔
    (x + 2) + Real.exp x ≤ t := Iff.rfl
example : GlobalEquiv mixed mixedTarget := mixedTarget.equiv

run_cmd do
  for proofs in #[false, true] do
    for declaration in #[``source, ``target] do
      discard <| checkPrinted declaration proofs
    for declaration in #[``mixed, ``mixedTarget] do
      discard <| checkPrinted declaration proofs (some `exp)

end Shadowing

namespace LocalNotation

section

local notation "growth" => Real.exp

def source (a : ℝ) :=
  problem (x : ℝ)
    let cost := growth x
    minimize cost + a

variable (a : ℝ)

reformulation target : (source a) := by
  epigraph t

example : GlobalEquiv (source a) (target a) := target.equiv a

end

run_cmd do
  for declaration in #[``source, ``target] do
    for proofs in #[false, true] do
      let printed ← checkPrinted declaration proofs
      if printed.contains "growth" then
        Lean.throwError "printing retained notation whose section has closed"

end LocalNotation

namespace ClosedNamespace

open Real

def source (n : Nat) (a : ℝ) :=
  problem (x : ℝ) (v : Fin n → ℝ)
    minimize exp x + a
    subject to bound : ∀ i, v i ≤ x

variable (n : Nat) (a : ℝ)

reformulation target : (source n a) := by
  epigraph t

example : GlobalEquiv (source n a) (target n a) := target.equiv n a

end ClosedNamespace

run_cmd do
  for declaration in #[``ClosedNamespace.source, ``ClosedNamespace.target] do
    for proofs in #[false, true] do
      discard <| checkPrinted declaration proofs

namespace ProofDetails

open Real

theorem indexBound : 0 < 2 := by decide

def source :=
  problem (x : ℝ) (v : Fin 2 → ℝ)
    let cost := exp x + v ⟨0, indexBound⟩
    minimize cost

reformulation target : source := by
  epigraph t

def exp (x : ℝ) : ℝ := x + 37

example : GlobalEquiv source target := target.equiv
example (x t : ℝ) (v : Fin 2 → ℝ) : target.feasible ((x, v), t) ↔
    Real.exp x + v ⟨0, indexBound⟩ ≤ t := Iff.rfl

run_cmd do
  let compact ← rawPrinted ``target false
  let detailed ← checkPrinted ``target true
  let compactAgain ← rawPrinted ``target false
  unless compact == compactAgain do
    Lean.throwError "detailed printing changed the next compact presentation"
  unless compact.contains "⋯" && !compact.contains "indexBound" do
    Lean.throwError m!"scope repair exposed compact finite-index proofs: {compact}"
  unless detailed.contains "indexBound" && !detailed.contains "⋯" do
    Lean.throwError m!"scope repair lost detailed finite-index proofs: {detailed}"

end ProofDetails

end
end MorewTest.Syntax.PrintContext
