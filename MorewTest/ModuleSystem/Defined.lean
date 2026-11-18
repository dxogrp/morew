/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Conic

/-! Producers with native private, public opaque, and exposed declarations. -/

namespace MorewTest.ModuleSystem

open Morew
noncomputable section

def privateSource := problem (x : ℝ) minimize x subject to lower : 0 ≤ x

reformulation privateTarget : privateSource certificate privateCertificate := by
  conic

example : GlobalEquiv privateSource privateTarget := privateCertificate
example : Conic.Form privateTarget := privateTarget.conicForm
example : IsConic privateTarget := privateTarget.isConic

run_cmd do
  for name in #[``privateSource, ``privateTarget, ``privateTarget.equiv,
      ``privateTarget.conicForm, ``privateTarget.isConic, ``privateCertificate] do
    unless Lean.isPrivateName name do
      Lean.throwError m!"a default-private command exported {name}"
  unless (Syntax.getProblemView? (← Lean.getEnv) ``privateTarget).isSome do
    Lean.throwError "a private target lost its local presentation"

/-- Exact native names used to test the import boundary. -/
public meta def privateDeclarations : Array Lean.Name :=
  #[``privateSource, ``privateTarget, ``privateTarget.equiv,
    ``privateTarget.conicForm, ``privateTarget.isConic, ``privateCertificate]

public section

opaque printable : Problem Nat Nat :=
  problem (x : Nat) minimize x + 1 subject to upper : x ≤ 7

def opaqueNorm :=
  letI : Norm ℝ := ⟨fun _ => 7⟩
  problem (x : ℝ) minimize ‖x‖

def opaqueSource := problem (x : ℝ) minimize x subject to lower : 0 ≤ x

reformulation opaqueTarget : opaqueSource certificate opaqueCertificate := by
  conic

end

@[expose] public section

-- Local source bodies remain available for planning an exposed reformulation.
reformulation exposedFromOpaque : opaqueSource certificate exposedFromOpaqueCertificate := by
  rename lower to nonnegative
  conic

def exposedSource (offset : ℝ) := problem (x : ℝ) minimize |x - offset|

def normSource (offset : ℝ) :=
  letI : Norm ℝ := ⟨fun _ => offset⟩
  problem (x : ℝ) minimize ‖x‖

variable (offset : ℝ)

reformulation exposedTarget : (exposedSource offset) certificate exposedCertificate := by
  epigraph bound as objectiveBound
  conic

example (point : FeasiblePoint (exposedSource offset)) :
    ((exposedTarget.equiv offset).forward.map point).val =
      (point.val, |point.val - offset|) := rfl

example (point : FeasiblePoint (exposedTarget offset)) :
    ((exposedTarget.equiv offset).backward.map point).val = point.val.1 := rfl

end
end
end MorewTest.ModuleSystem
