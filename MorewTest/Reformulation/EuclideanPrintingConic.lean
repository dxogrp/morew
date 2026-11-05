/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.EuclideanPrintingSupport

/-!
# Euclidean coordinates in generated conic problem presentations

Scalar coordinate shorthand and the unapplied SOC vector projection must retain
their meaning in both stored views, including under a conflicting coercion.
-/

namespace MorewTest.Reformulation.EuclideanPrintingConic

open Lean Lean.Elab.Command Morew
open MorewTest.Reformulation.PrintDetails (printed)
open MorewTest.Reformulation.EuclideanPrintingSupport (checkStoredProjections replayStored)

/-- Scalar coordinates are readable while the cone's full vector remains explicit. -/
def checkReadable (declaration : Name) : CommandElabM Unit := do
  let compact ← printed declaration false
  let detailed ← printed declaration true
  unless compact == (← printed declaration false) do
    throwError "detailed Euclidean printing changed subsequent compact output"
  for output in #[compact, detailed] do
    for fragment in #["EuclideanSpace ℝ (Fin 2)", "maximize t",
        "balance : x 0 + x 1 - 1", "hypograph_t_conic_1 : (-t, x.ofLp) ∈ SOC 2"] do
      unless output.contains fragment do
        throwError "readable Euclidean conic printing changed {fragment}: {output}"

noncomputable section

def source :=
  problem (x : EuclideanSpace ℝ (Fin 2))
    maximize -‖x‖
    subject to balance : x 0 + x 1 = 1

reformulation target : source := by
  hypograph t
  conic

set_option pp.proofs true in
reformulation registeredDetailed : source := by
  hypograph t
  conic

run_cmd do
  for declaration in #[``target, ``registeredDetailed] do
    checkReadable declaration
    checkStoredProjections declaration
  for proofs in #[false, true] do
    unless (← printed ``target proofs) == (← printed ``registeredDetailed proofs) do
      throwError "registration-time proof options changed Euclidean conic printing"

run_cmd replayStored ``target `exactReplay `displayReplay

example : exactReplay = target := rfl
example : displayReplay = target := rfl
example : GlobalEquiv source target := target.equiv
example : IsConic target := target.isConic

namespace AlteredCoercion

local instance (priority := high) :
    CoeFun (EuclideanSpace ℝ (Fin 2)) (fun _ => Fin 2 → ℝ) :=
  ⟨fun x i => x.ofLp i + 7⟩

example (x : EuclideanSpace ℝ (Fin 2)) : x 0 = x.ofLp 0 + 7 := rfl

run_cmd replayStored ``target `exactReplay `displayReplay

example : exactReplay = target := rfl
example : displayReplay = target := rfl

-- New printed representations cannot use coordinate shorthand with the caller's
-- conflicting coercion; the previously stored representation remains unchanged.
reformulation guarded : target := by conic

run_cmd do
  checkReadable ``target
  for proofs in #[false, true] do
    let output ← printed ``guarded proofs
    unless output.contains "balance : x.ofLp 0 + x.ofLp 1 - 1" &&
        output.contains "hypograph_t_conic_1 : (-t, x.ofLp) ∈ SOC 2" do
      throwError "Euclidean conic printing ignored a conflicting function coercion: {output}"

example : guarded = target := rfl
example : IsConic guarded := guarded.isConic

end AlteredCoercion

end
end MorewTest.Reformulation.EuclideanPrintingConic
