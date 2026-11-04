/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.NLP
import MorewTest.Reformulation.EuclideanPrintingSupport

/-!
# Euclidean coordinates in generated NLP problem presentations

Print-only coordinate notation must leave source spelling, unapplied projections,
and both stored reconstruction views intact.
-/

namespace MorewTest.Reformulation.EuclideanPrintingNLP

open Lean Lean.Elab.Command Morew
open MorewTest.Reformulation.PrintDetails (printed)
open MorewTest.Reformulation.EuclideanPrintingSupport (checkStoredProjections replayStored)

/-- Both print modes hide coordinate projections without changing the rows. -/
def checkReadable (declaration : Name) : CommandElabM Unit := do
  let compact ← printed declaration false
  let detailed ← printed declaration true
  unless compact == (← printed declaration false) do
    throwError "detailed Euclidean printing changed subsequent compact output"
  for output in #[compact, detailed] do
    if output.contains "ofLp" then
      throwError "generated Euclidean coordinates retained wrapper projections: {output}"
    for fragment in #["EuclideanSpace ℝ (Fin 2)", "maximize t",
        "balance : x 0 + x 1 = 1", "hypograph_t_nlp_1 : 0 ≤ -t",
        "hypograph_t_nlp_2 : ∑ i, x i ^ 2 ≤ (-t) ^ 2"] do
      unless output.contains fragment do
        throwError "readable Euclidean printing changed {fragment}: {output}"

noncomputable section

def source :=
  problem (x : EuclideanSpace ℝ (Fin 2))
    maximize -‖x‖
    subject to balance : x 0 + x 1 = 1

reformulation target : source := by
  hypograph t
  nlp

set_option pp.proofs true in
reformulation registeredDetailed : source := by
  hypograph t
  nlp

def explicitSource :=
  problem (x : EuclideanSpace ℝ (Fin 2))
    maximize -‖x‖
    subject to balance : x.ofLp 0 + x.ofLp 1 = 1

run_cmd do
  for declaration in #[``target, ``registeredDetailed] do
    checkReadable declaration
    checkStoredProjections declaration
  for proofs in #[false, true] do
    unless (← printed ``target proofs) == (← printed ``registeredDetailed proofs) do
      throwError "registration-time proof options changed Euclidean printing"
    unless (← printed ``explicitSource proofs).contains "x.ofLp 0 + x.ofLp 1 = 1" do
      throwError "Euclidean print cleanup changed explicit source spelling"

run_cmd replayStored ``target `exactReplay `displayReplay

example : exactReplay = target := rfl
example : displayReplay = target := rfl
example : GlobalEquivalence source target := target.equivalence
example : IsSmoothNLP target := target.isSmoothNLP

namespace AlteredCoercion

local instance (priority := high) :
    CoeFun (EuclideanSpace ℝ (Fin 2)) (fun _ => Fin 2 → ℝ) :=
  ⟨fun x i => x.ofLp i + 7⟩

example (x : EuclideanSpace ℝ (Fin 2)) : x 0 = x.ofLp 0 + 7 := rfl

run_cmd replayStored ``target `exactReplay `displayReplay

example : exactReplay = target := rfl
example : displayReplay = target := rfl

-- The new printed representation cannot use coordinate notation with the
-- currently selected, noncanonical function coercion.
reformulation guarded : target := by nlp

run_cmd do
  checkReadable ``target
  for proofs in #[false, true] do
    let output ← printed ``guarded proofs
    unless output.contains "x.ofLp 0" && output.contains "x.ofLp i" do
      throwError "Euclidean printing ignored a conflicting function coercion: {output}"

example : guarded = target := rfl

end AlteredCoercion

end
end MorewTest.Reformulation.EuclideanPrintingNLP
