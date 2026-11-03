/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.EuclideanPrintingConic
import MorewTest.Reformulation.EuclideanPrintingSupport

/-! # Euclidean conic coordinate printing after import and continued reformulation. -/

namespace MorewTest.ImportCompatibility.EuclideanPrintingConic

open Morew
open MorewTest.Reformulation.EuclideanPrintingConic
  (source target registeredDetailed checkReadable)
open MorewTest.Reformulation.EuclideanPrintingSupport
  (checkStoredProjections replayStored)
open MorewTest.Reformulation.PrintDetails (printed)

noncomputable section

reformulation continued : target := by conic

run_cmd do
  for declaration in #[``target, ``registeredDetailed, ``continued] do
    checkReadable declaration
    checkStoredProjections declaration

example : GlobalEquivalence source continued :=
  target.equivalence.trans continued.equivalence
example : IsConic continued := continued.isConic

namespace AlteredCoercion

local instance (priority := high) :
    CoeFun (EuclideanSpace ℝ (Fin 2)) (fun _ => Fin 2 → ℝ) :=
  ⟨fun x i => x.ofLp i + 11⟩

example (x : EuclideanSpace ℝ (Fin 2)) : x 0 = x.ofLp 0 + 11 := rfl

run_cmd do
  -- Producer print syntax remains readable; both replay views retain the
  -- canonical coordinate function despite the consumer's function coercion.
  checkReadable ``target
  checkReadable ``continued
  replayStored ``target `importedExactReplay `importedDisplayReplay
  replayStored ``continued `continuedExactReplay `continuedDisplayReplay

example : importedExactReplay = target := rfl
example : importedDisplayReplay = target := rfl
example : continuedExactReplay = continued := rfl
example : continuedDisplayReplay = continued := rfl

reformulation guarded : continued := by conic

run_cmd do
  checkStoredProjections ``guarded
  for proofs in #[false, true] do
    let output ← printed ``guarded proofs
    unless output.contains "balance : x.ofLp 0 + x.ofLp 1 - 1" &&
        output.contains "hypograph_t_conic_1 : (-t, x.ofLp) ∈ SOC 2" do
      Lean.throwError "imported conic printing ignored a conflicting function coercion: {output}"

example : guarded = continued := rfl
example : IsConic guarded := guarded.isConic

end AlteredCoercion

end
end MorewTest.ImportCompatibility.EuclideanPrintingConic
