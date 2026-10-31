/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.EuclideanPrinting

/-! # Euclidean coordinate printing after import and continued reformulation. -/

namespace MorewTest.ImportCompatibility.EuclideanPrinting

open Morew
open MorewTest.Reformulation.EuclideanPrinting
  (source target registeredDetailed checkReadable checkStoredProjections replayStored)

noncomputable section

reformulation continued : target := by nlp

run_cmd do
  for declaration in #[``target, ``registeredDetailed, ``continued] do
    checkReadable declaration
    checkStoredProjections declaration

example : GlobalEquivalence source continued :=
  target.equivalence.trans continued.equivalence
example : IsSmoothNLP continued := continued.isSmoothNLP

namespace AlteredCoercion

local instance (priority := high) :
    CoeFun (EuclideanSpace ℝ (Fin 2)) (fun _ => Fin 2 → ℝ) :=
  ⟨fun x i => x.ofLp i + 11⟩

example (x : EuclideanSpace ℝ (Fin 2)) : x 0 = x.ofLp 0 + 11 := rfl

run_cmd do
  -- Stored print syntax keeps the producer's notation, while both replay
  -- views must retain the checked coordinate function under consumer instances.
  checkReadable ``target
  checkReadable ``continued
  replayStored ``target `importedExactReplay `importedDisplayReplay
  replayStored ``continued `continuedExactReplay `continuedDisplayReplay

example : importedExactReplay = target := rfl
example : importedDisplayReplay = target := rfl
example : continuedExactReplay = continued := rfl
example : continuedDisplayReplay = continued := rfl

end AlteredCoercion

end
end MorewTest.ImportCompatibility.EuclideanPrinting
