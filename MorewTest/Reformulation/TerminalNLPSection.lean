/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.NLPImportedSource
import MorewTest.Reformulation.TerminalNLP

/-!
# Terminal smooth artifacts under parameters and imported presentation

Dependencies used only in proofs must survive emission; imported and applied
sources retain their exact local definitions and can be certified repeatedly.
-/

namespace MorewTest.Reformulation.TerminalNLPSection

open Morew
noncomputable section

-- Reuse an emitted target and its binding metadata after an actual module import.
reformulation importedCertified : TerminalNLP.localTarget := by
  epigraph t at first
  nlp
example : GlobalEquivalence TerminalNLP.localTarget importedCertified :=
  importedCertified.equivalence
example : NLP.Form importedCertified := importedCertified.nlpForm
example : importedCertified.nlpForm.data.toProblem = importedCertified :=
  importedCertified.nlpForm.represents

class Evidence where
  witness : True

opaque coefficient (_ : True) : ℝ := 7

section
variable [Evidence]

def objectiveSource :=
  problem (x : ℝ)
    minimize coefficient Evidence.witness + x ^ 2

reformulation objectiveTarget : objectiveSource := by
  nlp
example : GlobalEquivalence objectiveSource objectiveTarget := objectiveTarget.equivalence
example : NLP.Form objectiveTarget := objectiveTarget.nlpForm
example : IsSmoothNLP objectiveTarget := objectiveTarget.isSmoothNLP

def rowSource :=
  problem (x : ℝ)
    maximize x ^ 2
    subject to upper : x ≤ coefficient Evidence.witness

reformulation rowTarget : rowSource := by
  nlp
example : GlobalEquivalence rowSource rowTarget := rowTarget.equivalence
example : rowTarget.nlpForm.data.sense = .maximize := rfl
end

section
variable (radius : ℝ) (positive : 0 < radius)

reformulation importedTarget : (NLPImportedSource.family radius) := by
  nlp
example : GlobalEquivalence (NLPImportedSource.family radius) (importedTarget radius) :=
  importedTarget.equivalence radius
example : NLP.Form (importedTarget radius) := importedTarget.nlpForm radius positive

/--
info: problem (x : ℝ)
  let first := x ^ 2
  let second := x ^ 2
  minimize first + second
  subject to
    lower : radius ≤ x
    magnitude_nlp_1 : Real.log x ≤ 5
    magnitude_nlp_2 : -Real.log x ≤ 5
    untouched : first ≤ second + 1
-/
#guard_msgs in
#printp importedTarget

reformulation importedAgain : (importedTarget radius) := by
  nlp
example : GlobalEquivalence (importedTarget radius) (importedAgain radius) :=
  importedAgain.equivalence radius
example : NLP.Form (importedAgain radius) := importedAgain.nlpForm radius positive
end

section
variable (n : Nat)

def vectorSource :=
  problem (x : Fin n → ℝ)
    minimize ∑ i, (x i) ^ 2
    subject to
      coordinate : x ≤ fun _ => 3
      lower : ∀ i : Fin n, 0 ≤ x i

reformulation vectorTarget : (vectorSource n) := by
  nlp
example : (vectorTarget.nlpForm n).data.rowCount = n + n := by
  change (∑ _ : Fin n, (1 : ℕ)) + ((∑ _ : Fin n, (1 : ℕ)) + 0) = n + n
  simp
example : GlobalEquivalence (vectorSource n) (vectorTarget n) := vectorTarget.equivalence n
example : NLP.Form (vectorTarget n) := vectorTarget.nlpForm n
example : (vectorTarget.nlpForm 0).data.rowCount = 0 := rfl

reformulation zeroTarget : (vectorTarget 0) := by
  nlp
example : zeroTarget.nlpForm.data.rowCount = 0 := rfl
end

end
end MorewTest.Reformulation.TerminalNLPSection
