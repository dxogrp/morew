/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics

/-!
# Direct certification of reducible surface operations

Constructor-backed operations can expose complete affine or smooth expressions.
Unsuccessful reductions must retain their instances for registered matching.
-/

namespace MorewTest.Reformulation.DirectNormalization

open Morew
noncomputable section

def affineObjective :=
  problem (x : ℝ)
    minimize @Neg.neg ℝ ⟨fun x => x⟩ x
    subject to lower : 0 ≤ x

reformulation affineConic : affineObjective := by conic
reformulation affineNLP : affineObjective := by nlp

example : GlobalEquivalence affineObjective affineConic := affineConic.equivalence
example : GlobalEquivalence affineObjective affineNLP := affineNLP.equivalence
example : affineConic.conicForm.data.toProblem = affineConic := affineConic.conicForm.represents
example : affineNLP.nlpForm.data.toProblem = affineNLP := affineNLP.nlpForm.represents
example (x : ℝ) : affineConic.objective x = x := rfl
example (x : ℝ) : affineNLP.objective x = x := rfl

def maximumObjective :=
  problem (x y : ℝ)
    maximize @HAdd.hAdd ℝ ℝ ℝ ⟨fun x y => x - y⟩ x y
    subject to lower : 0 ≤ x

reformulation maximumConic : maximumObjective := by conic
reformulation maximumNLP : maximumObjective := by nlp

example : maximumConic.conicForm.data.sense = .maximize := rfl
example : maximumNLP.nlpForm.data.sense = .maximize := rfl
example : maximumConic.conicForm.data.toProblem = maximumConic := maximumConic.conicForm.represents
example : maximumNLP.nlpForm.data.toProblem = maximumNLP := maximumNLP.nlpForm.represents
example (x y : ℝ) : maximumConic.objective (x, y) = x - y := rfl
example (x y : ℝ) : maximumNLP.objective (x, y) = x - y := rfl

def directRelations :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : @LE.le ℝ ⟨fun a b => b ≤ a⟩ x 1
      trivial : @LE.le ℝ ⟨fun _ _ => True⟩ x 0

reformulation directRelationsNLP : directRelations := by nlp

example : directRelationsNLP.nlpForm.data.rowCount = 1 := rfl
example (x : ℝ) : directRelationsNLP.feasible x ↔ 1 ≤ x ∧ True := Iff.rfl

-- The guard follows the logarithm in the same group. Its accepted direct
-- reduction must become available before the logarithmic leaf is retried.
def groupedDomain :=
  problem (x t : ℝ)
    minimize @Neg.neg ℝ ⟨fun x => Real.log x⟩ x
    subject to
      grouped : @Neg.neg ℝ ⟨fun x => Real.log x⟩ x ≤ t ∧
        @LE.le ℝ ⟨fun a b => b ≤ a⟩ x 1

reformulation groupedDomainNLP : groupedDomain := by nlp

example : groupedDomainNLP.nlpForm.data.rowCount = 2 := rfl
example : groupedDomainNLP.nlpForm.data.toProblem = groupedDomainNLP :=
  groupedDomainNLP.nlpForm.represents
example (x t : ℝ) : groupedDomainNLP.objective (x, t) = Real.log x := rfl
example (x t : ℝ) : groupedDomainNLP.feasible (x, t) ↔ Real.log x ≤ t ∧ 1 ≤ x := Iff.rfl

-- A later exact rewrite exposes the margin for both the earlier custom row
-- and the maximizing objective. All three use the final common evaluation domain.
def loweredDomain :=
  problem (x y t : ℝ)
    maximize @Neg.neg ℝ ⟨fun x => Real.log x⟩ x
    subject to
      logarithm : @Neg.neg ℝ ⟨fun x => Real.log x⟩ x ≤ t
      margin : 1 ≤ min x y

reformulation loweredDomainNLP : loweredDomain := by nlp

example : loweredDomainNLP.nlpForm.data.sense = .maximize := rfl
example : loweredDomainNLP.nlpForm.data.rowCount = 3 := rfl
example : loweredDomainNLP.nlpForm.data.toProblem = loweredDomainNLP :=
  loweredDomainNLP.nlpForm.represents
example : GlobalEquivalence loweredDomain loweredDomainNLP := loweredDomainNLP.equivalence

def mixedSigned :=
  problem (x t : ℝ)
    minimize @Neg.neg ℝ ⟨fun x => x⟩ t
    subject to grouped : @LE.le ℝ ⟨fun a b => b ≤ a⟩ x 1 ∧ t ≤ -|x|

reformulation mixedSignedNLP : mixedSigned := by nlp

example : mixedSignedNLP.nlpForm.data.rowCount = 3 := rfl
example : GlobalEquivalence mixedSigned mixedSignedNLP := mixedSignedNLP.equivalence

section ProofLet

variable (c : ℝ) (hc : c ≠ 0)

def proofLetSource :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : (let _proof : c ≠ 0 := hc
        @Neg.neg ℝ ⟨fun x => x / c⟩ x ≤ 1)

reformulation proofLetNLP : (proofLetSource c hc) := by nlp

example : (proofLetNLP.nlpForm c hc).data.rowCount = 1 := rfl
example : GlobalEquivalence (proofLetSource c hc) (proofLetNLP c hc) := proofLetNLP.equivalence c hc

end ProofLet

def missingDomain :=
  problem (x : ℝ)
    minimize @Neg.neg ℝ ⟨fun x => Real.log x⟩ x
    subject to boundary : 0 ≤ x

#guard_error_fragments ["not certified as a smooth NLP"] in
reformulation noMissingDomain : missingDomain := by nlp

def changedNonsmooth :=
  problem (x t : ℝ)
    minimize t
    subject to bound : @Neg.neg ℝ ⟨fun x => x⟩ |x| ≤ t

#guard_error_fragments ["constraint `bound`"] in
reformulation noChangedNLP : changedNonsmooth := by nlp

#guard_error_fragments ["constraint `bound`"] in
reformulation noChangedConic : changedNonsmooth := by conic

assert_not_exists noMissingDomain noChangedNLP noChangedConic

end
end MorewTest.Reformulation.DirectNormalization
