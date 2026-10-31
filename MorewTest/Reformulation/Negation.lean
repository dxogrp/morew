/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics

/-!
# Exact conic bounds through real negation

The source keeps its spelling while existing epigraph and hypograph records
certify the reversed bound. Domains and ambiguity remain checked at each use.
-/

namespace MorewTest.Reformulation.Negation

open Morew Morew.Conic

noncomputable section

def logSource :=
  problem (x : ℝ)
    let loss := -Real.log x
    minimize loss
    subject to
      domain : 1 ≤ x
      cap : x ≤ 3

reformulation logBound : logSource := by
  epigraph t as lossBound

reformulation logTarget : logBound := by
  conic at lossBound

reformulation logReady : logSource := by
  epigraph t as lossBound
  conic

reformulation logSelected : logBound := by
  conic at lossBound using Exponential.logHypograph

reformulation logApplied : logBound := by
  conic at lossBound using (Exponential.logHypograph)

example : GlobalEquivalence logSource logTarget :=
  logBound.equivalence.trans logTarget.equivalence
example : IsConic logReady := logReady.isConic
example : Conic.Form logReady := logReady.conicForm
example : logReady.conicForm.data.toProblem = logReady := logReady.conicForm.represents
example : logReady.conicForm.data.sense = .minimize := rfl
example : logReady.conicForm.data.rowCount = 3 := rfl
example (x t : ℝ) : logTarget.feasible (x, t) ↔
    1 ≤ x ∧ x ≤ 3 ∧ (-t, 1, x) ∈ EXP := Iff.rfl
example : logSelected = logTarget := rfl
example : logApplied = logTarget := rfl

/--
info: problem (x t : ℝ)
  let loss := -Real.log x
  minimize t
  subject to
    domain : 1 ≤ x
    cap : x ≤ 3
    lossBound : loss ≤ t
-/
#guard_msgs in
#printp logBound

/--
info: problem (x t : ℝ)
  let loss := -Real.log x
  minimize t
  subject to
    domain : 1 ≤ x
    cap : x ≤ 3
    lossBound_conic_1 : (-t, 1, x) ∈ EXP
-/
#guard_msgs in
#printp logTarget

def minimumSource :=
  problem (x : ℝ)
    minimize -min x (2 * x)

reformulation minimumReady : minimumSource := by
  epigraph t
  conic

example : IsConic minimumReady := minimumReady.isConic
example : minimumReady.conicForm.data.rowCount = 2 := rfl

def meanSource (n : Nat) :=
  problem (x : Fin n → ℝ)
    minimize -Fn.geoMean x
    subject to domain : 0 ≤ x

variable (n : Nat) (hn : 0 < n)

include hn in
reformulation meanReady : (meanSource n) := by
  epigraph t
  conic

example : GlobalEquivalence (meanSource n) (meanReady n hn) := meanReady.equivalence n hn
example : IsConic (meanReady n hn) := meanReady.isConic n hn
example : (meanReady.conicForm n hn).data.rowCount = 5 := rfl

def absoluteSource :=
  problem (x : ℝ)
    maximize -|x|

reformulation absoluteReady : absoluteSource := by
  hypograph t
  conic

example : IsConic absoluteReady := absoluteReady.isConic
example : absoluteReady.conicForm.data.sense = .maximize := rfl
example : absoluteReady.conicForm.data.rowCount = 2 := rfl

def normSource (n : Nat) :=
  problem (x : EuclideanSpace ℝ (Fin n))
    maximize -‖x‖

reformulation normBound : (normSource n) := by
  hypograph t

reformulation normReady : (normSource n) := by
  hypograph t
  conic

example : IsConic (normReady n) := normReady.isConic n
example : (normReady.conicForm n).data.sense = .maximize := rfl
example : (normReady.conicForm n).data.rowCount = 1 := rfl

-- Consume original endpoint negations once, with either relation spelling.
def endpointSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      domain : 1 ≤ x
      triple : -(-(-Real.log x)) ≤ t
      double : -(-|x|) ≤ t
      bothLog : -Real.log x ≤ -t
      bothAbs : -t ≤ -|x|
      greaterLog : t ≥ -Real.log x
      greaterAbs : -|x| ≥ t

reformulation endpointTarget : endpointSource := by
  conic at triple
  conic at double
  conic at bothLog
  conic at bothAbs
  conic at greaterLog
  conic at greaterAbs

reformulation endpointReady : endpointSource := by conic

example : GlobalEquivalence endpointSource endpointTarget := endpointTarget.equivalence
example : IsConic endpointReady := endpointReady.isConic
example : endpointReady.conicForm.data.rowCount = 10 := rfl
example (x t : ℝ) : endpointTarget.feasible (x, t) ↔
    1 ≤ x ∧ (-t, 1, x) ∈ EXP ∧
    x ≤ t ∧ -x ≤ t ∧ (t, 1, x) ∈ EXP ∧
    x ≤ t ∧ -x ≤ t ∧ (-t, 1, x) ∈ EXP ∧
    x ≤ -t ∧ -x ≤ -t := Iff.rfl

namespace Custom

def reward (center x : ℝ) : ℝ := min (x - center) (2 * x)

@[morew_conic, morew_nlp]
def rewardHypograph (center : ℝ) : HypographRepresentation (reward center) where
  Auxiliary := Unit
  target x t _ := t ≤ x - center ∧ t ≤ 2 * x
  source_iff_exists x t := Rewrite.minHypograph.source_iff_exists (x - center, 2 * x) t

def source (center : ℝ) :=
  problem (x t : ℝ)
    minimize t
    subject to bound : -reward center x ≤ t

variable (center : ℝ)

reformulation target : (source center) := by conic at bound
reformulation selected : (source center) := by conic at bound using rewardHypograph
reformulation applied : (source center) := by conic at bound using (rewardHypograph center)

example : GlobalEquivalence (source center) (target center) := target.equivalence center
example (x t : ℝ) : (target center).feasible (x, t) ↔
    -t ≤ x - center ∧ -t ≤ 2 * x := Iff.rfl
example : selected center = target center := rfl
example : applied center = target center := rfl

-- Distinct direct-negative and derived rules remain genuinely ambiguous.
def negativeRewardEpigraph (center : ℝ) :
    EpigraphRepresentation (fun x => -reward center x) where
  Auxiliary := Unit
  target x t _ := -t ≤ x - center ∧ -t ≤ 2 * x
  source_iff_exists x t := by
    rw [neg_le]
    exact (rewardHypograph center).source_iff_exists x (-t)

section Overlap

attribute [local morew_conic] negativeRewardEpigraph

#guard_error_fragments ["ambiguous exact conic rules", "negativeRewardEpigraph",
    "rewardHypograph", "using"] in
reformulation ambiguous : (source center) := by conic at bound

assert_not_exists ambiguous ambiguous.equivalence

reformulation direct : (source center) := by conic at bound using negativeRewardEpigraph
reformulation derived : (source center) := by conic at bound using rewardHypograph
reformulation directApplied : (source center) := by
  conic at bound using (negativeRewardEpigraph center)

example : direct center = derived center := rfl
example : directApplied center = direct center := rfl

end Overlap

section ReverseRegistration

attribute [-morew_conic] rewardHypograph
attribute [local morew_conic] negativeRewardEpigraph rewardHypograph

#guard_error_fragments ["ambiguous exact conic rules", "negativeRewardEpigraph",
    "rewardHypograph", "using"] in
reformulation ambiguousReversed : (source center) := by conic at bound

assert_not_exists ambiguousReversed ambiguousReversed.equivalence

end ReverseRegistration

-- The same checked sign view also exposes a smooth NLP representation.
reformulation nlpSigned : (source center) := by nlp at bound

example : nlpSigned center = target center := rfl

-- Existing direct whole-predicate and graph rules still match directly.
def exactRule (center : ℝ) :
    ExactConstraintLift (fun p : ℝ × ℝ => p.2 ≤ reward center p.1) :=
  (rewardHypograph center).toExactConstraintLift Prod.fst Prod.snd

def wholeSource (center : ℝ) :=
  problem (x t : ℝ)
    maximize t
    subject to bound : t ≤ reward center x

reformulation exactDirect : (wholeSource center) := by conic at bound using exactRule

#guard_error_fragments ["constraint `bound`"] in
reformulation exactUnchanged : (source center) := by conic at bound using exactRule

assert_not_exists exactUnchanged exactUnchanged.equivalence

def shifted (x : ℝ) : ℝ := x + 1

def shiftedGraph : GraphRepresentation shifted where
  Auxiliary := Unit
  target x t _ := t = x + 1
  source_iff_exists _ _ := by simp only [shifted, exists_const]

def graphSource :=
  problem (x t : ℝ)
    minimize t
    subject to bound : t = shifted x

def negativeGraphSource :=
  problem (x t : ℝ)
    minimize t
    subject to bound : -t = -shifted x

reformulation graphDirect : graphSource := by conic at bound using shiftedGraph

reformulation graphSigned : negativeGraphSource := by conic at bound using shiftedGraph

example : GlobalEquivalence negativeGraphSource graphSigned := graphSigned.equivalence
example (x t : ℝ) : graphSigned.feasible (x, t) ↔ t = x + 1 := Iff.rfl

section RegisteredGraph

attribute [local morew_conic] shiftedGraph

reformulation graphAutomatic : negativeGraphSource := by conic at bound
reformulation graphApplied : negativeGraphSource := by conic at bound using (shiftedGraph)

example : graphAutomatic = graphSigned := rfl
example : graphApplied = graphSigned := rfl

end RegisteredGraph

end Custom

namespace FixedParameters

def indexedAbs (n : Nat) (x : ℝ) : ℝ := |x - n|

def indexedAbsEpigraph (n : Nat) : EpigraphRepresentation (indexedAbs n) where
  Auxiliary := Unit
  target x t _ := x - n ≤ t ∧ -(x - n) ≤ t
  source_iff_exists x t := Rewrite.absEpigraph.source_iff_exists (x - n) t

def source (n : Nat) :=
  problem (x t : ℝ)
    minimize t
    subject to bound : indexedAbs (n + 0) x ≤ t

def signedSource (n : Nat) :=
  problem (x t : ℝ)
    minimize t
    subject to bound : t ≤ -indexedAbs (n + 0) x

-- A supplied record may fix a symbolic discrete parameter before matching.
-- Definitional equality still recognizes that parameter beneath the atom.
reformulation target : (source n) := by
  conic at bound using (indexedAbsEpigraph n)

reformulation nlpTarget : (source n) := by
  nlp at bound using (indexedAbsEpigraph n)

reformulation signedTarget : (signedSource n) := by
  conic at bound using (indexedAbsEpigraph n)

reformulation signedNLP : (signedSource n) := by
  nlp at bound using (indexedAbsEpigraph n)

example : GlobalEquivalence (source n) (target n) := target.equivalence n
example : nlpTarget n = target n := rfl
example : signedNLP n = signedTarget n := rfl
example (x t : ℝ) : (signedTarget n).feasible (x, t) ↔
    x - n ≤ -t ∧ -(x - n) ≤ -t := Iff.rfl

def finAbs {n : Nat} (i : Fin n) (x : ℝ) : ℝ := indexedAbs i.val x

def finAbsEpigraph {n : Nat} (i : Fin n) : EpigraphRepresentation (finAbs i) :=
  indexedAbsEpigraph i.val

def finSource {n : Nat} (i : Fin n) :=
  problem (x t : ℝ)
    minimize t
    subject to bound : t ≤ -(finAbs
      (⟨i.val + 0, by simpa only [Nat.add_zero] using i.isLt⟩ : Fin n) x)

variable (i : Fin n)

reformulation finTarget : (finSource i) := by
  conic at bound using (finAbsEpigraph i)

reformulation finNLP : (finSource i) := by
  nlp at bound using (finAbsEpigraph i)

example : GlobalEquivalence (finSource i) (finTarget n i) := finTarget.equivalence n i
example : finNLP n i = finTarget n i := rfl
example (x t : ℝ) : (finTarget n i).feasible (x, t) ↔
    x - i.val ≤ -t ∧ -(x - i.val) ≤ -t := Iff.rfl

end FixedParameters

namespace Failures

def missingDomain :=
  problem (x t : ℝ)
    minimize t
    subject to bound : -Real.log x ≤ t

#guard_error_fragments ["constraint `bound`", "positive constant margin"] in
reformulation rejectedDomain : missingDomain := by conic at bound

assert_not_exists rejectedDomain rejectedDomain.equivalence

-- A whole selected conjunction is not implicitly split to match an atom rule.
def selfDomain :=
  problem (x t : ℝ)
    minimize t
    subject to bound : 1 ≤ x ∧ -Real.log x ≤ t

#guard_error_fragments ["constraint `bound`"] in
reformulation rejectedSelfDomain : selfDomain := by
  conic at bound using Exponential.logHypograph

assert_not_exists rejectedSelfDomain rejectedSelfDomain.equivalence

def wrongPolarity :=
  problem (x t : ℝ)
    minimize t
    subject to bound : -|x| ≤ t

#guard_error_fragments ["constraint `bound`", "no supported registered"] in
reformulation rejectedPolarity : wrongPolarity := by conic at bound

assert_not_exists rejectedPolarity rejectedPolarity.equivalence

def nestedArithmetic :=
  problem (x t : ℝ)
    minimize t
    subject to
      domain : 1 ≤ x
      nested : -Real.log x + 1 ≤ t
      coefficient : (-2) * Real.log x ≤ t
      subtraction : 0 - Real.log x ≤ t
      equality : -Real.log x = t

#guard_error_fragments ["constraint `nested`", "no supported registered"] in
reformulation rejectedNested : nestedArithmetic := by conic at nested

#guard_error_fragments ["constraint `coefficient`"] in
reformulation rejectedCoefficient : nestedArithmetic := by conic at coefficient

#guard_error_fragments ["constraint `subtraction`", "no supported registered"] in
reformulation rejectedSubtraction : nestedArithmetic := by conic at subtraction

#guard_error_fragments ["constraint `equality`", "no supported registered"] in
reformulation rejectedEquality : nestedArithmetic := by conic at equality

assert_not_exists rejectedNested rejectedCoefficient rejectedSubtraction rejectedEquality

end Failures

end
end MorewTest.Reformulation.Negation
