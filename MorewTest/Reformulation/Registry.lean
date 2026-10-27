/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.RegistrySource

/-!
# Registered rules through targeted and terminal commands

The imported helper has no privileged namespace or expression-certification
rule. Its registered exact representation supplies the complete replacement.
-/

namespace MorewTest.Reformulation.Registry

open Morew MorewTest.Reformulation.RegistrySource

noncomputable section

variable (center : ℝ)

reformulation conicTarget : (source center) := by
  conic at bound

reformulation nlpTarget : (source center) := by
  nlp at bound

example : GlobalEquivalence (source center) (conicTarget center) :=
  conicTarget.equivalence center

example : GlobalEquivalence (source center) (nlpTarget center) :=
  nlpTarget.equivalence center

example (x t : ℝ) : (conicTarget center).feasible (x, t) ↔
    0 ≤ x ∧ x - center ≤ t ∧ -(x - center) ≤ t ∧ t ≤ 10 := Iff.rfl

example (x t : ℝ) : (nlpTarget center).feasible (x, t) ↔
    0 ≤ x ∧ x - center ≤ t ∧ -(x - center) ≤ t ∧ t ≤ 10 := Iff.rfl

example : (conicTarget center).objective = (source center).objective := rfl
example : (nlpTarget center).objective = (source center).objective := rfl

/--
info: problem (x t : ℝ)
  let loss := shiftedAbs center x
  minimize t
  subject to
    before : 0 ≤ x
    bound_conic_1 : x - center ≤ t
    bound_conic_2 : -(x - center) ≤ t
    after : t ≤ 10
-/
#guard_msgs in
#printp conicTarget

/--
info: problem (x t : ℝ)
  let loss := shiftedAbs center x
  minimize t
  subject to
    before : 0 ≤ x
    bound_nlp_1 : x - center ≤ t
    bound_nlp_2 : -(x - center) ≤ t
    after : t ≤ 10
-/
#guard_msgs in
#printp nlpTarget

-- Declaration selection infers its explicit center parameter from the row.
reformulation selectedConic : (source center) := by
  conic at bound using shiftedAbsEpigraph

reformulation selectedNLP : (source center) := by
  nlp at bound using shiftedAbsEpigraph

-- An applied certificate keeps ordinary Lean term elaboration.
reformulation appliedConic : (source center) := by
  conic at bound using (shiftedAbsEpigraph center)

reformulation appliedNLP : (source center) := by
  nlp at bound using (shiftedAbsEpigraph center)

reformulation conicReady : (source center) := by
  conic

reformulation nlpReady : (source center) := by
  nlp

example : (conicReady.conicForm center).data.toProblem = conicReady center :=
  (conicReady.conicForm center).represents

example : (nlpReady.nlpForm center).data.toProblem = nlpReady center :=
  (nlpReady.nlpForm center).represents

reformulation maxConic : (maximizing center) := by
  conic

reformulation maxNLP : (maximizing center) := by
  nlp

example : (maxConic.conicForm center).data.sense = .maximize := rfl
example : (maxNLP.nlpForm center).data.sense = .maximize := rfl

section Unregistered

attribute [-morew_conic, -morew_nlp] shiftedAbsEpigraph

reformulation explicitConic : (source center) := by
  conic at bound using shiftedAbsEpigraph

reformulation explicitNLP : (source center) := by
  nlp at bound using shiftedAbsEpigraph

example : GlobalEquivalence (source center) (explicitConic center) :=
  explicitConic.equivalence center

example : GlobalEquivalence (source center) (explicitNLP center) :=
  explicitNLP.equivalence center

end Unregistered

-- Closing the scope restores imported registrations for later scripts.
reformulation restored : (source center) := by
  nlp at bound
  conic

example : GlobalEquivalence (source center) (restored center) :=
  restored.equivalence center

-- Targeted conic selection now reports genuine overlaps instead of accepting
-- the first successful native family. Explicit selection resolves either way.
def overlapping :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : max (0 : ℝ) 1 ≤ min 2 3

/--
error: constraint `bound`: ambiguous exact conic rules: Morew.Rewrite.maxEpigraph, Morew.Rewrite.minHypograph; select one with `using`
-/
#guard_msgs in
reformulation ambiguous : overlapping := by
  conic at bound

assert_not_exists ambiguous ambiguous.equivalence

reformulation upper : overlapping := by
  conic at bound using Rewrite.maxEpigraph

reformulation lower : overlapping := by
  conic at bound using Rewrite.minHypograph

example : GlobalEquivalence overlapping upper := upper.equivalence
example : GlobalEquivalence overlapping lower := lower.equivalence

-- Terminal validation still accepts an already affine row directly.
reformulation alreadyAffine : overlapping := by
  conic

example : IsConic alreadyAffine := alreadyAffine.isConic

-- Real-valued declaration parameters can be model operands, not only ambient
-- constants. Shape parameters and certificate instances remain uniform.
def decisionCenterSource :=
  problem (x shift t : ℝ)
    minimize t
    subject to
      bound : shiftedAbs shift x ≤ t

reformulation decisionCenterConic : decisionCenterSource := by
  conic at bound

reformulation decisionCenterNLP : decisionCenterSource := by
  nlp at bound

reformulation selectedDecisionCenterConic : decisionCenterSource := by
  conic at bound using shiftedAbsEpigraph

reformulation selectedDecisionCenterNLP : decisionCenterSource := by
  nlp at bound using shiftedAbsEpigraph

example : GlobalEquivalence decisionCenterSource decisionCenterConic :=
  decisionCenterConic.equivalence

example : GlobalEquivalence decisionCenterSource decisionCenterNLP :=
  decisionCenterNLP.equivalence

example (x shift t : ℝ) : decisionCenterConic.feasible ((x, shift), t) ↔
    x - shift ≤ t ∧ -(x - shift) ≤ t := Iff.rfl

example (x shift t : ℝ) : decisionCenterNLP.feasible ((x, shift), t) ↔
    x - shift ≤ t ∧ -(x - shift) ≤ t := Iff.rfl

end

end MorewTest.Reformulation.Registry

namespace MorewTest.Reformulation.Registry.ExplicitContainer

open Morew

noncomputable section

noncomputable def source :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : |x| ≤ 3

noncomputable def modelRule : ExactConstraintLift source.feasible :=
  .ofIff (fun x => x ≤ 3 ∧ -x ≤ 3)
    (fun x => Rewrite.Polyhedral.abs_le_iff x 3)

-- Concrete expressions keep the original checked predicate adapter, including
-- representation sources exposed through a named model's feasibility field.
reformulation ready : source := by
  conic at bound using (modelRule)

reformulation namedReady : source := by
  conic at bound using modelRule

reformulation namedNLP : source := by
  nlp at bound using modelRule

example : GlobalEquivalence source ready := ready.equivalence
example : GlobalEquivalence source namedReady := namedReady.equivalence
example : GlobalEquivalence source namedNLP := namedNLP.equivalence

example (x : ℝ) : ready.feasible x ↔ x ≤ 3 ∧ -x ≤ 3 := Iff.rfl
example (x : ℝ) : namedReady.feasible x ↔ x ≤ 3 ∧ -x ≤ 3 := Iff.rfl
example (x : ℝ) : namedNLP.feasible x ↔ x ≤ 3 ∧ -x ≤ 3 := Iff.rfl

end

end MorewTest.Reformulation.Registry.ExplicitContainer
