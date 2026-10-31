/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics

/-!
# Signed exact NLP bounds and graphs

Negation reuses existing records while every resulting row still passes the
NLP domain and smoothness checks. Smooth expressions keep their direct path.
-/

namespace MorewTest.Reformulation.NegationNLP

open Morew

noncomputable section

def logSource :=
  problem (x : ℝ)
    minimize -Real.log x
    subject to domain : 1 ≤ x

reformulation logReady : logSource := by nlp

example : IsSmoothNLP logReady := logReady.isSmoothNLP
example : logReady.objective = logSource.objective := rfl
example : logReady.nlpForm.data.rowCount = 1 := rfl

def absoluteSource :=
  problem (x : ℝ)
    maximize (-|x ^ 2 - 1| : ℝ)

reformulation absoluteBound : absoluteSource := by hypograph t

reformulation absoluteTarget : absoluteBound := by nlp at hypograph_t

reformulation absoluteSelected : absoluteBound := by
  nlp at hypograph_t using Rewrite.absEpigraph

reformulation absoluteApplied : absoluteBound := by
  nlp at hypograph_t using (Rewrite.absEpigraph)

reformulation absoluteReady : absoluteSource := by
  hypograph t
  nlp

example : GlobalEquivalence absoluteSource absoluteTarget :=
  absoluteBound.equivalence.trans absoluteTarget.equivalence
example : IsSmoothNLP absoluteReady := absoluteReady.isSmoothNLP
example : absoluteReady.nlpForm.data.sense = .maximize := rfl
example : absoluteReady.nlpForm.data.toProblem = absoluteReady := absoluteReady.nlpForm.represents
example : absoluteReady.nlpForm.data.rowCount = 2 := rfl
example (x t : ℝ) : absoluteTarget.feasible (x, t) ↔
    x ^ 2 - 1 ≤ -t ∧ -(x ^ 2 - 1) ≤ -t := Iff.rfl
example : absoluteSelected = absoluteTarget := rfl
example : absoluteApplied = absoluteTarget := rfl

/--
info: problem (x t : ℝ)
  maximize t
  subject to
    hypograph_t_nlp_1 : x ^ 2 - 1 ≤ -t
    hypograph_t_nlp_2 : -(x ^ 2 - 1) ≤ -t
-/
#guard_msgs in
#printp absoluteTarget

def normSource :=
  problem (x : ℝ)
    maximize -‖(WithLp.toLp 2 (fun i : Fin 2 => x ^ 2 + (i.val : ℝ)) :
      EuclideanSpace ℝ (Fin 2))‖

reformulation normReady : normSource := by
  hypograph t
  nlp

example : IsSmoothNLP normReady := normReady.isSmoothNLP
example : normReady.nlpForm.data.rowCount = 2 := rfl
example : normReady.nlpForm.data.sense = .maximize := rfl

def minimumSource :=
  problem (x : ℝ)
    minimize -min (x ^ 2) (Real.sin x)

reformulation minimumReady : minimumSource := by
  epigraph t
  nlp

example : IsSmoothNLP minimumReady := minimumReady.isSmoothNLP
example : minimumReady.nlpForm.data.sense = .minimize := rfl
example (x t : ℝ) : minimumReady.feasible (x, t) ↔
    -t ≤ x ^ 2 ∧ -t ≤ Real.sin x := Iff.rfl

-- Both endpoints, nested signs, and ≥ retain their original semantics.
def comparisons :=
  problem (x t : ℝ)
    minimize t
    subject to
      triple : -(-(-min (x ^ 2) (Real.sin x))) ≤ t
      both : -t ≤ -|x ^ 2 - 1|
      greater : -|x ^ 2 - 1| ≥ t

reformulation comparisonsReady : comparisons := by nlp

example : IsSmoothNLP comparisonsReady := comparisonsReady.isSmoothNLP
example : comparisonsReady.nlpForm.data.rowCount = 6 := rfl

section BoundAmbiguity

def negativeAbsHypograph : HypographRepresentation (fun x : ℝ => -|x|) where
  Auxiliary := Unit
  target x t _ := x ≤ -t ∧ -x ≤ -t
  source_iff_exists x t := by
    rw [le_neg]
    exact Rewrite.absEpigraph.source_iff_exists x (-t)

attribute [local morew_nlp] negativeAbsHypograph

#guard_error_fragments ["ambiguous exact NLP rules", "negativeAbsHypograph", "absEpigraph"] in
reformulation boundAmbiguous : absoluteBound := by nlp at hypograph_t

assert_not_exists boundAmbiguous boundAmbiguous.equivalence

reformulation boundDirect : absoluteBound := by nlp at hypograph_t using negativeAbsHypograph
reformulation boundDerived : absoluteBound := by nlp at hypograph_t using Rewrite.absEpigraph

example : boundDirect = boundDerived := rfl

end BoundAmbiguity

namespace Domain

def positiveLogHypograph :
    HypographRepresentation (fun x : {x : ℝ // 0 < x} => Real.log x.1) where
  Auxiliary := Unit
  target x t _ := Real.exp t ≤ x.1
  source_iff_exists x t := by
    simpa only [exists_const] using Real.le_log_iff_exp_le x.2 (x := t)

attribute [local morew_nlp] positiveLogHypograph

def source :=
  problem (x t : ℝ)
    minimize t
    subject to
      domain : 1 ≤ x
      bound : -Real.log x ≤ t

reformulation target : source := by nlp at bound
reformulation selected : source := by nlp at bound using positiveLogHypograph
reformulation applied : source := by nlp at bound using (positiveLogHypograph)

example (x t : ℝ) : target.feasible (x, t) ↔
    1 ≤ x ∧ Real.exp (-t) ≤ x := Iff.rfl
example : selected = target := rfl
example : applied = target := rfl

def missing :=
  problem (x t : ℝ)
    minimize t
    subject to bound : -Real.log x ≤ t

-- The prospective exponential row cannot supply its own positive domain.
#guard_error_fragments ["constraint `bound`", "missing retained premise"] in
reformulation rejectedMissing : missing := by nlp at bound

assert_not_exists rejectedMissing rejectedMissing.equivalence

def guardedIdentity (x : ℝ) : ℝ := x

def guardedHypograph :
    HypographRepresentation (fun x : {x : ℝ // 0 ≤ x} => guardedIdentity x.1) where
  Auxiliary := Unit
  target x t _ := t ≤ x.1
  source_iff_exists _ _ := by simp only [guardedIdentity, exists_const]

def selectedPremise :=
  problem (x : ℝ)
    minimize x
    subject to bound : -guardedIdentity x ≤ 0

-- Even when the selected relation implies the premise, it is not retained evidence.
#guard_error_fragments ["constraint `bound`", "missing retained premise"] in
reformulation rejectedSelectedPremise : selectedPremise := by
  nlp at bound using guardedHypograph

assert_not_exists rejectedSelectedPremise rejectedSelectedPremise.equivalence

end Domain

namespace Graph

theorem absolute_iff (x y : ℝ) : y = |x| ↔ 0 ≤ y ∧ y ^ 2 = x ^ 2 := by
  constructor
  · rintro rfl
    exact ⟨abs_nonneg x, sq_abs x⟩
  · rintro ⟨hy, hsq⟩
    simpa only [abs_of_nonneg hy] using (sq_eq_sq_iff_abs_eq_abs y x).mp hsq

def absoluteGraph : GraphRepresentation (fun x : ℝ => |x|) where
  Auxiliary := Unit
  target x y _ := 0 ≤ y ∧ y ^ 2 = x ^ 2
  source_iff_exists x y := by
    simpa only [exists_const] using absolute_iff x y

attribute [scoped morew_nlp] absoluteGraph

def source :=
  problem (x y : ℝ)
    minimize y
    subject to bound : y = -|x ^ 2 - 1|

reformulation target : source := by nlp at bound
reformulation selected : source := by nlp at bound using absoluteGraph
reformulation applied : source := by nlp at bound using (absoluteGraph)
reformulation ready : source := by nlp

example : GlobalEquivalence source target := target.equivalence
example : IsSmoothNLP ready := ready.isSmoothNLP
example : ready.nlpForm.data.rowCount = 2 := rfl
example (x y : ℝ) : target.feasible (x, y) ↔
    0 ≤ -y ∧ (-y) ^ 2 = (x ^ 2 - 1) ^ 2 := Iff.rfl
example : selected = target := rfl
example : applied = target := rfl

/--
info: problem (x y : ℝ)
  minimize y
  subject to
    bound_nlp_1 : 0 ≤ -y
    bound_nlp_2 : (-y) ^ 2 = (x ^ 2 - 1) ^ 2
-/
#guard_msgs in
#printp target

def equations :=
  problem (x y : ℝ)
    minimize y
    subject to
      right : y = -|x|
      left : -|x| = y
      both : -y = -|x|
      nested : -(-y) = -(-(-|x|))

reformulation equationsTarget : equations := by
  nlp at right
  nlp at left
  nlp at both
  nlp at nested

reformulation equationsReady : equations := by nlp

example : IsSmoothNLP equationsReady := equationsReady.isSmoothNLP
example : equationsReady.nlpForm.data.rowCount = 8 := rfl
example (x y : ℝ) : equationsTarget.feasible (x, y) ↔
    0 ≤ -y ∧ (-y) ^ 2 = x ^ 2 ∧
    0 ≤ -y ∧ (-y) ^ 2 = x ^ 2 ∧
    0 ≤ y ∧ y ^ 2 = x ^ 2 ∧
    0 ≤ -y ∧ (-y) ^ 2 = x ^ 2 := Iff.rfl

def negativeAbsoluteGraph : GraphRepresentation (fun x : ℝ => -|x|) where
  Auxiliary := Unit
  target x y _ := 0 ≤ -y ∧ (-y) ^ 2 = x ^ 2
  source_iff_exists x y := by
    simp only [exists_const]
    constructor
    · intro h
      apply (absolute_iff x (-y)).mp
      rw [h, neg_neg]
    · intro h
      have equality := congrArg Neg.neg ((absolute_iff x (-y)).mpr h)
      simpa only [neg_neg] using equality

section Ambiguity

attribute [local morew_nlp] negativeAbsoluteGraph

#guard_error_fragments ["ambiguous exact NLP rules", "absoluteGraph", "negativeAbsoluteGraph"] in
reformulation ambiguous : source := by nlp at bound

assert_not_exists ambiguous ambiguous.equivalence

reformulation direct : source := by nlp at bound using negativeAbsoluteGraph
reformulation derived : source := by nlp at bound using absoluteGraph
reformulation directApplied : source := by nlp at bound using (negativeAbsoluteGraph)

example : direct = derived := rfl
example : directApplied = direct := rfl

end Ambiguity

section ReverseRegistration

attribute [-morew_nlp] absoluteGraph
attribute [local morew_nlp] negativeAbsoluteGraph absoluteGraph

#guard_error_fragments ["ambiguous exact NLP rules", "absoluteGraph", "negativeAbsoluteGraph"] in
reformulation ambiguousReverse : source := by nlp at bound

assert_not_exists ambiguousReverse ambiguousReverse.equivalence

end ReverseRegistration

namespace Guarded

-- This graph is valid only on its declared domain; other graph registrations
-- are scoped out so discovery must establish that premise.
attribute [-morew_nlp] absoluteGraph

def nonnegativeAbsoluteGraph :
    GraphRepresentation (fun x : {x : ℝ // 0 ≤ x} => |x.1|) where
  Auxiliary := Unit
  target x y _ := y = x.1
  source_iff_exists x _ := by simp only [exists_const, abs_of_nonneg x.2]

attribute [local morew_nlp] nonnegativeAbsoluteGraph

def domainSource :=
  problem (x y : ℝ)
    minimize y
    subject to
      domain : 0 ≤ x
      bound : y = -|x|

reformulation domainTarget : domainSource := by nlp at bound
reformulation domainSelected : domainSource := by
  nlp at bound using nonnegativeAbsoluteGraph

example (x y : ℝ) : domainTarget.feasible (x, y) ↔ 0 ≤ x ∧ -y = x := Iff.rfl
example : domainSelected = domainTarget := rfl

def missingDomain :=
  problem (x y : ℝ)
    minimize y
    subject to bound : y = -|x|

#guard_error_fragments ["constraint `bound`", "missing retained premise"] in
reformulation missingAutomatic : missingDomain := by nlp at bound

#guard_error_fragments ["constraint `bound`", "missing retained premise"] in
reformulation missingSelected : missingDomain := by nlp at bound using nonnegativeAbsoluteGraph

def selectedDomain :=
  problem (x : ℝ)
    minimize x
    subject to bound : 0 = -|x|

#guard_error_fragments ["constraint `bound`", "missing retained premise"] in
reformulation missingSelectedDomain : selectedDomain := by
  nlp at bound using nonnegativeAbsoluteGraph

assert_not_exists missingAutomatic missingSelected missingSelectedDomain

end Guarded

def alteredNegation :=
  problem (x y : ℝ)
    minimize y
    subject to bound : y = @Neg.neg ℝ ⟨fun x => x⟩ |x|

#guard_error_fragments ["constraint `bound`"] in
reformulation alteredAutomatic : alteredNegation := by nlp at bound

#guard_error_fragments ["constraint `bound`"] in
reformulation alteredSelected : alteredNegation := by nlp at bound using absoluteGraph

assert_not_exists alteredAutomatic alteredSelected

-- A valid graph record whose target is still nonsmooth is not an NLP certificate.
def unsmoothedGraph : GraphRepresentation (fun x : ℝ => |x|) where
  Auxiliary := Unit
  target x y _ := y = |x|
  source_iff_exists _ _ := by simp only [exists_const]

#guard_error_fragments ["constraint `bound`", "generated row certification failed"] in
reformulation rejectedTarget : source := by nlp at bound using unsmoothedGraph

assert_not_exists rejectedTarget rejectedTarget.equivalence

end Graph

namespace InstanceSafety

def affineAtom (x : ℝ) : ℝ := x + 1

def affineGraph : GraphRepresentation affineAtom where
  Auxiliary := Unit
  target x y _ := y = x + 1
  source_iff_exists _ _ := by simp only [affineAtom, exists_const]

attribute [local morew_conic, local morew_nlp] affineGraph

-- The custom operation agrees at this particular operand, but it is not the
-- real negation instance. Equality of values cannot authorize sign adaptation.
def coincidentNegation :=
  problem (y : ℝ)
    minimize y
    subject to bound : y = @Neg.neg ℝ ⟨fun _ => -(affineAtom 0)⟩ (affineAtom 0)

example : @Neg.neg ℝ ⟨fun _ => -(affineAtom 0)⟩ (affineAtom 0) =
    -(affineAtom 0) := rfl

#guard_error_fragments ["constraint `bound`"] in
reformulation badNegNLPAutomatic : coincidentNegation := by nlp at bound

#guard_error_fragments ["constraint `bound`"] in
reformulation badNegNLPSelected : coincidentNegation := by nlp at bound using affineGraph

#guard_error_fragments ["constraint `bound`"] in
reformulation badNegNLPApplied : coincidentNegation := by nlp at bound using (affineGraph)

#guard_error_fragments ["constraint `bound`"] in
reformulation badNegConicAutomatic : coincidentNegation := by conic at bound

#guard_error_fragments ["constraint `bound`"] in
reformulation badNegConicSelected : coincidentNegation := by conic at bound using affineGraph

#guard_error_fragments ["constraint `bound`"] in
reformulation badNegConicApplied : coincidentNegation := by conic at bound using (affineGraph)

assert_not_exists badNegNLPAutomatic badNegNLPSelected badNegNLPApplied
  badNegConicAutomatic badNegConicSelected badNegConicApplied

-- This relation agrees with the real order when its left operand is zero.
-- Its different instance still forbids real-order sign transfer.
def coincidentOrder :=
  problem (x : ℝ)
    minimize x
    subject to bound : @LE.le ℝ ⟨fun _ b => (0 : ℝ) ≤ b⟩ 0 (-|x|)

example (x : ℝ) : @LE.le ℝ ⟨fun _ b => (0 : ℝ) ≤ b⟩ 0 (-|x|) ↔
    0 ≤ -|x| := Iff.rfl

#guard_error_fragments ["constraint `bound`"] in
reformulation badOrderNLPAutomatic : coincidentOrder := by nlp at bound

#guard_error_fragments ["constraint `bound`"] in
reformulation badOrderNLPSelected : coincidentOrder := by nlp at bound using Rewrite.absEpigraph

#guard_error_fragments ["constraint `bound`"] in
reformulation badOrderNLPApplied : coincidentOrder := by nlp at bound using (Rewrite.absEpigraph)

#guard_error_fragments ["constraint `bound`"] in
reformulation badOrderConicAutomatic : coincidentOrder := by conic at bound

#guard_error_fragments ["constraint `bound`"] in
reformulation badOrderConicSelected : coincidentOrder := by conic at bound using Rewrite.absEpigraph

#guard_error_fragments ["constraint `bound`"] in
reformulation badOrderConicApplied : coincidentOrder := by conic at bound using (Rewrite.absEpigraph)

assert_not_exists badOrderNLPAutomatic badOrderNLPSelected badOrderNLPApplied
  badOrderConicAutomatic badOrderConicSelected badOrderConicApplied

-- Literal bounds must make the same instance checks as adapted signed bounds.
-- This decision-dependent relation ignores its arguments but happens to return
-- the native proposition at the selected operands.
def coincidentDirectOrder :=
  problem (x t : ℝ)
    minimize t
    subject to bound : @LE.le ℝ ⟨fun _ _ => |x| ≤ t⟩ |x| t

example (x t : ℝ) : @LE.le ℝ ⟨fun _ _ => |x| ≤ t⟩ |x| t ↔ |x| ≤ t := Iff.rfl

#guard_error_fragments ["constraint `bound`"] in
reformulation badDirectOrderNLPAutomatic : coincidentDirectOrder := by nlp at bound

#guard_error_fragments ["constraint `bound`"] in
reformulation badDirectOrderNLPSelected : coincidentDirectOrder := by
  nlp at bound using Rewrite.absEpigraph

#guard_error_fragments ["constraint `bound`"] in
reformulation badDirectOrderNLPApplied : coincidentDirectOrder := by
  nlp at bound using (Rewrite.absEpigraph)

#guard_error_fragments ["constraint `bound`"] in
reformulation badDirectOrderConicAutomatic : coincidentDirectOrder := by conic at bound

#guard_error_fragments ["constraint `bound`"] in
reformulation badDirectOrderConicSelected : coincidentDirectOrder := by
  conic at bound using Rewrite.absEpigraph

#guard_error_fragments ["constraint `bound`"] in
reformulation badDirectOrderConicApplied : coincidentDirectOrder := by
  conic at bound using (Rewrite.absEpigraph)

assert_not_exists badDirectOrderNLPAutomatic badDirectOrderNLPSelected badDirectOrderNLPApplied
  badDirectOrderConicAutomatic badDirectOrderConicSelected badDirectOrderConicApplied

-- Direct affine relations may reduce semantically while a nonlinear sibling
-- still reaches the checked signed registry path.
def mixedDirectAndSigned :=
  problem (x t : ℝ)
    minimize t
    subject to grouped : @LE.le ℝ ⟨fun a b => b ≤ a⟩ x 1 ∧ t ≤ -|x|

reformulation mixedDirectAndSignedReady : mixedDirectAndSigned := by conic

example : IsConic mixedDirectAndSignedReady := mixedDirectAndSignedReady.isConic
example : mixedDirectAndSignedReady.conicForm.data.rowCount = 3 := rfl
example : GlobalEquivalence mixedDirectAndSigned mixedDirectAndSignedReady :=
  mixedDirectAndSignedReady.equivalence

def mixedProofLet :=
  problem (x t : ℝ)
    minimize t
    subject to grouped :
      (let _proof : (0 : ℝ) ≤ 1 := (by norm_num);
        @LE.le ℝ ⟨fun a b => b ≤ a⟩ x 1 ∧ t ≤ -|x|)

reformulation mixedProofLetReady : mixedProofLet := by conic

example : IsConic mixedProofLetReady := mixedProofLetReady.isConic
example : mixedProofLetReady.conicForm.data.rowCount = 3 := rfl
example : GlobalEquivalence mixedProofLet mixedProofLetReady := mixedProofLetReady.equivalence

def terminalChangedNegation :=
  problem (x t : ℝ)
    minimize t
    subject to bound : @Neg.neg ℝ ⟨fun x => x⟩ |x| ≤ t

#guard_error_fragments ["terminal conic validation is uncertified", "constraint `bound`"] in
reformulation badTerminalNegation : terminalChangedNegation := by conic

#guard_error_fragments ["terminal conic validation is uncertified", "constraint `bound`"] in
reformulation badTerminalOrder : coincidentOrder := by conic

assert_not_exists badTerminalNegation badTerminalOrder

end InstanceSafety

namespace Failures

def nonsmoothTarget :=
  problem (x t : ℝ)
    maximize t
    subject to bound : t ≤ -|min x (2 * x)|

#guard_error_fragments ["constraint `bound`", "generated row certification failed"] in
reformulation rejectedNonsmooth : nonsmoothTarget := by nlp at bound using Rewrite.absEpigraph

assert_not_exists rejectedNonsmooth rejectedNonsmooth.equivalence

def alteredNeg :=
  problem (x t : ℝ)
    maximize t
    subject to bound : t ≤ @Neg.neg ℝ ⟨fun x => x⟩ |x|

#guard_error_fragments ["constraint `bound`"] in
reformulation rejectedNeg : alteredNeg := by nlp at bound using Rewrite.absEpigraph

def alteredOrder :=
  problem (x t : ℝ)
    maximize t
    subject to bound : @LE.le ℝ ⟨fun _ _ => True⟩ t (-|x|)

#guard_error_fragments ["constraint `bound`"] in
reformulation rejectedOrder : alteredOrder := by nlp at bound using Rewrite.absEpigraph

def alteredNorm :=
  problem (x : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    maximize t
    subject to bound : t ≤ -(@Norm.norm (EuclideanSpace ℝ (Fin 2)) ⟨fun _ => 0⟩ x)

#guard_error_fragments ["constraint `bound`"] in
reformulation rejectedNorm : alteredNorm := by nlp at bound using Rewrite.euclideanNormEpigraph

assert_not_exists rejectedNeg rejectedOrder rejectedNorm

end Failures

end
end MorewTest.Reformulation.NegationNLP
