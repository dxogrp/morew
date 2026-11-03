/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Diagnostics

/-! Negation and comparison rewrites respect the operations captured by each problem. -/

namespace MorewTest.Reformulation.NegationNLP

open Morew
noncomputable section

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

end
end MorewTest.Reformulation.NegationNLP
