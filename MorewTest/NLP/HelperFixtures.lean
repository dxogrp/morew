/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Smooth

/-!
# Imported fixtures for bounded smooth helper expansion

These ordinary declarations have no registration attributes. Tests in separate
modules exercise their imported bodies, universe parameters, and scoped evidence.
-/

namespace MorewTest.NLP.HelperFixtures

noncomputable section
universe u

def square (x : ℝ) : ℝ := x * x
abbrev shift (x : ℝ) : ℝ := x + 1
def nestedSquare (x : ℝ) : ℝ := square x
def polynomial (a b x : ℝ) : ℝ := a * x * x + b
def taggedSquare {α : Type u} (_tag : α) (x : ℝ) : ℝ := x * x
def ignored (_x : ℝ) : ℝ := 0
def ignoredPair (_x : ℝ × ℝ) : ℝ := 0
def ignoredVector (_x : Fin 2 → ℝ) : ℝ := 0

def hiddenLog (x : ℝ) : ℝ := Real.log x
def nestedLog (x : ℝ) : ℝ := hiddenLog x
def hiddenAbs (x : ℝ) : ℝ := |x|
def hiddenTan (x : ℝ) : ℝ := Real.tan x
def branchSquare (x : ℝ) : ℝ := if x ≤ 0 then x * x else x * x
opaque sealedSquare (x : ℝ) : ℝ := x * x
@[irreducible] def irreducibleSquare (x : ℝ) : ℝ := x * x

def recursiveSquare : Nat → ℝ → ℝ
  | 0, x => x
  | n + 1, x => recursiveSquare n (x * x)

def hiddenExponent (_x : ℝ) : Nat := 2
def hiddenIndex (_x : ℝ) : Fin 2 := 0

def sumSquares {n : Nat} (v : Fin n → ℝ) : ℝ := ∑ i, v i * v i
def euclideanSquare (v : EuclideanSpace ℝ (Fin 1)) : ℝ := v 0 * v 0

-- The second field must not be visited when only the first field is selected.
def smoothTuple (x : ℝ) : ℝ × ℝ := (x * x, |x|)
def functionPair : (ℝ → ℝ) × ℝ := ((fun x => x * x), 0)
def selectedHelper (x : ℝ) : ℝ × ℝ := (square x, 0)
def partialAddPair (x : ℝ) : (ℝ → ℝ) × ℝ := (HAdd.hAdd (square x), 0)
def constantPair : ℝ × ℝ := (Real.log 0, 1)
def constantWrapper (x : ℝ) : ℝ := hiddenLog 0 + square x
def constantArgumentWrapper (x : ℝ) : ℝ := ignored (Real.log 0) + square x

abbrev alteredAdd : HAdd ℝ ℝ ℝ := ⟨fun a b => a + b + 1⟩
def noncanonical (x : ℝ) : ℝ := @HAdd.hAdd ℝ ℝ ℝ alteredAdd x x
def noncanonicalPair : (ℝ → ℝ) × ℝ :=
  ((fun x => @HAdd.hAdd ℝ ℝ ℝ alteredAdd x x), 0)
def noncanonicalPartial (x : ℝ) : (ℝ → ℝ) × ℝ :=
  ((@HAdd.hAdd ℝ ℝ ℝ alteredAdd x), 0)

def coefficient (c : ℝ) : ℝ := c ^ 2 + 1
theorem coefficient_pos (c : ℝ) : 0 < coefficient c :=
  add_pos_of_nonneg_of_pos (sq_nonneg c) zero_lt_one

def withEvidence (c x : ℝ) : ℝ :=
  let _h : 0 < coefficient c := coefficient_pos c
  Real.log (coefficient c) * x

def withInstanceEvidence (c x : ℝ) : ℝ :=
  letI : Fact (0 < coefficient c) := ⟨coefficient_pos c⟩
  let _h : 0 < coefficient c := Fact.out
  Real.log (coefficient c) * x

theorem decisionEvidence (c _x : ℝ) : 0 < coefficient c := coefficient_pos c

def withDependentEvidence (c x : ℝ) : ℝ :=
  let _h : 0 < coefficient c := decisionEvidence c x
  Real.log (coefficient c) * x

def indexedEvidence {n : Nat} (c : Fin n → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, let _h : 0 < coefficient (c i) := coefficient_pos (c i)
       Real.log (coefficient (c i)) * v i

def wrongIndexEvidence (c : Fin 2 → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  ∑ i, letI : Fact (0 < coefficient (c i)) := ⟨coefficient_pos (c i)⟩
       let _h : 0 < coefficient (c i) := Fact.out
       Real.log (coefficient (c 0)) * v i

-- The scalar fallback must not discover a whole model or predicate.
def squareProblem (x : ℝ) : Morew.Problem ℝ ℝ :=
  ⟨fun y => x * x + y, fun _ => True⟩
def wrappedRow (x : ℝ) : Prop := x ≤ 3

def duplicate (x : ℝ) : ℝ := x + x + x + x
def duplicateLet (x : ℝ) : ℝ :=
  let y := x + x + x + x + x + x + x + x
  y + y + y + y
def applyHelper (f : ℝ → ℝ) (x : ℝ) : ℝ := f x
def projectedDuplicate : (ℝ → ℝ) × ℝ := ((fun x => x + x + x + x), 0)
def aliasDuplicate (x : ℝ) : ℝ :=
  let f : ℝ → ℝ := fun y => y + y + y + y
  let localAlias := f
  localAlias (x + x + x + x + x + x + x + x)

end
end MorewTest.NLP.HelperFixtures
