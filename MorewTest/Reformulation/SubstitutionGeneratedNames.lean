import Morew.Reformulation.Command

/-!
# Substitution through displayed generated names

Replacement elaboration resolves hygienic model bindings and retains those
identities when constructing the semantic map and substituted presentation.
-/

namespace MorewTest.Reformulation.SubstitutionGeneratedNames

open Morew
noncomputable section

macro "shiftedModel" : term =>
  `(problem (x y : ℝ)
    let loss := x ^ 2
    let shift := y + 1
    minimize loss)

def macroSource := shiftedModel

def macroCoverage : FeasibleSurjection macroSource
    (fun point : ℝ × ℝ => (point.1 + (point.2 + 1), point.2)) where
  preimage point := (point.1.1 - (point.1.2 + 1), point.1.2)
  rightInverse point := by simp

-- The inserted expression must retain y's macro scope after expanding shift.
reformulation macroTarget : macroSource := by
  substitute x := u + shift using macroCoverage

example : GlobalEquivalence macroSource macroTarget := macroTarget.equivalence
example (u y : ℝ) : macroTarget.objective (u, y) = (u + (y + 1)) ^ 2 := rfl

/--
info: problem (u y : ℝ)
  let loss := (u + (y + 1)) ^ 2
  let shift := y + 1
  minimize loss
-/
#guard_msgs in
#printp macroTarget

-- A lexical binder with the same spelling still shadows the exposed alias.
reformulation shadowed : macroSource := by
  substitute x := (fun shift : ℝ => shift) u + shift using macroCoverage

example : GlobalEquivalence macroSource shadowed := shadowed.equivalence
example (u y : ℝ) : shadowed.objective (u, y) = (u + (y + 1)) ^ 2 := rfl

/-- error: substitution replacement uses model-local definition `loss`, which depends on the decision variable being replaced -/
#guard_msgs (substring := true) in
reformulation dependentReplacement : macroSource := by
  substitute x := u + loss using macroCoverage

def square := problem (x : ℝ) minimize x ^ 2

reformulation squareLift : square := by
  epigraph a at (x ^ 2)

def generatedCoverage : FeasibleSurjection squareLift
    (fun point : ℝ × ℝ => (point.1 + point.2, point.2)) where
  preimage point := (point.1.1 - point.1.2, point.1.2)
  rightInverse point := by simp

-- No model-local definitions are present: a's identity must still be replayed.
reformulation generatedTarget : squareLift := by
  substitute x := u + a using generatedCoverage

example : GlobalEquivalence squareLift generatedTarget := generatedTarget.equivalence
example (u a : ℝ) : generatedTarget.objective (u, a) = a := rfl
example (u a : ℝ) : generatedTarget.feasible (u, a) ↔ (u + a) ^ 2 ≤ a := Iff.rfl

reformulation generatedInScript : square := by
  epigraph a at (x ^ 2)
  substitute x := u + a using (by
    refine {
      preimage := fun point => (point.1.1 - point.1.2, point.1.2)
      rightInverse := ?_ }
    intro point
    simp)

example : GlobalEquivalence square generatedInScript := generatedInScript.equivalence
example (u a : ℝ) : generatedInScript.feasible (u, a) ↔ (u + a) ^ 2 ≤ a := Iff.rfl

structure Offset where
  value : ℝ

macro "recordModel" : term =>
  `(problem (x y : ℝ)
    let shift : Offset := ⟨y + 1⟩
    minimize x ^ 2)

def recordSource := recordModel

def recordCoverage : FeasibleSurjection recordSource
    (fun point : ℝ × ℝ => (point.1 + (point.2 + 1), point.2)) where
  preimage point := (point.1.1 - (point.1.2 + 1), point.1.2)
  rightInverse point := by simp

-- A named projection is part of an existing binding, not a new decision name.
reformulation projected : recordSource := by
  substitute x := u + shift.value using recordCoverage

example : GlobalEquivalence recordSource projected := projected.equivalence
example (u y : ℝ) : projected.objective (u, y) = (u + (y + 1)) ^ 2 := rfl

private def shift : ℝ := 7

-- Plain user syntax prefers the displayed model binding over this global.
reformulation localWins : macroSource := by
  substitute x := u + shift using macroCoverage

example : GlobalEquivalence macroSource localWins := localWins.equivalence
example (u y : ℝ) : localWins.objective (u, y) = (u + (y + 1)) ^ 2 := rfl

macro "withCapturedShift " value:term : term => `($value + shift)

def capturedCoverage : FeasibleSurjection macroSource
    (fun point : ℝ × ℝ => (point.1 + 7, point.2)) where
  preimage point := (point.1.1 - 7, point.1.2)
  rightInverse point := by simp

-- A macro's captured global shift is not the model-local shift := y + 1.
reformulation captured : macroSource := by
  substitute x := withCapturedShift u using capturedCoverage

example : GlobalEquivalence macroSource captured := captured.equivalence
example (u y : ℝ) : captured.objective (u, y) = (u + 7) ^ 2 := rfl

end
end MorewTest.Reformulation.SubstitutionGeneratedNames
