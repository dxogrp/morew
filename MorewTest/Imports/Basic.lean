/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic

assert_not_imported Morew.Elab.Conic.Plan
assert_not_imported Morew.Elab.Conic.Terminal
assert_not_imported Morew.Elab.Conic.Rules
assert_not_imported Morew.Elab.Reformulation.Conic.Rewrite
assert_not_imported Morew.Elab.Reformulation.Conic.Terminal
assert_not_imported Morew.Elab.Reformulation.Conic.View
assert_not_imported Morew.Elab.NLP.Rewrite
assert_not_imported Morew.Elab.NLP.Terminal
assert_not_imported Morew.Elab.NLP.Rules
assert_not_imported Morew.Elab.Reformulation.NLP.Rewrite
assert_not_imported Morew.Elab.Reformulation.NLP.Terminal
assert_not_imported Morew.Conic.PSD.NuclearNorm
assert_not_imported Morew.Conic.PSD.LogDet

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 0 do
    Lean.throwError "unexpected selective-import presentation providers"

namespace MorewTest.Imports.Basic
open Morew
noncomputable section

def source := problem (x : ℝ) minimize x subject to tag : True

reformulation generic : source certificate aliasProof := by
  substitute x := u
  derive copy : True using (by intro _ _; trivial)
  rename copy to copied
  remove at copied
  epigraph t

example : GlobalEquivalence source generic := aliasProof
example (u t : ℝ) : generic.feasible (u, t) ↔ True ∧ u ≤ t := Iff.rfl

def coverage : GlobalImprovement source (source.addConstraint (fun _ => True)) where
  map point := ⟨point.1, point.2, True.intro⟩
  objective_le _ := le_rfl

reformulation restricted : source := by
  restrict kept : True using coverage
  remove at kept
example : restricted = source := rfl

reformulation selectedSubstitution : source := by
  substitute x := u via Morew.Substitution.identity
example : GlobalEquivalence source selectedSubstitution := selectedSubstitution.equivalence

def minimum := problem (x : ℝ) minimize x ^ 2 + x
reformulation occurrenceUpper : minimum := by epigraph t at (x ^ 2)
example : GlobalEquivalence minimum occurrenceUpper := occurrenceUpper.equivalence

def maximum := problem (x : ℝ) maximize x ^ 2 + x
reformulation objectiveLower : maximum := by hypograph t
reformulation occurrenceLower : maximum := by hypograph t at (x ^ 2)
example : GlobalEquivalence maximum objectiveLower := objectiveLower.equivalence
example : GlobalEquivalence maximum occurrenceLower := occurrenceLower.equivalence

/--
info: problem (u t : ℝ)
  minimize t
  subject to
    tag : True
    epigraph_t : u ≤ t
-/
#guard_msgs in
#printp generic

/-- error: reformulation step is unavailable; import Morew.Reformulation.Conic -/
#guard_msgs in
reformulation missingConic : source := by conic
/-- error: reformulation step is unavailable; import Morew.Reformulation.Conic -/
#guard_msgs in
reformulation missingConicAt : source := by conic at tag
/-- error: reformulation step is unavailable; import Morew.Reformulation.NLP -/
#guard_msgs in
reformulation missingNLP : source := by nlp
/-- error: reformulation step is unavailable; import Morew.Reformulation.NLP -/
#guard_msgs in
reformulation missingNLPAt : source := by nlp at tag
assert_not_exists missingConic missingConicAt missingNLP missingNLPAt
end
end MorewTest.Imports.Basic
