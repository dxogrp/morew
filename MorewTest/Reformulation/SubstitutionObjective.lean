/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-! Exponential substitutions in a finite-sum objective, before and after epigraph rewriting. -/

namespace MorewTest.Reformulation.SubstitutionObjective

open Morew
noncomputable section

def source (a b c : Fin m → ℝ) :=
  problem (x y : ℝ)
    minimize ∑ i, (a i * Real.log x + b i * Real.log y - c i) ^ 2
    subject to
      positiveX : 0 < x
      positiveY : 0 < y

variable (a b c : Fin m → ℝ)

-- These commands use the default heartbeat limit.
reformulation first : (source a b c) := by
  substitute x := Real.exp u

example : GlobalEquiv (source a b c) (first a b c) := first.equiv a b c
example (u y : ℝ) : (first a b c).objective (u, y) =
    ∑ i, (a i * u + b i * Real.log y - c i) ^ 2 := rfl
example (u y : ℝ) : (first a b c).feasible (u, y) ↔ 0 < y := Iff.rfl

reformulation logarithmic : (source a b c) := by
  substitute x := Real.exp u
  substitute y := Real.exp v

example : GlobalEquiv (source a b c) (logarithmic a b c) := logarithmic.equiv a b c
example (u v : ℝ) : (logarithmic a b c).objective (u, v) =
    ∑ i, (a i * u + b i * v - c i) ^ 2 := rfl
example (u v : ℝ) : (logarithmic a b c).feasible (u, v) := trivial

reformulation conicAfterSubstitution : (source a b c) := by
  substitute x := Real.exp u
  substitute y := Real.exp v
  epigraph t as residualBound
  conic at residualBound
  conic

example : GlobalEquiv (source a b c) (conicAfterSubstitution a b c) :=
  conicAfterSubstitution.equiv a b c
example : IsConic (conicAfterSubstitution a b c) :=
  conicAfterSubstitution.isConic a b c
example : (conicAfterSubstitution.conicForm a b c).data.toProblem =
    conicAfterSubstitution a b c := (conicAfterSubstitution.conicForm a b c).represents

reformulation epigraphFirst : (source a b c) := by
  epigraph t as residualBound
  substitute x := Real.exp u
  substitute y := Real.exp v
  conic at residualBound
  conic

example : GlobalEquiv (source a b c) (epigraphFirst a b c) := epigraphFirst.equiv a b c
example : IsConic (epigraphFirst a b c) := epigraphFirst.isConic a b c
example : (epigraphFirst.conicForm a b c).data.toProblem = epigraphFirst a b c :=
  (epigraphFirst.conicForm a b c).represents

end
end MorewTest.Reformulation.SubstitutionObjective
