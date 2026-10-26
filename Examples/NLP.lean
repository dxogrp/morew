/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Command

/-!
# Exact smooth replacements of nonsmooth constraints

`nlp at label` replaces a direct nonsmooth bound by exactly equivalent smooth
constraints. `using` selects an explicit exact representation.

For a nested term, first expose it with an occurrence epigraph or hypograph
step. Generated constraint labels replace the selected label in place. Finite
coordinate rows remain grouped, including when their dimension is symbolic.
-/

namespace Morew.Examples.NLP

open Morew
noncomputable section

def nonlinear :=
  problem (x y t : ℝ)
    minimize (x * y - 1) ^ 2 + t
    subject to
      error : |x ^ 2 - y| ≤ t
      budget : |x| + y ^ 2 ≤ 10

reformulation smoothConstraints : nonlinear := by
  nlp at error using Exact.absEpigraph
  epigraph a at (|x|) in budget as magnitude
  nlp at magnitude

#printp smoothConstraints
example : GlobalEquivalence nonlinear smoothConstraints := smoothConstraints.equivalence

def normBound (n : ℕ) :=
  problem (v : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      norm : ‖WithLp.toLp 2 v‖ ≤ t

variable (n : ℕ)

reformulation squaredNorm : (normBound n) := by
  nlp at norm

#printp squaredNorm
example : GlobalEquivalence (normBound n) (squaredNorm n) :=
  squaredNorm.equivalence n

end
end Morew.Examples.NLP
