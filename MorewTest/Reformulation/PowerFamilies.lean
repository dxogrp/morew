/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-! Complete finite geometric-mean and inverse-product workflows. -/

namespace MorewTest.Reformulation.PowerFamilies

open Morew Morew.Conic
noncomputable section

namespace GeometricMean

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    maximize t
    subject to
      domain : 0 ≤ x
      mean : t ≤ Fn.geoMean x

variable (n : ℕ) (hn : 0 < n)

include hn in
reformulation targeted : (source n) := by
  conic at mean

include hn in
reformulation ready : (source n) := by
  conic

example : GlobalEquiv (source n) (targeted n hn) := targeted.equiv n hn
example : GlobalEquiv (source n) (ready n hn) := ready.equiv n hn
example : (ready.conicForm n hn).data.toProblem = ready n hn :=
  (ready.conicForm n hn).represents
example : (ready.conicForm n hn).data.sense = .maximize := rfl
example : (ready.conicForm n hn).data.rowCount = 5 := rfl

reformulation singleton : (source 1) := by conic
reformulation pair : (source 2) := by conic
reformulation triple : (source 3) := by conic

example : IsConic singleton := singleton.isConic
example : IsConic pair := pair.isConic
example : IsConic triple := triple.isConic

end GeometricMean

namespace InverseProduct

def source (n : ℕ) (ε : Fin n → ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : ε ≤ x
      inverse : Fn.invProd x ≤ t

variable (n : ℕ) (hn : 0 < n) (ε : Fin n → ℝ) (hε : ∀ i, 0 < ε i)

include hn hε in
reformulation ready : (source n ε) := by
  conic

example : GlobalEquiv (source n ε) (ready n hn ε) := ready.equiv n hn ε hε
example : (ready.conicForm n hn ε).data.toProblem = ready n hn ε :=
  (ready.conicForm n hn ε).represents
example : (ready.conicForm n hn ε).data.sense = .minimize := rfl
example : (ready.conicForm n hn ε).data.rowCount = 4 := rfl

reformulation singleton : (source 1 (fun _ => 1)) := by conic
reformulation pair : (source 2 (fun _ => 1)) := by conic
reformulation triple : (source 3 (fun _ => 1)) := by conic

example : IsConic singleton := singleton.isConic
example : IsConic pair := pair.isConic
example : IsConic triple := triple.isConic

end InverseProduct

end
end MorewTest.Reformulation.PowerFamilies
