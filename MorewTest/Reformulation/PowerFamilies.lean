/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics

/-!
# Complete finite power-cone workflows

The norm rules deliberately share automatic discovery. Explicit selection
chooses the SOC or power representation when both certify the L2 source.
-/

namespace MorewTest.Reformulation.PowerFamilies

open Morew Morew.Conic
open scoped ENNReal
noncomputable section

def normSource (n : ℕ) (p : ℝ≥0∞) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      bound : ‖WithLp.toLp p x‖ ≤ t

namespace L2
variable (n : ℕ)

#guard_error_fragments ["ambiguous exact conic rules", "Morew.Conic.Power.normEpigraph",
    "Morew.Conic.SecondOrder.normEpigraph", "using"] in
reformulation ambiguousTargeted : (normSource n 2) := by
  conic at bound

#guard_error_fragments ["ambiguous exact conic rules", "Morew.Conic.Power.normEpigraph",
    "Morew.Conic.SecondOrder.normEpigraph", "using"] in
reformulation ambiguousTerminal : (normSource n 2) := by
  conic

assert_not_exists ambiguousTargeted ambiguousTargeted.equivalence ambiguousTerminal
  ambiguousTerminal.equivalence ambiguousTerminal.conicForm

reformulation soc : (normSource n 2) := by
  conic at bound using Conic.SecondOrder.normEpigraph
  conic

reformulation powerTargeted : (normSource n 2) := by
  conic at bound using Conic.Power.normEpigraph

reformulation power : (powerTargeted n) := by
  conic

example : GlobalEquivalence (normSource n 2) (soc n) := soc.equivalence n
example : GlobalEquivalence (normSource n 2) (power n) :=
  (powerTargeted.equivalence n).trans (power.equivalence n)
example : GlobalEquivalence (soc n) (power n) :=
  (soc.equivalence n).symm.trans
    ((powerTargeted.equivalence n).trans (power.equivalence n))
example : Conic.Form (soc n) := soc.conicForm n
example : Conic.Form (power n) := power.conicForm n
example : (soc.conicForm n).data.toProblem = soc n := (soc.conicForm n).represents
example : (power.conicForm n).data.toProblem = power n := (power.conicForm n).represents
example : IsConic (soc n) := soc.isConic n
example : IsConic (power n) := power.isConic n
example : (soc.conicForm n).data.rowCount = 1 := rfl
example : (power.conicForm n).data.rowCount = 3 := rfl
example (x r : Fin n → ℝ) (t : ℝ) : (powerTargeted n).feasible ((x, t), r) ↔
    0 ≤ t ∧ (∑ i, r i) ≤ t ∧ ∀ i, (r i, t, x i) ∈ POW (1 / 2 : ℝ) := Iff.rfl
example (x r : Fin 0 → ℝ) : ¬ (powerTargeted 0).feasible ((x, -1), r) := by
  intro h
  have := h.1
  norm_num at this

/--
info: problem (x : Fin n → ℝ) (t : ℝ)
  minimize t
  subject to
    bound_conic_1 : (t, x) ∈ SOC n
-/
#guard_msgs in
#printp soc

/--
info: problem (x : Fin n → ℝ) (t : ℝ) (bound_aux : Fin n → ℝ)
  minimize t
  subject to
    bound_conic_1 : t ∈ ℝ₊
    bound_conic_2 : t - ∑ i, bound_aux i ∈ ℝ₊
    bound_conic_3 : ∀ (i : Fin n), (bound_aux i, t, x i) ∈ POW (1 / 2)
-/
#guard_msgs in
#printp power

end L2

namespace Exponents
variable (n : ℕ)

reformulation one : (normSource n 1) := by
  conic

reformulation threeHalves : (normSource n (3 / 2)) := by
  conic

reformulation three : (normSource n 3) := by
  conic

example : GlobalEquivalence (normSource n 1) (one n) := one.equivalence n
example : GlobalEquivalence (normSource n (3 / 2)) (threeHalves n) := threeHalves.equivalence n
example : (threeHalves.conicForm n).data.rowCount = 3 := rfl
example : (three.conicForm n).data.rowCount = 3 := rfl

/--
info: problem (x : Fin n → ℝ) (t : ℝ) (bound_aux : Fin n → ℝ)
  minimize t
  subject to
    bound_conic_1 : t ∈ ℝ₊
    bound_conic_2 : t - ∑ i, bound_aux i ∈ ℝ₊
    bound_conic_3 : ∀ (i : Fin n), (bound_aux i, t, x i) ∈ POW (2 / 3)
-/
#guard_msgs in
#printp threeHalves

variable (p : ℝ≥0∞) (hp : 1 < p.toReal)

include hp in
reformulation symbolic : (normSource n p) := by
  conic

example : GlobalEquivalence (normSource n p) (symbolic n p hp) := symbolic.equivalence n p hp
example : Conic.Form (symbolic n p hp) := symbolic.conicForm n p hp

variable (q : ℝ) (hq : 1 < q)

include hq in
reformulation realExponent : (normSource n (ENNReal.ofReal q)) := by
  conic

example : GlobalEquivalence (normSource n (ENNReal.ofReal q)) (realExponent n q hq) :=
  realExponent.equivalence n q hq

variable (hsqrt : 1 < Real.sqrt 2)

include hsqrt in
reformulation irrational : (normSource n (ENNReal.ofReal (Real.sqrt 2))) := by
  conic

example : Conic.Form (irrational n Real.one_lt_sqrt_two) :=
  irrational.conicForm n Real.one_lt_sqrt_two

end Exponents

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

example : GlobalEquivalence (source n) (targeted n hn) := targeted.equivalence n hn
example : GlobalEquivalence (source n) (ready n hn) := ready.equivalence n hn
example : Conic.Form (ready n hn) := ready.conicForm n hn
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

example : GlobalEquivalence (source n ε) (ready n hn ε) := ready.equivalence n hn ε hε
example : Conic.Form (ready n hn ε) := ready.conicForm n hn ε
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
