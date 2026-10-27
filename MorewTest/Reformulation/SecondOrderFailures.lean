/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics

/-!
# Second-order failure diagnostics and atomicity

Unsupported bounds and missing denominator margins leave no declarations or
presentation metadata behind, including after a successful earlier rewrite.
-/

namespace MorewTest.Reformulation.SecondOrderFailures

open Morew

noncomputable section

def source :=
  problem (x y t : ℝ)
    minimize t
    subject to
      square : x ^ 2 ≤ t
      ratio : x ^ 2 / y ≤ t

#guard_error_fragments [
  "constraint `ratio`: no registered exact conic rule was fully certified:",
  "Morew.Conic.SecondOrder.squareDivEpigraph: registered conic rewrite was not certified: missing positive constant margin"] in
reformulation missing : source certificate missingAlias := by
  conic at square
  conic at ratio

run_cmd do
  let env ← Lean.getEnv
  for name in #[`missing, `missing.equivalence, `missingAlias] do
    let full := `MorewTest.Reformulation.SecondOrderFailures ++ name
    if env.contains full || (Syntax.getProblemView? env full).isSome then
      Lean.throwError "failed second-order rewrite emitted {full}"

def nonnegative :=
  problem (x y t : ℝ)
    minimize t
    subject to
      margin : 0 ≤ y
      ratio : x ^ 2 / y ≤ t

#guard_error_fragments [
  "constraint `ratio`: no registered exact conic rule was fully certified:",
  "Morew.Conic.SecondOrder.squareDivEpigraph: registered conic rewrite was not certified: missing positive constant margin"] in
reformulation zeroMargin : nonnegative := by
  conic at ratio

def strictlyPositive :=
  problem (x y t : ℝ)
    minimize t
    subject to
      positive : 0 < y
      ratio : x ^ 2 / y ≤ t

#guard_error_fragments [
  "constraint `ratio`: no registered exact conic rule was fully certified:",
  "Morew.Conic.SecondOrder.squareDivEpigraph: registered conic rewrite was not certified: missing positive constant margin"] in
reformulation noUniformMargin : strictlyPositive := by
  conic at ratio

def derived :=
  problem (x y z t : ℝ)
    minimize t
    subject to
      lower : 1 ≤ z
      comparison : z ≤ y
      ratio : x ^ 2 / y ≤ t

#guard_error_fragments [
  "constraint `ratio`: no registered exact conic rule was fully certified:",
  "Morew.Conic.SecondOrder.squareDivEpigraph: registered conic rewrite was not certified: missing positive constant margin"] in
reformulation noArithmeticSearch : derived := by
  conic at ratio

def reverse :=
  problem (x t : ℝ)
    minimize t
    subject to
      bound : t ≤ x ^ 2

/-- error: constraint `bound`: no supported registered conic rule matches the entire selected predicate and bound polarity -/
#guard_msgs (substring := true) in
reformulation reversedSquare : reverse := by
  conic at bound

def equality :=
  problem (x t : ℝ)
    minimize t
    subject to
      bound : x ^ 2 = t

/-- error: constraint `bound`: no supported registered conic rule matches the entire selected predicate and bound polarity -/
#guard_msgs (substring := true) in
reformulation squareEquality : equality := by
  conic at bound

def nonlinear :=
  problem (x t : ℝ)
    minimize t
    subject to
      bound : (Real.exp x) ^ 2 ≤ t

#guard_error_fragments [
  "constraint `bound`: no registered exact conic rule was fully certified:",
  "Morew.Conic.SecondOrder.squareEpigraph: generated row: constraint: cone coordinates"] in
reformulation nonlinearCoordinate : nonlinear := by
  conic at bound

def nonlinearDenominator :=
  problem (x y t : ℝ)
    minimize t
    subject to
      margin : 1 ≤ y ^ 2
      ratio : x ^ 2 / y ^ 2 ≤ t

#guard_error_fragments [
  "constraint `ratio`: no registered exact conic rule was fully certified:",
  "Morew.Conic.SecondOrder.squareDivEpigraph: generated row: constraint: cone coordinates"] in
reformulation nonlinearRatio : nonlinearDenominator := by
  conic at ratio

def emptyRatio :=
  problem (x : Fin 0 → ℝ) (y t : ℝ)
    minimize t
    subject to
      ratio : (∑ i, x i ^ 2) / y ≤ t

#guard_error_fragments [
  "constraint `ratio`: no registered exact conic rule was fully certified:",
  "Morew.Conic.SecondOrder.sumSquaresDivEpigraph: registered conic rewrite was not certified: missing positive constant margin"] in
reformulation emptyStillRequiresMargin : emptyRatio := by
  conic at ratio

/-- error: constraint `square`: expected ExactConstraintLift -/
#guard_msgs (substring := true) in
reformulation invalidExplicitRule : source := by
  conic at square using (0 : ℝ)

/-- error: unknown or stale constraint label `square` -/
#guard_msgs in
reformulation stale : source := by
  conic at square
  conic at square

/-- error: unknown or stale constraint label `absent` -/
#guard_msgs in
reformulation unknown : source := by
  conic at absent

end
end MorewTest.Reformulation.SecondOrderFailures
