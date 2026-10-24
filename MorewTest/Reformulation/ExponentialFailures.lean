/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import Morew.Conic.Exponential

/-!
# Exponential rewrite diagnostics and atomic failure

Unsupported domains, atoms, and explicit certificates must not produce a
reformulated declaration, metadata, or private proof helpers. Typed tests check
individual obligations; these guards check the selected-label integration.
-/

namespace MorewTest.Reformulation.ExponentialFailures

open Morew

noncomputable section

elab "assert_exp_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  for (name, _) in after.constants.toList do
    unless before.contains name do
      Lean.throwError "failed exponential rewrite leaked auxiliary declaration {name}"

def source :=
  problem (x y t : ℝ)
    minimize t
    subject to
      exponential : Real.exp x ≤ t
      logarithm : t ≤ Real.log y

/-- error: constraint `logarithm`: -/
#guard_msgs (substring := true) in
assert_exp_atomic%
reformulation missingDomain : source certificate missingDomainAlias := by
  conic at exponential
  conic at logarithm

def nonnegative :=
  problem (x t : ℝ)
    minimize t
    subject to
      domain : 0 ≤ x
      logarithm : t ≤ Real.log x

/-- error: constraint `logarithm`: -/
#guard_msgs (substring := true) in
reformulation zeroMargin : nonnegative := by
  conic at logarithm

def strictlyPositive :=
  problem (x t : ℝ)
    minimize t
    subject to
      domain : 0 < x
      logarithm : t ≤ Real.log x

/-- error: constraint `logarithm`: -/
#guard_msgs (substring := true) in
reformulation noUniformMargin : strictlyPositive := by
  conic at logarithm

def derived :=
  problem (x y t : ℝ)
    minimize t
    subject to
      lower : 1 ≤ y
      comparison : y ≤ x
      logarithm : t ≤ Real.log x

/-- error: constraint `logarithm`: -/
#guard_msgs (substring := true) in
reformulation noArithmeticSearch : derived := by
  conic at logarithm

def selectedConjunction :=
  problem (x t : ℝ)
    minimize t
    subject to
      bound : 1 ≤ x ∧ t ≤ Real.log x

/-- error: constraint `bound`: -/
#guard_msgs (substring := true) in
reformulation selectedCannotSupplyMargin : selectedConjunction := by
  conic at bound

def entropyMissingNumeratorDomain :=
  problem (a b t : ℝ)
    minimize t
    subject to
      margin : 1 ≤ b
      entropy : Fn.relativeEntropy a b ≤ t

/-- error: constraint `entropy`: -/
#guard_msgs (substring := true) in
reformulation missingNonnegativity : entropyMissingNumeratorDomain := by
  conic at entropy

def entropyZeroDenominator :=
  problem (t : ℝ)
    minimize t
    subject to
      entropy : Fn.relativeEntropy 0 0 ≤ t

/-- error: constraint `entropy`: -/
#guard_msgs (substring := true) in
reformulation closedCornerNeedsCustomRule : entropyZeroDenominator := by
  conic at entropy

def empty :=
  problem (xs : Fin 0 → ℝ) (t : ℝ)
    minimize t
    subject to
      lse : Fn.logSumExp xs ≤ t

/-- error: constraint `lse`: -/
#guard_msgs (substring := true) in
reformulation emptyLSE : empty := by
  conic at lse

class Dimension where
  size : ℕ

section
variable [Dimension]

def symbolic :=
  problem (xs : Fin Dimension.size → ℝ) (t : ℝ)
    minimize t
    subject to
      lse : Fn.logSumExp xs ≤ t

/-- error: constraint `lse`: -/
#guard_msgs (substring := true) in
reformulation unavailableNonempty : symbolic := by
  conic at lse

end

def reverse :=
  problem (x t : ℝ)
    minimize t
    subject to
      bound : t ≤ Real.exp x

/-- error: constraint `bound`: -/
#guard_msgs (substring := true) in
reformulation reversedExponential : reverse := by
  conic at bound

def equality :=
  problem (x t : ℝ)
    minimize t
    subject to
      bound : Real.exp x = t

/-- error: constraint `bound`: -/
#guard_msgs (substring := true) in
reformulation exponentialEquality : equality := by
  conic at bound

def nonlinear :=
  problem (x t : ℝ)
    minimize t
    subject to
      bound : Fn.softplus (x ^ 2) ≤ t

/-- error: constraint `bound`: -/
#guard_msgs (substring := true) in
reformulation nonaffineCoordinate : nonlinear := by
  conic at bound

def nonlinearMargin :=
  problem (x t : ℝ)
    minimize t
    subject to
      margin : 1 ≤ x ^ 2
      bound : t ≤ Real.log (x ^ 2)

/-- error: constraint `bound`: -/
#guard_msgs (substring := true) in
reformulation nonaffineLogArgument : nonlinearMargin := by
  conic at bound

def subset :=
  problem (xs : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      lse : Real.log (∑ i ∈ ({0} : Finset (Fin 2)), Real.exp (xs i)) ≤ t

/-- error: constraint `lse`: -/
#guard_msgs (substring := true) in
reformulation unsupportedSubset : subset := by
  conic at lse

def fakeOrder :=
  problem (x t : ℝ)
    minimize t
    subject to
      bound : @LE.le ℝ ⟨fun _ _ => True⟩ (Real.exp x) t

/-- error: constraint `bound`: -/
#guard_msgs (substring := true) in
reformulation incompatibleOrder : fakeOrder := by
  conic at bound

/-- error: constraint `exponential`: expected an ExactConstraintLift -/
#guard_msgs (substring := true) in
reformulation invalidExplicitRule : source := by
  conic at exponential using (0 : ℝ)

def scalarSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      exponential : Real.exp x ≤ t

def uncertifiedTarget : ExactConstraintLift
    (fun point : ℝ × ℝ => Real.exp point.1 ≤ point.2) :=
  ExactConstraintLift.ofIff (fun point : ℝ × ℝ => Real.exp point.1 ≤ point.2)
    (fun _ => Iff.rfl)

-- This certificate is mathematically valid, but its unlowered target is not
-- affine. The explicit request must fail instead of running the automatic atom.
/-- error: constraint `exponential`: generated row: -/
#guard_msgs (substring := true) in
assert_exp_atomic%
reformulation explicitCannotFallback : scalarSource certificate explicitCannotFallbackAlias := by
  conic at exponential using uncertifiedTarget

def liftedSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      softplus : Fn.softplus x ≤ t
      logarithm : t ≤ Real.log x

/-- error: constraint `logarithm`: -/
#guard_msgs (substring := true) in
assert_exp_atomic%
reformulation failureAfterAuxiliary : liftedSource certificate failureAfterAuxiliaryAlias := by
  conic at softplus
  conic at logarithm

/-- error: unknown or stale constraint label `exponential` -/
#guard_msgs in
assert_exp_atomic%
reformulation stale : source := by
  conic at exponential
  conic at exponential

/-- error: unknown or stale constraint label `absent` -/
#guard_msgs in
reformulation unknown : source := by
  conic at absent

run_cmd do
  let env ← Lean.getEnv
  for name in #[`missingDomain, `zeroMargin, `noUniformMargin, `noArithmeticSearch,
      `selectedCannotSupplyMargin, `missingNonnegativity, `closedCornerNeedsCustomRule,
      `emptyLSE, `unavailableNonempty, `reversedExponential, `exponentialEquality,
      `nonaffineCoordinate, `nonaffineLogArgument, `unsupportedSubset, `incompatibleOrder,
      `invalidExplicitRule, `explicitCannotFallback, `failureAfterAuxiliary, `stale, `unknown] do
    let full := `MorewTest.Reformulation.ExponentialFailures ++ name
    if env.contains full || env.contains (full ++ `equivalence) ||
        (Syntax.getProblemView? env full).isSome then
      Lean.throwError "failed exponential rewrite emitted {full}"

end
end MorewTest.Reformulation.ExponentialFailures
