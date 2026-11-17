/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.DiagnosticsSupport
import Morew.Conic.Exponential
import MorewTest.CommandSupport

/-!
# Exponential rewrite diagnostics and atomic failure

Unsupported domains, atoms, and explicit certificates must not produce a
reformulated declaration, metadata, or private proof helpers. Typed tests check
individual obligations; these guards check the selected-label integration.
-/

namespace MorewTest.Reformulation.ExponentialFailures

open Morew

noncomputable section

elab "assert_exp_atomic% " nested:command : command =>
  MorewTest.elabNoNewDeclarations nested fun name => m!"failed exponential rewrite leaked auxiliary declaration {name}"

def source :=
  problem (x y t : ℝ)
    minimize t
    subject to
      exponential : Real.exp x ≤ t
      logarithm : t ≤ Real.log y

#guard_error_fragments ["constraint `logarithm`:"] in
assert_exp_atomic%
reformulation missingDomain : source certificate missingDomainAlias := by
  conic at exponential
  conic at logarithm

def nonneg :=
  problem (x t : ℝ)
    minimize t
    subject to
      domain : 0 ≤ x
      logarithm : t ≤ Real.log x

/-- error: constraint `logarithm`: -/
#guard_msgs (substring := true) in
reformulation zeroMargin : nonneg := by
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
      entropy : Fn.relEntr a b ≤ t

/-- error: constraint `entropy`: -/
#guard_msgs (substring := true) in
reformulation missingNonnegativity : entropyMissingNumeratorDomain := by
  conic at entropy

def entropyZeroDenominator :=
  problem (t : ℝ)
    minimize t
    subject to
      entropy : Fn.relEntr 0 0 ≤ t

/-- error: constraint `entropy`: -/
#guard_msgs (substring := true) in
reformulation closedCornerNeedsCustomRule : entropyZeroDenominator := by
  conic at entropy

def newAtomsMissingDomain :=
  problem (x y t : ℝ)
    minimize t
    subject to
      margin : 1 ≤ y
      entropy : t ≤ Real.negMulLog x
      namedEntropy : t ≤ Fn.entr x
      divergence : Fn.klDiv x y ≤ t

#guard_error_fragments ["constraint `entropy`:"] in
assert_exp_atomic%
reformulation entropyMissingNonnegativity : newAtomsMissingDomain := by
  conic at entropy

#guard_error_fragments ["constraint `namedEntropy`:"] in
assert_exp_atomic%
reformulation entrMissingNonnegativity : newAtomsMissingDomain := by
  conic at namedEntropy

#guard_error_fragments ["constraint `divergence`:"] in
assert_exp_atomic%
reformulation klMissingNonnegativity : newAtomsMissingDomain := by
  conic at divergence

def klNonnegativeDenominator :=
  problem (x y t : ℝ)
    minimize t
    subject to
      numerator : 0 ≤ x
      denominator : 0 ≤ y
      divergence : Fn.klDiv x y ≤ t

#guard_error_fragments ["constraint `divergence`:"] in
assert_exp_atomic%
reformulation klZeroMargin : klNonnegativeDenominator := by
  conic at divergence

def klStrictDenominator :=
  problem (x y t : ℝ)
    minimize t
    subject to
      numerator : 0 ≤ x
      denominator : 0 < y
      divergence : Fn.klDiv x y ≤ t

#guard_error_fragments ["constraint `divergence`:"] in
assert_exp_atomic%
reformulation klNoUniformMargin : klStrictDenominator := by
  conic at divergence

def newAtomsBoundary :=
  problem (t : ℝ)
    minimize t
    subject to
      entropy : t ≤ Real.negMulLog 0
      divergence : Fn.klDiv 0 0 ≤ t

-- A valid entropy rewrite followed by an invalid KL rewrite leaves no declarations.
#guard_error_fragments ["constraint `divergence`:"] in
assert_exp_atomic%
reformulation klZeroDenominator : newAtomsBoundary certificate klZeroDenominatorAlias := by
  conic at entropy
  conic at divergence

def newAtomsReverse :=
  problem (x y t : ℝ)
    minimize t
    subject to
      numerator : 0 ≤ x
      denominator : 1 ≤ y
      entropy : Real.negMulLog x ≤ t
      namedEntropy : Fn.entr x ≤ t
      divergence : t ≤ Fn.klDiv x y

#guard_error_fragments ["constraint `entropy`:"] in
assert_exp_atomic%
reformulation reversedEntropy : newAtomsReverse := by
  conic at entropy

#guard_error_fragments ["constraint `namedEntropy`:"] in
assert_exp_atomic%
reformulation reversedEntr : newAtomsReverse := by
  conic at namedEntropy using Morew.Conic.Exponential.entrHypograph

#guard_error_fragments ["constraint `divergence`:"] in
assert_exp_atomic%
reformulation reversedKL : newAtomsReverse := by
  conic at divergence using Morew.Conic.Exponential.klDivEpigraph

def newAtomsNonlinear :=
  problem (x t : ℝ)
    minimize t
    subject to
      numerator : 0 ≤ x ^ 2
      entropy : t ≤ Real.negMulLog (x ^ 2)
      divergence : Fn.klDiv (x ^ 2) 1 ≤ t

#guard_error_fragments ["constraint `entropy`:"] in
assert_exp_atomic%
reformulation nonaffineEntropy : newAtomsNonlinear := by
  conic at entropy

#guard_error_fragments ["constraint `divergence`:"] in
assert_exp_atomic%
reformulation nonaffineKL : newAtomsNonlinear := by
  conic at divergence

def sumMissingDomain :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    maximize t
    subject to
      entropy : t ≤ ∑ i, Fn.entr (x i)
      divergence : (∑ i, Fn.klDiv (x i) 1) ≤ t

#guard_error_fragments ["constraint `entropy`:"] in
assert_exp_atomic%
reformulation sumMissingNonnegativity : sumMissingDomain := by
  conic at entropy

#guard_error_fragments ["constraint `divergence`:"] in
assert_exp_atomic%
reformulation sumKLMissingNonnegativity : sumMissingDomain := by
  conic at divergence

def sumNonlinear :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    maximize t
    subject to
      domain : ∀ i, 0 ≤ x i ^ 2
      entropy : t ≤ ∑ i, Fn.entr (x i ^ 2)
      divergence : (∑ i, Fn.klDiv (x i ^ 2) 1) ≤ t

#guard_error_fragments ["constraint `entropy`:"] in
assert_exp_atomic%
reformulation sumNonaffineCoordinates : sumNonlinear := by
  conic at entropy

#guard_error_fragments ["constraint `divergence`:"] in
assert_exp_atomic%
reformulation sumKLNonaffineCoordinates : sumNonlinear := by
  conic at divergence

def unsupportedSums :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : ∀ i, 0 ≤ x i
      reversed : (∑ i, Fn.entr (x i)) ≤ t
      mixed : t ≤ ∑ i, (Fn.entr (x i) + Real.exp (x i))

#guard_error_fragments ["constraint `reversed`:"] in
assert_exp_atomic%
reformulation sumReversedPolarity : unsupportedSums := by
  conic at reversed

#guard_error_fragments ["constraint `mixed`:"] in
assert_exp_atomic%
reformulation sumUnrelatedSummands : unsupportedSums := by
  conic at mixed

def empty :=
  problem (xs : Fin 0 → ℝ) (t : ℝ)
    minimize t
    subject to
      lse : Fn.logSumExp xs ≤ t

/-- error: constraint `lse`: -/
#guard_msgs (substring := true) in
reformulation emptyLSE : empty := by
  conic at lse

section

variable (n : ℕ)

def symbolic :=
  problem (xs : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      lse : Fn.logSumExp xs ≤ t

/-- error: constraint `lse`: -/
#guard_msgs (substring := true) in
reformulation unavailableNonempty : (symbolic n) := by
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

/-- error: constraint `exponential`: expected ConstraintRepr, GraphRepr, EpigraphRepr, or HypographRepr; reduced type is ℝ -/
#guard_msgs in
reformulation invalidExplicitRule : source := by
  conic at exponential using (0 : ℝ)

def scalarSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      exponential : Real.exp x ≤ t

def uncertifiedTarget : ConstraintRepr
    (fun point : ℝ × ℝ => Real.exp point.1 ≤ point.2) :=
  ConstraintRepr.ofIff (fun point : ℝ × ℝ => Real.exp point.1 ≤ point.2)
    (fun _ => Iff.rfl)

-- The exact certificate has a non-affine target, so explicit selection fails.
#guard_error_fragments ["constraint `exponential`: generated row:"] in
assert_exp_atomic%
reformulation explicitCannotFallback : scalarSource certificate explicitCannotFallbackAlias := by
  conic at exponential using uncertifiedTarget

def liftedSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      softplus : Fn.softplus x ≤ t
      logarithm : t ≤ Real.log x

#guard_error_fragments ["constraint `logarithm`:"] in
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

run_cmd do
  let env ← Lean.getEnv
  for name in #[`missingDomain, `zeroMargin, `noUniformMargin, `noArithmeticSearch,
      `selectedCannotSupplyMargin, `missingNonnegativity, `closedCornerNeedsCustomRule,
      `emptyLSE, `unavailableNonempty, `reversedExponential, `exponentialEquality,
      `nonaffineCoordinate, `nonaffineLogArgument, `unsupportedSubset, `incompatibleOrder,
      `invalidExplicitRule, `explicitCannotFallback, `failureAfterAuxiliary, `stale] do
    let full := `MorewTest.Reformulation.ExponentialFailures ++ name
    if env.contains full || env.contains (full ++ `equiv) ||
        (Syntax.getProblemView? env full).isSome then
      Lean.throwError "failed exponential rewrite emitted {full}"

end
end MorewTest.Reformulation.ExponentialFailures
