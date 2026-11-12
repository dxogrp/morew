/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.NLP
import MorewTest.DiagnosticsSupport
import MorewTest.CommandSupport

/-! # Targeted NLP diagnostics and transactional failure -/

namespace MorewTest.Reformulation.NLPFailures

open Morew

noncomputable section

def source := problem (x : ℝ) minimize x subject to bound : |x| ≤ 3

/-- error: unknown or stale constraint label `missing` -/
#guard_msgs in
reformulation unknown : source := by
  nlp at missing

/-- error: unknown or stale constraint label `bound` -/
#guard_msgs in
reformulation stale : source := by
  nlp at bound
  nlp at bound

def reverseSource := problem (x : ℝ) minimize x subject to reversed : 1 ≤ |x|

/-- error: constraint `reversed`: no supported exact NLP rule -/
#guard_msgs (substring := true) in
reformulation reverse : reverseSource := by
  nlp at reversed

def equalitySource := problem (x : ℝ) minimize x subject to equality : |x| = 1

/-- error: constraint `equality`: no supported exact NLP rule -/
#guard_msgs (substring := true) in
reformulation equality : equalitySource := by
  nlp at equality

def nestedSource := problem (x : ℝ) minimize x subject to nested : |x| + x ^ 2 ≤ 3

/-- error: constraint `nested`: no supported exact NLP rule -/
#guard_msgs (substring := true) in
reformulation nested : nestedSource := by
  nlp at nested

def remainingSource := problem (x : ℝ) minimize x subject to remaining : max |x| x ≤ 3

/-- error: constraint `remaining`: generated row certification failed -/
#guard_msgs (substring := true) in
reformulation remaining : remainingSource := by
  nlp at remaining

def domainSource := problem (x : ℝ) minimize x subject to logarithm : |Real.log x| ≤ 3

/-- error: constraint `logarithm`: generated row certification failed -/
#guard_msgs (substring := true) in
reformulation missingDomain : domainSource := by
  nlp at logarithm

def smoothSource := problem (x : ℝ) minimize x subject to smooth : x ^ 2 ≤ 3

/-- error: constraint `smooth`: no supported exact NLP rule -/
#guard_msgs (substring := true) in
reformulation noIdentity : smoothSource := by
  nlp at smooth

def ambiguousSource :=
  problem (x : ℝ) minimize x subject to bound : max (0 : ℝ) 1 ≤ min 2 3

/-- error: constraint `bound`: ambiguous exact NLP rules: Morew.Rewrite.maxEpigraph, Morew.Rewrite.minHypograph -/
#guard_msgs (substring := true) in
reformulation ambiguous : ambiguousSource := by
  nlp at bound

reformulation selected : ambiguousSource := by
  nlp at bound using Rewrite.maxEpigraph

example : GlobalEquiv ambiguousSource selected := selected.equiv

/-- error: constraint `bound`: expected ConstraintRepr -/
#guard_msgs (substring := true) in
reformulation wrongRecord : source := by
  nlp at bound using (0 : ℝ)

def wrongRepr : ConstraintRepr (fun x : ℝ => x ≤ 3) :=
  ConstraintRepr.ofIff (fun x => x ≤ 3) (fun _ => Iff.rfl)

/-- error: constraint `bound`: the supplied exact certificate does not describe the entire selected predicate -/
#guard_msgs in
reformulation wrongPredicate : source := by
  nlp at bound using wrongRepr

def guardedRule (_ : True) : ConstraintRepr (fun x : ℝ => |x| ≤ 3) :=
  ConstraintRepr.ofIff (fun x => x ≤ 3 ∧ -x ≤ 3)
    (fun x => abs_le' (a := x) (b := 3))

/-- error: constraint `bound`: failed to elaborate exact rule: exact rule contains unresolved metavariables -/
#guard_msgs in
reformulation unresolvedRule : source := by
  nlp at bound using (guardedRule _)

def zeroGuard : ConstraintRepr (fun x : ℝ => 0 ≤ x) where
  Auxiliary := ℝ
  target x u := u = 0 ∧ Real.log u = 0 ∧ 0 ≤ x
  source_iff_exists x := by simp

def zeroGuardSource := problem (x : ℝ) minimize x subject to positive : 0 ≤ x

/-- error: constraint `positive`: generated row certification failed -/
#guard_msgs (substring := true) in
reformulation invalidGeneratedDomain : zeroGuardSource := by
  nlp at positive using zeroGuard

def strictSource := problem (x : ℝ) minimize x subject to strict : x < 3

def strictRepr : ConstraintRepr (fun x : ℝ => x < 3) :=
  ConstraintRepr.ofIff (fun x => x < 3) (fun _ => Iff.rfl)

/-- error: constraint `strict`: generated row certification failed -/
#guard_msgs (substring := true) in
reformulation strict : strictSource := by
  nlp at strict using strictRepr

elab "assert_atomic_nlp% " nested:command : command =>
  MorewTest.elabNoNewDeclarations nested fun name => m!"failed NLP reformulation leaked auxiliary declaration {name}"

def auxiliarySource :=
  problem (v : Fin 1 → ℝ)
    minimize v 0
    subject to
      norm : ‖WithLp.toLp 1 v‖ ≤ 3
      later : 1 ≤ |v 0|

#guard_error_fragments ["constraint `later`: no supported exact NLP rule"] in
assert_atomic_nlp%
reformulation afterAuxiliary : auxiliarySource certificate failedAlias := by
  nlp at norm
  nlp at later

reformulation validAfterFailures : source := by
  nlp at bound
  epigraph t

example : GlobalEquiv source validAfterFailures := validAfterFailures.equiv

run_cmd do
  let env ← Lean.getEnv
  for target in #[`unknown, `stale, `reverse, `equality, `nested, `remaining,
      `missingDomain, `noIdentity, `ambiguous, `wrongRecord, `wrongPredicate,
      `unresolvedRule, `invalidGeneratedDomain, `strict, `afterAuxiliary] do
    let name := `MorewTest.Reformulation.NLPFailures ++ target
    for declaration in #[name, name ++ `equiv] do
      if env.contains declaration then
        Lean.throwError "failed NLP reformulation emitted {declaration}"
    if (Morew.Syntax.getProblemView? env name).isSome then
      Lean.throwError "failed NLP reformulation registered presentation metadata"
  if env.contains `MorewTest.Reformulation.NLPFailures.failedAlias then
    Lean.throwError "failed NLP reformulation emitted its certificate alias"

end
end MorewTest.Reformulation.NLPFailures
