/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Exact exponential-cone reformulations

These executable examples exercise native and named atoms, retained domain
evidence, grouped finite lifts, and composition with the existing targeted
rewrites. Margins remain ordinary constraints in their original positions.
-/

namespace MorewTest.Reformulation.Exponential

open Morew Morew.Conic

noncomputable section

namespace Scalar

def source :=
  problem (a b t : ℝ)
    minimize a ^ 2
    subject to
      first : Real.exp (2 * a + 1) ≤ t
      untouched : Real.exp (a ^ 2) ≤ 100
      positive : b ≥ 1 / 2
      logarithm : Real.log b ≥ t
      nonnegative : 0 ≤ a
      last : Fn.relativeEntropy a b ≤ t

reformulation target : source := by
  conic at first
  conic at logarithm
  conic at last

example : GlobalEquivalence source target := target.equivalence

example (a b t : ℝ) : target.objective ((a, b), t) = a ^ 2 := rfl

example (a b t : ℝ) : target.feasible ((a, b), t) ↔
    (2 * a + 1, 1, t) ∈ EXP ∧ Real.exp (a ^ 2) ≤ 100 ∧ b ≥ 1 / 2 ∧
      (t, 1, b) ∈ EXP ∧ 0 ≤ a ∧ (-t, a, b) ∈ EXP := Iff.rfl

/--
info: problem (a b t : ℝ)
  minimize a ^ 2
  subject to
    first_conic_1 : (2 * a + 1, 1, t) ∈ EXP
    untouched : Real.exp (a ^ 2) ≤ 100
    positive : b ≥ 1 / 2
    logarithm_conic_1 : (t, 1, b) ∈ EXP
    nonnegative : 0 ≤ a
    last_conic_1 : (-t, a, b) ∈ EXP
-/
#guard_msgs in
#printp target

def reverseSource :=
  problem (a b t : ℝ)
    maximize t
    subject to
      exp : t ≥ Real.exp a
      log : t ≤ Real.log b
      entropy : t ≥ a * Real.log (a / b)
      domain : a ≥ 0 ∧ 1 ≤ b

reformulation reverseTarget : reverseSource := by
  conic at exp
  conic at log
  conic at entropy

example : GlobalEquivalence reverseSource reverseTarget := reverseTarget.equivalence

example (a b t : ℝ) : reverseTarget.feasible ((a, b), t) ↔
    (a, 1, t) ∈ EXP ∧ (t, 1, b) ∈ EXP ∧ (-t, a, b) ∈ EXP ∧
      (a ≥ 0 ∧ 1 ≤ b) := Iff.rfl

def constantDomainSource :=
  problem (t : ℝ)
    minimize t
    subject to
      logarithm : t ≤ Real.log (3 / 2)
      entropy : Fn.relativeEntropy 0 2 ≤ t

reformulation constantDomainTarget : constantDomainSource := by
  conic at logarithm
  conic at entropy

example : GlobalEquivalence constantDomainSource constantDomainTarget :=
  constantDomainTarget.equivalence

example (t : ℝ) : constantDomainTarget.feasible t ↔
    (t, 1, 3 / 2) ∈ EXP ∧ (-t, 0, 2) ∈ EXP := Iff.rfl

def affineDomainSource :=
  problem (a b t : ℝ)
    minimize t
    subject to
      entropy : Fn.relativeEntropy (2 * a + 1) (b + 1) ≤ t / 2
      logarithm : t - 1 ≤ Real.log (b + 1)
      domain : 0 ≤ 2 * a + 1 ∧ 1 ≤ b + 1

reformulation affineDomainTarget : affineDomainSource := by
  conic at entropy
  conic at logarithm

example : GlobalEquivalence affineDomainSource affineDomainTarget :=
  affineDomainTarget.equivalence

example (a b t : ℝ) : affineDomainTarget.feasible ((a, b), t) ↔
    (-(t / 2), 2 * a + 1, b + 1) ∈ EXP ∧ (t - 1, 1, b + 1) ∈ EXP ∧
      (0 ≤ 2 * a + 1 ∧ 1 ≤ b + 1) := Iff.rfl

end Scalar

namespace Margins

def source :=
  problem (a b t : ℝ)
    minimize t
    subject to
      unusable : -1 ≤ b
      logarithm : t ≤ Real.log b
      nested : Real.exp (a ^ 2) ≤ 100 ∧ (0 ≤ b ∧ (1 / 3 ≤ b ∧ a ≥ 0))
      entropy : a * Real.log (a / b) ≤ t
      anotherMargin : 1 ≤ b

-- A failed candidate does not stop the search. Both contextual rewrites use
-- retained conjunction leaves without splitting or duplicating their entries.
reformulation target : source := by
  conic at logarithm
  conic at entropy

example : GlobalEquivalence source target := target.equivalence

example (a b t : ℝ) : target.feasible ((a, b), t) ↔
    -1 ≤ b ∧ (t, 1, b) ∈ EXP ∧
      (Real.exp (a ^ 2) ≤ 100 ∧ (0 ≤ b ∧ (1 / 3 ≤ b ∧ a ≥ 0))) ∧
      (-t, a, b) ∈ EXP ∧ 1 ≤ b := Iff.rfl

class Parameter where
  epsilon : ℝ

section

variable [Parameter] (hε : 0 < Parameter.epsilon)

def symbolicSource :=
  problem (a b t : ℝ)
    minimize t
    subject to
      entropy : Fn.relativeEntropy a b ≤ t
      nonnegative : 0 ≤ a
      denominator : Parameter.epsilon ≤ b

include hε in
reformulation symbolicTarget : symbolicSource := by
  conic at entropy

example : GlobalEquivalence symbolicSource symbolicTarget := symbolicTarget.equivalence hε

end

end Margins

namespace FiniteLifts

def namedSource :=
  problem (xs : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      before : Real.exp (xs 0 ^ 2) ≤ 100
      lse : Fn.logSumExp (fun i => 2 * xs i + 1) ≤ t
      after : xs 0 ≤ 4

reformulation namedTarget : namedSource := by
  conic at lse

example : GlobalEquivalence namedSource namedTarget := namedTarget.equivalence

example (xs u : Fin 2 → ℝ) (t : ℝ) : namedTarget.feasible ((xs, t), u) ↔
    Real.exp (xs 0 ^ 2) ≤ 100 ∧
      (∀ i, (2 * xs i + 1 - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 ∧
      xs 0 ≤ 4 := Iff.rfl

/--
info: problem (xs : Fin 2 → ℝ) (t : ℝ) (lse_aux : Fin 2 → ℝ)
  minimize t
  subject to
    before : Real.exp (xs 0 ^ 2) ≤ 100
    lse_conic_1 : ∀ (i : Fin 2), (2 * xs i + 1 - t, 1, lse_aux i) ∈ EXP
    lse_conic_2 : ∑ i, lse_aux i ≤ 1
    after : xs 0 ≤ 4
-/
#guard_msgs in
#printp namedTarget

def rawSource :=
  problem (xs : Fin 1 → ℝ) (t : ℝ)
    minimize t
    subject to
      lse : t ≥ Real.log (∑ i, Real.exp (xs i))

reformulation rawTarget : rawSource := by
  conic at lse

example : GlobalEquivalence rawSource rawTarget := rawTarget.equivalence

example (xs u : Fin 1 → ℝ) (t : ℝ) : rawTarget.feasible ((xs, t), u) ↔
    (∀ i, (xs i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 := Iff.rfl

def softplusSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      loss : Fn.softplus (2 * x - 1) ≤ t

reformulation softplusTarget : softplusSource := by
  conic at loss

example : GlobalEquivalence softplusSource softplusTarget := softplusTarget.equivalence

example (x t : ℝ) (u : Fin 2 → ℝ) : softplusTarget.feasible ((x, t), u) ↔
    (∀ i, (![0, 2 * x - 1] i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 := Iff.rfl

/--
info: problem (x t : ℝ) (loss_aux : Fin 2 → ℝ)
  minimize t
  subject to
    loss_conic_1 : ∀ (i : Fin 2), (![0, 2 * x - 1] i - t, 1, loss_aux i) ∈ EXP
    loss_conic_2 : ∑ i, loss_aux i ≤ 1
-/
#guard_msgs in
#printp softplusTarget

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    loss : Fn.softplus (2 * x - 1) ≤ t
-/
#guard_msgs in
#printp softplusSource

def rawSoftplusSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      loss : t ≥ Real.log (1 + Real.exp x)

reformulation rawSoftplusTarget : rawSoftplusSource := by
  conic at loss

example : GlobalEquivalence rawSoftplusSource rawSoftplusTarget := rawSoftplusTarget.equivalence

-- Printing the original problem retains the native spelling used by its author.
/--
info: problem (x t : ℝ)
  minimize t
  subject to
    loss : t ≥ Real.log (1 + Real.exp x)
-/
#guard_msgs in
#printp rawSoftplusSource

run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``softplusTarget
    | Lean.throwError "missing grouped exponential presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `softplusCopy
  Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : softplusCopy = softplusTarget := rfl

-- The compact EXP carrier spelling belongs only to stored presentations.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← Lean.Elab.Term.elabTerm
    (← `(fun (x y z : ℝ) => (x, y, z) ∈ EXP)) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  let exact ← Morew.Reformulation.Internal.exactExpressionSyntax original
  if (exact.raw.findStack? (fun _ => true) (fun stx =>
      stx.isOfKind ``Morew.Conic.exponentialCarrier)).isSome then
    Lean.throwError "exponential notation leaked into exact semantic syntax"
  let restored ← Lean.Elab.Term.elabTerm exact none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  unless ← Lean.Meta.isDefEq original (← Lean.instantiateMVars restored) do
    Lean.throwError "exact exponential syntax changed its meaning"

end FiniteLifts

namespace SymbolicDimensions

class Dimension where
  size : Nat

section

variable [Dimension] (hn : 0 < Dimension.size)

def source :=
  problem (xs : Fin Dimension.size → ℝ) (t : ℝ)
    minimize t
    subject to
      lse : Fn.logSumExp xs ≤ t

include hn in
reformulation positiveTarget : source := by
  conic at lse

example : GlobalEquivalence source positiveTarget := positiveTarget.equivalence hn

example (xs u : Fin Dimension.size → ℝ) (t : ℝ) :
    positiveTarget.feasible ((xs, t), u) ↔
      (∀ i, (xs i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 := Iff.rfl

end

section

variable [Dimension] [NeZero Dimension.size]

reformulation neZeroTarget : source := by
  conic at lse

example : GlobalEquivalence source neZeroTarget := neZeroTarget.equivalence

end

section

variable [Dimension] [Nonempty (Fin Dimension.size)]

reformulation nonemptyTarget : source := by
  conic at lse

example : GlobalEquivalence source nonemptyTarget := nonemptyTarget.equivalence

end

end SymbolicDimensions

namespace Names

def source :=
  problem (loss_aux x t : ℝ)
    minimize t
    subject to
      loss_conic_1 : loss_aux ≤ x
      loss : Fn.softplus x ≤ t
      labels.cap : Real.exp x ≤ 10

reformulation target : source := by
  conic at loss
  conic at labels.cap

example : GlobalEquivalence source target := target.equivalence

example (a x t : ℝ) (u : Fin 2 → ℝ) : target.feasible (((a, x), t), u) ↔
    a ≤ x ∧ (∀ i, (![0, x] i - t, 1, u i) ∈ EXP) ∧
      (∑ i, u i) ≤ 1 ∧ (x, 1, 10) ∈ EXP := Iff.rfl

/--
info: problem (loss_aux x t : ℝ) (loss_aux_1 : Fin 2 → ℝ)
  minimize t
  subject to
    loss_conic_1 : loss_aux ≤ x
    loss_conic_1_1 : ∀ (i : Fin 2), (![0, x] i - t, 1, loss_aux_1 i) ∈ EXP
    loss_conic_2 : ∑ i, loss_aux_1 i ≤ 1
    cap_conic_1 : (x, 1, 10) ∈ EXP
-/
#guard_msgs in
#printp target

end Names

namespace Composition

-- Atom heads in independent affine bounds must not suppress successful
-- second-order or polyhedral fallback rules.
def fallbackSource :=
  problem (x : ℝ)
    minimize x
    subject to
      square : x ^ 2 ≤ Real.log 2
      absolute : |x| ≤ Real.exp 2

reformulation fallbackTarget : fallbackSource := by
  conic at square
  conic at absolute

example : GlobalEquivalence fallbackSource fallbackTarget := fallbackTarget.equivalence

example (x : ℝ) : fallbackTarget.feasible x ↔
    (Real.log 2, 1 / 2, ![x]) ∈ RSOC 1 ∧ x ≤ Real.exp 2 ∧ -x ≤ Real.exp 2 := Iff.rfl

def mixedSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      absolute : |x| ≤ 5
      square : x ^ 2 ≤ 25
      exponential : Real.exp x ≤ t
      softplus : Fn.softplus x ≤ t

reformulation mixedTarget : mixedSource := by
  conic at absolute
  conic at square
  conic at exponential
  conic at softplus

example : GlobalEquivalence mixedSource mixedTarget := mixedTarget.equivalence

example (x t : ℝ) (u : Fin 2 → ℝ) : mixedTarget.feasible ((x, t), u) ↔
    x ≤ 5 ∧ -x ≤ 5 ∧ (25, 1 / 2, ![x]) ∈ RSOC 1 ∧
      (x, 1, t) ∈ EXP ∧ (∀ i, (![0, x] i - t, 1, u i) ∈ EXP) ∧
      (∑ i, u i) ≤ 1 := Iff.rfl

def Positive (x : ℝ) : Prop := 0 < x

def substitutionSource :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      exponential : Real.exp x ≤ 10
      positive : Positive x

reformulation substitutionTarget : substitutionSource := by
  conic at exponential
  substitute x := Real.exp u
  epigraph t as value

example : GlobalEquivalence substitutionSource substitutionTarget :=
  substitutionTarget.equivalence

example (u t : ℝ) : substitutionTarget.feasible (u, t) ↔
    (Real.exp u, 1, 10) ∈ EXP ∧ u ≤ t := Iff.rfl

def expObjective := problem (x : ℝ) minimize Real.exp x

reformulation epigraphTarget : expObjective := by
  epigraph t
  conic at epigraph_t

reformulation continued : epigraphTarget := by
  epigraph value as objectiveBound

example : GlobalEquivalence expObjective continued :=
  epigraphTarget.equivalence.trans continued.equivalence

example (x t value : ℝ) : continued.feasible ((x, t), value) ↔
    (x, 1, t) ∈ EXP ∧ t ≤ value := Iff.rfl

def logObjective :=
  problem (x : ℝ)
    maximize Real.log x
    subject to
      margin : 1 ≤ x

reformulation hypographTarget : logObjective := by
  hypograph t as value
  conic at value

example : GlobalEquivalence logObjective hypographTarget := hypographTarget.equivalence

example (x t : ℝ) : hypographTarget.feasible (x, t) ↔
    1 ≤ x ∧ (t, 1, x) ∈ EXP := Iff.rfl

end Composition

end

end MorewTest.Reformulation.Exponential
