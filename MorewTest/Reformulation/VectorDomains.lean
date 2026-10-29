/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Affine.Support
import MorewTest.Diagnostics
import MorewTest.Environment
import Lean.Meta.Tactic.AuxLemma

/-!
# Coordinatewise retained-domain evidence

Small exact records isolate domain reconstruction from the finite power-cone
mathematics. Only checked non-strict vector margins establish positive inputs.
-/

namespace MorewTest.Reformulation.VectorDomains

open Morew Morew.Conic
noncomputable section

def nonnegativeSum {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i
def positiveSum {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

@[morew_conic]
def nonnegativeSumEpigraph {n : ℕ} :
    EpigraphRepresentation
      (fun x : {x : Fin n → ℝ // ∀ i, 0 ≤ x i} => nonnegativeSum x.1) where
  Auxiliary := Unit
  target x t _ := (∑ i, x.1 i) ≤ t
  source_iff_exists _ _ := by simp only [nonnegativeSum, exists_const]

@[morew_conic]
def positiveSumEpigraph {n : ℕ} :
    EpigraphRepresentation
      (fun x : {x : Fin n → ℝ // ∀ i, 0 < x i} => positiveSum x.1) where
  Auxiliary := Unit
  target x t _ := (∑ i, x.1 i) ≤ t
  source_iff_exists _ _ := by simp only [positiveSum, exists_const]

def nonnegativeSource (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : 0 ≤ x
      bound : nonnegativeSum x ≤ t

section
variable (n : ℕ)

reformulation nonnegativeReady : (nonnegativeSource n) := by
  conic at bound
  conic

example : GlobalEquivalence (nonnegativeSource n) (nonnegativeReady n) :=
  nonnegativeReady.equivalence n

end

def positiveSource (n : ℕ) (ε : Fin n → ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : x ≥ ε
      bound : positiveSum x ≤ t

section Parameterized
variable (n : ℕ) (ε : Fin n → ℝ) (hε : ∀ i, 0 < ε i)

include hε in
reformulation positiveReady : (positiveSource n ε) := by
  conic at bound
  conic

example : GlobalEquivalence (positiveSource n ε) (positiveReady n ε) :=
  positiveReady.equivalence n ε hε
example : (positiveReady.conicForm n ε).data.toProblem = positiveReady n ε :=
  (positiveReady.conicForm n ε).represents

def coneSource (n : ℕ) (ε : Fin n → ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : x - ε ∈ ℝ₊^n
      bound : positiveSum x ≤ t

include hε in
reformulation coneReady : (coneSource n ε) := by
  conic at bound
  conic

example : GlobalEquivalence (coneSource n ε) (coneReady n ε) :=
  coneReady.equivalence n ε hε

def directConeSource (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : x ∈ ℝ₊^n
      bound : nonnegativeSum x ≤ t

reformulation directConeReady : (directConeSource n) := by
  conic at bound
  conic

def familySource (n : ℕ) (ε : Fin n → ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : ∀ i, ε i ≤ x i
      bound : positiveSum x ≤ t

include hε in
reformulation familyTargeted : (familySource n ε) := by
  conic at bound

example : GlobalEquivalence (familySource n ε) (familyTargeted n ε) :=
  familyTargeted.equivalence n ε hε

-- Pointwise margins are usable evidence, but this retained syntax is not a
-- terminal cone family. It is never silently rewritten as a vector bound.
#guard_error_fragments ["domain"] in
reformulation familyTerminal : (familyTargeted n ε) := by
  conic

end Parameterized

-- Strict Pi order is not coordinatewise strict positivity: one coordinate
-- may remain zero. An exact proof of vector positivity must not fill the gap.
section
variable (n : ℕ) (ε : Fin n → ℝ) (hvector : 0 < ε)
include hvector in
#guard_error_fragments ["coordinatewise positive", "margin"] in
reformulation strictVectorRejected : (positiveSource n ε) := by
  conic at bound
end

#guard_error_fragments ["coordinatewise positive", "margin"] in
reformulation zeroMarginRejected : (positiveSource 2 ![1, 0]) := by
  conic at bound

def wrongCoordinate :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      oneCoordinate : 1 ≤ x 0
      bound : positiveSum x ≤ t

#guard_error_fragments ["coordinatewise positive", "margin"] in
reformulation wrongCoordinateRejected : wrongCoordinate := by
  conic at bound

def dependentMargin :=
  problem (x y : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      first : (fun _ => (1 : ℝ)) ≤ y
      second : y ≤ x
      bound : positiveSum x ≤ t

#guard_error_fragments ["coordinatewise positive", "margin"] in
reformulation dependentMarginRejected : dependentMargin := by
  conic at bound

def selectedOnly :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      bound : positiveSum x ≤ t

#guard_error_fragments ["coordinatewise positive", "margin"] in
reformulation selectedOnlyRejected : selectedOnly := by
  conic at bound

-- A successful rewrite after all failures checks that no evidence escaped.
reformulation recovered : (positiveSource 2 (fun _ => 1)) := by
  conic at bound
  conic

example : IsConic recovered := recovered.isConic

/-! Direct planning checks isolate evidence provenance from the validity of
retained rows as terminal constraints. -/

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open MorewTest.Affine

private def checkPlan (source : Expr) (retained : Array Expr) (accepted : Bool)
    (fragment : String := "") (provider : Morew.Elab.Affine.EvidenceProvider := {}) :
    MetaM Unit := do
  let unresolved ← mkFreshExprMVar (mkConst ``Nat)
  let assigned ← mkFreshExprMVar (mkConst ``Nat)
  assigned.mvarId!.assign (mkNatLit 7)
  let before ← getMCtx
  let environment ← getEnv
  let result ← Morew.Elab.Conic.Rewrite.planDeclaration source
    ``positiveSumEpigraph retained provider
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "vector domain planning changed caller metavariable state"
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "vector domain planning changed an existing assignment"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "vector domain planning assigned a caller hole"
  if ← unresolved.mvarId!.isAssigned then throwError "vector domain planning assigned a caller hole"
  unless (← instantiateMVars assigned) == mkNatLit 7 do
    throwError "vector domain planning discarded a caller assignment"
  match result with
  | .ok result =>
    unless accepted do throwError "unsupported vector domain evidence was accepted: {source}"
    result.toResult.check source retained
    checkWithKernel result.certificate.expression
    for row in result.certifiedRows do
      checkWithKernel row.constraint
      checkWithKernel row.pointwiseIff
  | .error error =>
    if accepted then throwError "vector domain control was rejected: {error.reason}"
    unless (← error.reason.toString).contains fragment do
      throwError "unexpected vector domain rejection: {error.reason}"
    unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
      throwError "failed vector domain planning changed declarations"

private def hiddenMargin (x : Fin 2 → ℝ) : Prop := ∀ i, 1 ≤ x i

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ => positiveSum p.1 ≤ p.2))
  let good ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    True ∧ ∀ i : Fin 2, True ∧ (1 : ℝ) ≤ p.1 i))
  checkPlan source #[good] true
  -- A native vector bound remains valid under a surrounding conjunction/let.
  let vector ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    let ε : Fin 2 → ℝ := fun _ => 1
    True ∧ ε ≤ p.1))
  checkPlan source #[vector] true
  -- These fake instances even agree with native operations on the particular
  -- operands below. Checking only the complete proposition would therefore
  -- miss the unsupported vector order, subtraction, or membership instance.
  let fakeLE ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    @LE.le (Fin 2 → ℝ) ⟨fun _ x => (fun _ => (1 : ℝ)) ≤ x⟩ (fun _ => 1) p.1))
  checkPlan source #[fakeLE] false "coordinatewise positive"
  let fakeSub ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    @HSub.hSub (Fin 2 → ℝ) (Fin 2 → ℝ) (Fin 2 → ℝ)
      ⟨fun x _ => x - fun _ => 1⟩ p.1 (fun _ => 1) ∈ ℝ₊^2))
  checkPlan source #[fakeSub] false "coordinatewise positive"
  let fakeMembership ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    @Membership.mem (Fin 2 → ℝ) (ConvexCone ℝ (Fin 2 → ℝ))
      ⟨fun _ x => x ∈ ℝ₊^2⟩ (ℝ₊^2) (p.1 - fun _ => 1)))
  checkPlan source #[fakeMembership] false "coordinatewise positive"
  -- Strict rows are deliberately not converted into constant margins, and
  -- Pi's strict order must not be mistaken for coordinatewise strict order.
  let strictFamily ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    ∀ i, (0 : ℝ) < p.1 i))
  checkPlan source #[strictFamily] false "coordinatewise positive"
  let strictVector ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    (0 : Fin 2 → ℝ) < p.1))
  checkPlan source #[strictVector] false "coordinatewise positive"
  -- One exact finite specialization is supported; neither nested binders,
  -- reindexing, nor unfolding a named predicate widens that policy.
  let nested ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    ∀ _j : Fin 2, ∀ i : Fin 2, (1 : ℝ) ≤ p.1 i))
  checkPlan source #[nested] false "coordinatewise positive"
  let reindexed ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    ∀ i : Fin 2, (1 : ℝ) ≤ p.1 i.rev))
  checkPlan source #[reindexed] false "coordinatewise positive"
  let hidden ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ => hiddenMargin p.1))
  checkPlan source #[hidden] false "coordinatewise positive"
  let otherSource ← elaborate (← `(fun p : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ℝ =>
    positiveSum p.1.1 ≤ p.2))
  let otherMargin ← elaborate (← `(fun p : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ℝ =>
    (fun _ => (1 : ℝ)) ≤ p.1.2))
  checkPlan otherSource #[otherMargin] false "coordinatewise positive"

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ => positiveSum p.1 ≤ p.2))
  let margin ← elaborate (← `(fun ε : Fin 2 → ℝ =>
    fun p : (Fin 2 → ℝ) × ℝ => ε ≤ p.1))
  let positive ← elaborate (← `(fun ε : Fin 2 → ℝ => ∀ i, (0 : ℝ) < ε i))
  let vectorType ← elaborate (← `(Fin 2 → ℝ))
  withLocalDeclD `ε vectorType fun epsilon => do
    let goal := positive.beta #[epsilon]
    let retained := #[margin.beta #[epsilon]]
    withLocalDeclD `positiveCoordinates goal fun _ => checkPlan source retained true
    withLetDecl `hiddenPositive goal (← mkSorry goal true) fun _ =>
      checkPlan source retained false "coordinatewise positive"
    let hole ← mkFreshExprMVar goal
    withLetDecl `hiddenPositive goal hole fun _ =>
      checkPlan source retained false "coordinatewise positive"
    if ← hole.mvarId!.isAssigned then throwError "domain search assigned hidden proof evidence"
    checkPlan source retained false "coordinatewise positive"

-- Fail after successful coordinate evidence and an affine callback has created
-- an actual auxiliary theorem. Both that declaration and caller assignments
-- must roll back, including when a second attempt follows the first.
run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    positiveSum p.1 ≤ p.2 / 2 + p.2 * p.2))
  let margin ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ => (fun _ => (1 : ℝ)) ≤ p.1))
  let proof ← elaborate (← `(show (2 : ℝ) ≠ 0 from by norm_num))
  let callerHole ← mkFreshExprMVar (mkConst ``Nat)
  let generated ← IO.mkRef (#[] : Array Name)
  let provider : Morew.Elab.Affine.EvidenceProvider := {
    nonzeroEvidence? := some fun goal => do
      unless ← isDefEq (← inferType proof) goal do return none
      let name ← mkAuxLemma [] goal proof (cache := false)
      generated.modify (·.push name)
      callerHole.mvarId!.assign (mkNatLit 19)
      return some (mkConst name)
  }
  for _ in [:2] do
    let previousCount := (← generated.get).size
    checkPlan source #[margin] false "both factors of multiplication" provider
    unless (← generated.get).size > previousCount do
      throwError "late vector-domain failure did not reach the evidence callback"
  let names ← generated.get
  for name in names do
    if (← getEnv).contains name then throwError "late vector-domain failure leaked {name}"
  if ← callerHole.mvarId!.isAssigned then throwError "late failure retained a callback assignment"
  let recovered ← elaborate (← `(fun p : (Fin 2 → ℝ) × ℝ => positiveSum p.1 ≤ p.2))
  checkPlan recovered #[margin] true
  checkPlan recovered #[] false "coordinatewise positive"

end
end MorewTest.Reformulation.VectorDomains
