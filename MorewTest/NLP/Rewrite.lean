/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Rewrite
import MorewTest.NLP.DomainSupport

/-!
# Exact selected-row planning

Every successful plan is checked against the original selected predicate and
the exact proposed feasibility, including row insertion and auxiliary projection.
The tests distinguish candidate matching from complete domain certification.
-/

namespace MorewTest.NLP.Rewrite

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew.Elab.NLP
open scoped ENNReal

private def input {X : Type} (source : X → Prop) (retained : Array (X → Prop)) :=
  (source, retained)

private def checkResult (source : Expr) (retained : Array Expr) (insertionIndex : Nat)
    (result : Rewrite.Result) : MetaM Unit := do
  discard <| Morew.Elab.Conic.Plan.checkLift source result.lift
  unless result.rowPredicates.size == result.certified.rowCertificates.size do
    throwError "generated row certificates are incomplete"
  for proof in #[result.lift, result.targetIff, result.certified.domainIsOpen,
      result.certified.feasibleMemDomain] ++ result.certified.rowCertificates do
    if proof.hasMVar || proof.hasSorry then throwError "incomplete exact NLP plan"
    checkWithKernel proof
  let expectedInclusion ← withLocalDeclD `point result.nextDomain fun point => do
    let original := if result.auxiliary?.isSome then Expr.proj ``Prod 0 point else point
    let retained := retained.map (mkApp · original)
    let generated := result.rowPredicates.map (mkApp · point)
    let bodies := retained.extract 0 insertionIndex ++ generated ++
      retained.extract insertionIndex retained.size
    let feasible := Morew.Elab.Conic.Decomposition.conjunction bodies.toList
    let member ← mkAppM ``Membership.mem #[result.certified.domain, point]
    mkForallFVars #[point] (← mkArrow feasible member)
  unless ← isDefEq (← inferType result.certified.feasibleMemDomain) expectedInclusion do
    throwError "NLP plan changed the exact proposed feasibility"
  for i in [:result.rowPredicates.size] do
    let expected ← Space.withCanonicalSpaces #[result.nextDomain] <|
      mkAppM ``Morew.NLP.Rows.Certified
        #[result.certified.domain, result.rowPredicates[i]!]
    unless ← isDefEq (← inferType result.certified.rowCertificates[i]!) expected do
      throwError "NLP plan certified a different generated row"

private def expect (term : TSyntax `term) (rowCount : Nat)
    (auxiliary : Bool := false) (parameters : Nat := 0)
    (insertionIndex : Nat := 0) : TermElabM Unit :=
  Domain.withInput term parameters fun source retained => do
    let before ← getMCtx
    let result ← match ← Rewrite.plan source retained none insertionIndex with
      | .ok result => pure result
      | .error error => throwError "expected exact NLP plan: {error.reason}"
    unless before.mvarCounter == (← getMCtx).mvarCounter &&
        before.lmvarCounter == (← getMCtx).lmvarCounter do
      throwError "successful planning leaked scratch metavariables"
    unless result.rowPredicates.size == rowCount && result.auxiliary?.isSome == auxiliary do
      throwError "unexpected generated rows or auxiliary space"
    checkResult source retained insertionIndex result

private def rejected (term : TSyntax `term) (message : String)
    (parameters : Nat := 0) : TermElabM Unit :=
  Domain.withInput term parameters fun source retained => do
    let environment ← getEnv
    let before ← getMCtx
    let .error error ← Rewrite.plan source retained
      | throwError "unsupported exact NLP replacement was accepted"
    let diagnostic ← error.reason.toString
    unless diagnostic.contains message do
      throwError "wrong exact NLP diagnostic: {error.reason}"
    if diagnostic.contains "no supported exact NLP rule" then
      unless diagnostic.contains "selected predicate:" && diagnostic.contains "predicate type:" do
        throwError "unsupported rule diagnostic omitted its typed source"
    unless error.expression == source do throwError "NLP failure changed the selected source"
    unless before.mvarCounter == (← getMCtx).mvarCounter &&
        before.lmvarCounter == (← getMCtx).lmvarCounter do
      throwError "failed planning leaked scratch metavariables"
    for (name, _) in (← getEnv).constants.toList do
      unless environment.contains name do
        throwError "failed planning leaked declaration {name}"

private def expectUsing (term rule : TSyntax `term) (rowCount : Nat)
    (auxiliary : Bool := false) (parameters : Nat := 0) : TermElabM Unit :=
  Domain.withInput term parameters fun source retained => do
    let rule ← Domain.elaborate rule
    let result ← match ← Rewrite.plan source retained (some rule) with
      | .ok result => pure result
      | .error error => throwError "explicit exact NLP record {rule} failed for {source}: {error.reason}"
    unless result.rowPredicates.size == rowCount && result.auxiliary?.isSome == auxiliary do
      throwError "unexpected explicit replacement shape"
    checkResult source retained 0 result

-- Every scalar orientation permits nonlinear smooth inputs and bounds.
run_cmd liftTermElabM do
  expect (← `(input (fun x : ℝ => |x ^ 2 + Real.sin x| ≤ Real.exp x) #[])) 2
  expect (← `(input (fun x : ℝ => (x * x)⁺ ≤ 3 + Real.cos x) #[])) 2
  expect (← `(input (fun x : ℝ => max (x * x) (Real.sin x) ≤ 2) #[])) 2
  expect (← `(input (fun x : ℝ => -1 ≤ min (x * x) (Real.sin x)) #[])) 2
  expect (← `(input (fun x : ℝ => 3 ≥ |Real.tanh x|) #[])) 2
  expect (← `(input (fun x : ℝ => min (x * x) (Real.cos x) ≥ -2) #[])) 2
  -- A failed abs candidate must not make the successful min plan ambiguous.
  expect (← `(input (fun p : ℝ × ℝ => |(2 : ℝ)| ≤ min p.1 p.2) #[])) 2
  rejected (← `(input (fun _ : ℝ => max (0 : ℝ) 1 ≤ min 2 3) #[]))
    "ambiguous exact NLP rules: Morew.Exact.maxEpigraph, Morew.Exact.minHypograph"
  rejected (← `(input (fun _ : ℝ =>
    ‖WithLp.toLp ∞ (fun _ : Fin 2 => (0 : ℝ))‖ ≤ min 2 3) #[]))
    "Morew.Exact.minHypograph, Morew.Exact.normInfToLpEpigraph"
  rejected (← `(fun v : EuclideanSpace ℝ (Fin 2) =>
    input (fun _ : ℝ => ‖v‖ ≤ min 2 3) #[]))
    "Morew.Exact.minHypograph, Morew.Exact.euclideanNormEpigraph" 1

-- Domains use exact proposed rows, without validating unrelated retained rows.
private def unrelated (x : ℝ) : Prop := x < 50

run_cmd liftTermElabM do
  expect (← `(input (fun x : ℝ => |Real.log x| ≤ 2)
    #[(fun x : ℝ => 1 ≤ x), (fun x : ℝ => unrelated x), (fun x : ℝ => x < 100)]))
    2 false 0 1
  expect (← `(input (fun x : ℝ => max (Real.log x) 1 ≤ x)
    #[(fun x : ℝ => x = 1)])) 2
  rejected (← `(input (fun x : ℝ => |Real.log x| ≤ 2) #[])) "domain"
  rejected (← `(input (fun x : ℝ => |Real.log x| ≤ 2) #[(fun x : ℝ => 0 < x)])) "domain"

-- Symbolic families stay grouped and use the source support, including n = 0.
run_cmd liftTermElabM do
  expect (← `(fun n : ℕ => (input (fun v : Fin n → ℝ => ‖v‖ ≤ 3) #[]))) 3 false 1
  expect (← `(fun n : ℕ => (input (fun v : Fin n → ℝ => ‖WithLp.toLp 1 v‖ ≤ 3) #[])))
    3 true 1
  expect (← `(fun n : ℕ => (input (fun v : Fin n → ℝ => ‖WithLp.toLp 2 v‖ ≤ 3) #[])))
    2 false 1
  expect (← `(input (fun v : Fin 0 → ℝ => ‖v‖ ≤ -1) #[])) 3
  expect (← `(input (fun v : Fin 0 → ℝ => ‖WithLp.toLp 1 v‖ ≤ -1) #[])) 3 true
  expect (← `(input (fun v : Fin 0 → ℝ => ‖WithLp.toLp 2 v‖ ≤ -1) #[])) 2
  expect (← `(input (fun v : Fin 2 → ℝ => ‖WithLp.toLp ∞ (fun i => (v i) ^ 2)‖ ≤ 3) #[])) 3
  expect (← `(input (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖ ≤ 3) #[])) 2
  expect (← `(input (fun v : EuclideanSpace ℝ (Fin 2) => ‖WithLp.ofLp v‖ ≤ 3) #[])) 3
  expect (← `(fun (s : Finset ℕ) (hs : s.Nonempty) (a : ℕ → ℝ) =>
    (input (fun x : ℝ => s.sup' hs (fun i => a i * x ^ 2) ≤ 3) #[]))) 1 false 3
  expect (← `(fun (s : Finset ℕ) (hs : s.Nonempty) (a : ℕ → ℝ) =>
    (input (fun x : ℝ => -3 ≤ s.inf' hs (fun i => a i * x ^ 2)) #[]))) 1 false 3
  expect (← `(fun (s : Finset ℕ) (hs : s.Nonempty) (a : ℕ → ℝ)
      (_ : ∀ i ∈ s, 0 < a i) =>
    (input (fun x : ℝ => s.sup' hs (fun i => Real.log (a i) + x ^ 2) ≤ 3) #[])))
    1 false 4
  expect (← `(fun (s : Finset ℕ) (hs : s.Nonempty) =>
    input (fun x : ℝ => s.sup'
      (@ite s.Nonempty (x = 0) (Classical.propDecidable _) hs hs)
      (fun i => (i : ℝ) * x ^ 2) ≤ 3) #[])) 1 false 2

noncomputable def absoluteGraph : Morew.GraphRepresentation (fun a : ℝ => |a|) where
  Auxiliary := Unit
  target a t _ := t ^ 2 = a ^ 2 ∧ 0 ≤ t
  source_iff_exists a t := by
    constructor
    · intro h
      exact ⟨(), by simpa only [h] using sq_abs a,
        by simpa only [h] using abs_nonneg a⟩
    · rintro ⟨_, h, ht⟩
      apply (sq_eq_sq₀ ht (abs_nonneg a)).mp
      simpa only [sq_abs] using h

def emptyLift : Morew.ExactConstraintLift (fun _ : ℝ => True) :=
  .ofIff (fun _ => True) (fun _ => Iff.rfl)

def identityLift : Morew.ExactConstraintLift (fun x : ℝ => x ^ 2 ≤ 3) :=
  .ofIff (fun x => x ^ 2 ≤ 3) (fun _ => Iff.rfl)

private def hiddenTarget (x : ℝ) : Prop := x ^ 2 ≤ 3

def opaqueTargetLift : Morew.ExactConstraintLift (fun x : ℝ => x ^ 2 ≤ 3) :=
  .ofIff hiddenTarget (fun _ => Iff.rfl)

def strictLift : Morew.ExactConstraintLift (fun x : ℝ => x < 1) :=
  .ofIff (fun x => x < 1) (fun _ => Iff.rfl)

def disjunctiveLift : Morew.ExactConstraintLift (fun x : ℝ => x ≤ 0 ∨ 1 ≤ x) :=
  .ofIff (fun x => x ≤ 0 ∨ 1 ≤ x) (fun _ => Iff.rfl)

def booleanAuxiliary : Morew.ExactConstraintLift (fun _ : ℝ => True) where
  Auxiliary := Bool
  target _ _ := True
  source_iff_exists _ := ⟨fun _ => ⟨false, trivial⟩, fun _ => trivial⟩

run_cmd liftTermElabM do
  expectUsing (← `(input (fun p : ℝ × ℝ => p.2 = |p.1|) #[])) (← `(absoluteGraph)) 2
  expectUsing (← `(input (fun p : ℝ × ℝ => |p.1| = p.2) #[])) (← `(absoluteGraph)) 2
  expectUsing (← `(input (fun x : ℝ => |x ^ 2| ≤ 3) #[])) (← `(Morew.Exact.absEpigraph)) 2
  expectUsing (← `(input (fun p : ℝ × ℝ => 0 ≤ min p.1 p.2) #[]))
    (← `(Morew.Exact.minHypograph)) 2
  expectUsing (← `(input (fun _ : ℝ => max (0 : ℝ) 1 ≤ min 2 3) #[]))
    (← `(Morew.Exact.maxEpigraph)) 2
  expectUsing (← `(input (fun _ : ℝ => max (0 : ℝ) 1 ≤ min 2 3) #[]))
    (← `(Morew.Exact.minHypograph)) 2
  expectUsing (← `(input (fun _ : ℝ =>
    ‖WithLp.toLp ∞ (fun _ : Fin 2 => (0 : ℝ))‖ ≤ min 2 3) #[]))
    (← `(Morew.Exact.normInfToLpEpigraph (n := 2))) 3
  expectUsing (← `(fun v : EuclideanSpace ℝ (Fin 2) =>
    input (fun _ : ℝ => ‖v‖ ≤ min 2 3) #[]))
    (← `(Morew.Exact.euclideanNormEpigraph (n := 2))) 2 false 1
  expectUsing (← `(input (fun _ : ℝ => True) #[])) (← `(emptyLift)) 0
  expectUsing (← `(input (fun x : ℝ => x ^ 2 ≤ 3) #[])) (← `(identityLift)) 1

private def hiddenAbs (x : ℝ) : ℝ := |x|
private def hiddenSquare (x : ℝ) : ℝ := x * x

-- Named model builders are helpers too. Selecting their fields must not expose
-- a decision-dependent predicate, nonsmooth atom, or native norm conversion.
private noncomputable def boundModel (c : ℝ) : Morew.Problem ℝ ℝ where
  objective x := |c * x|
  feasible x := |c * x| ≤ 3

private noncomputable abbrev boundModelAbbrev (c : ℝ) : Morew.Problem ℝ ℝ :=
  ⟨fun x => |c * x|, fun x => |c * x| ≤ 3⟩

private noncomputable def normModel (c : ℝ) :
    Morew.Problem ℝ (EuclideanSpace ℝ (Fin 1)) where
  objective x := WithLp.toLp 2 (fun _ => c * x)
  feasible _ := True

private noncomputable def smoothModel (c : ℝ) : Morew.Problem ℝ ℝ where
  objective x := c * x
  feasible x := c * x ≤ 3

private def modelTargetLift : Morew.ExactConstraintLift (fun x : ℝ => x * x ≤ 3) :=
  .ofIff (fun x => (smoothModel x).feasible x) (fun _ => Iff.rfl)

private def independentModelTargetLift :
    Morew.ExactConstraintLift (fun x : ℝ => 2 * x ≤ 3) :=
  .ofIff (fun x => (smoothModel 2).feasible x) (fun _ => Iff.rfl)

private def literalModelTargetLift : Morew.ExactConstraintLift (fun x : ℝ => x * x ≤ 3) :=
  .ofIff (fun x =>
    (Morew.Problem.mk (fun y : ℝ => y) (fun y => x * y ≤ 3)).feasible x)
    (fun _ => Iff.rfl)

run_cmd liftTermElabM do
  rejected (← `(input (fun x : ℝ => (boundModel x).feasible x) #[]))
    "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => (boundModelAbbrev x).feasible x) #[]))
    "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => let p := boundModel x; p.feasible x) #[]))
    "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => (boundModel x).objective x ≤ 3) #[]))
    "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => ‖(normModel x).objective x‖ ≤ 3) #[]))
    "generated row"
  -- Independent named containers and literal decision-dependent containers
  -- retain the structural reductions used by imported/applied models.
  expect (← `(fun c : ℝ => input (fun x : ℝ => (boundModel c).feasible x) #[])) 2 false 1
  expect (← `(fun c : ℝ => input (fun x : ℝ => (boundModel c).objective x ≤ 3) #[]))
    2 false 1
  expect (← `(fun c : ℝ => input (fun x : ℝ => ‖(normModel c).objective x‖ ≤ 3) #[]))
    2 false 1
  expect (← `(input (fun x : ℝ =>
    (Morew.Problem.mk (fun y : ℝ => y) (fun y => |x * y| ≤ 3)).feasible x) #[])) 2
  expect (← `(input (fun x : ℝ =>
    let p : Morew.Problem ℝ ℝ := ⟨fun y => y, fun y => |x * y| ≤ 3⟩
    p.feasible x) #[])) 2
  expectUsing (← `(input (fun x : ℝ => 2 * x ≤ 3) #[]))
    (← `(independentModelTargetLift)) 1
  expectUsing (← `(input (fun x : ℝ => x * x ≤ 3) #[]))
    (← `(literalModelTargetLift)) 1
  let source ← Domain.elaborate (← `(fun x : ℝ => x * x ≤ 3))
  let rule ← Domain.elaborate (← `(modelTargetLift))
  let .error error ← Rewrite.plan source #[] (some rule)
    | throwError "a decision-dependent named model target was unfolded"
  unless (← error.reason.toString).contains "generated row" do
    throwError "named model target did not fail at the target grammar boundary"

run_cmd liftTermElabM do
  rejected (← `(input (fun x : ℝ => x ^ 2 ≤ 3) #[])) "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => 0 ≤ |x|) #[])) "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => |x| = 1) #[])) "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => Real.exp |x| ≤ 3) #[])) "entire selected predicate"
  rejected (← `(input (fun x : ℝ => hiddenAbs x ≤ 3) #[])) "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => |hiddenSquare x| ≤ 3) #[])) "generated row"
  rejected (← `(fun (s : Finset ℕ) (hs : s.Nonempty) (a : ℕ → ℝ) =>
    (input (fun x : ℝ => s.sup' hs (fun i => Real.log (a i) + x ^ 2) ≤ 3) #[])))
    "domain" 3
  rejected (← `(input (fun x : ℝ => @Max.max ℝ ⟨fun a _ => a⟩ x x ≤ 3) #[]))
    "no supported exact NLP rule"
  rejected (← `(input (fun x : ℝ => @LE.le ℝ ⟨fun _ _ => True⟩ |x| 3) #[]))
    "order instance"
  expect (← `(input (fun _ : ℝ => ‖(fun _ : Fin 2 => (0 : ℝ))‖ ≤ 1) #[])) 3
  rejected (← `(input (fun _ : ℝ =>
    @Norm.norm (Fin 2 → ℝ) ⟨fun _ => 0⟩ (fun _ => 0) ≤ 1) #[])) "instance"

-- Explicit records cannot bypass exact-source, target-grammar or state checks.
run_cmd liftTermElabM do
  let source ← Domain.elaborate (← `(fun x : ℝ => |x| ≤ 3))
  let wrong ← Domain.elaborate (← `(identityLift))
  let .error _ ← Rewrite.plan source #[] (some wrong)
    | throwError "mismatching explicit record was accepted"
  let smoothSource ← Domain.elaborate (← `(fun x : ℝ => x ^ 2 ≤ 3))
  let opaqueTarget ← Domain.elaborate (← `(opaqueTargetLift))
  let .error error ← Rewrite.plan smoothSource #[] (some opaqueTarget)
    | throwError "a named target predicate was unfolded"
  unless (← error.reason.toString).contains "generated row" do
    throwError "named target did not fail at the target grammar boundary"
  for term in #[← `(strictLift), ← `(disjunctiveLift), ← `(booleanAuxiliary)] do
    let rule ← Domain.elaborate term
    let type ← whnf (← inferType rule)
    let .error _ ← Rewrite.plan type.getAppArgs[1]! #[] (some rule)
      | throwError "unsupported explicit target grammar or auxiliary space was accepted"
  let .error _ ← Rewrite.plan source #[] none 1
    | throwError "out-of-bounds insertion was accepted"
  let builder ← Domain.elaborate (← `(fun c : ℝ => fun x : ℝ => |x| ≤ c))
  let hole ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  let .error error ← Rewrite.plan (mkApp builder hole) #[]
    | throwError "unresolved bound was accepted"
  unless (← error.reason.toString).contains "unresolved" do
    throwError "unresolved input lost its diagnostic"
  if ← hole.mvarId!.isAssigned then throwError "planning assigned a caller hole"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "planning leaked metavariables on unresolved input"
  withLetDecl `hidden (mkConst ``Real) hole fun binding => do
    let expression := mkApp builder binding
    unless !expression.hasMVar do throwError "hidden-hole fixture exposes its hole directly"
    let .error error ← Rewrite.plan expression #[]
      | throwError "a placeholder hidden in a source local was accepted"
    unless (← error.reason.toString).contains "unresolved" do
      throwError "hidden placeholder lost its diagnostic"
    if ← hole.mvarId!.isAssigned then throwError "planning assigned a hidden caller hole"

end MorewTest.NLP.Rewrite
