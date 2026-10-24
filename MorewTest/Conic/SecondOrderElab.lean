/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.SecondOrder
import MorewTest.Affine.Support
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Typed second-order planning and retained domain evidence

Each result is checked against the exact selected predicate, the ordered retained
conjunction, and its single certified cone row. Rejection tests distinguish native
operation instances and exercise isolation of caller metavariables.
-/

namespace MorewTest.Conic.SecondOrderElab

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open MorewTest.Affine
open Morew.Elab.Conic.SecondOrder
open scoped ENNReal

private noncomputable abbrev nativeLE : LE ℝ := inferInstance

private def conjunction (rows : Array Expr) : Expr :=
  if rows.isEmpty then mkConst ``True
  else rows.pop.toList.foldr (mkApp2 (mkConst ``And)) rows.back!

private def checkPlan (source : Expr) (retained : Array Expr := #[]) : MetaM Unit := do
  let result ← match ← plan source retained with
    | .ok result => pure result
    | .error error => throwError "expected a second-order plan for {source}: {error.reason}"
  unless result.rowPredicates.size == 1 && result.certifiedRows.size == 1 do
    throwError "second-order planning must produce exactly one cone row"
  let .forallE _ domain _ _ ← whnf (← inferType source)
    | throwError "source is not a predicate"
  unless ← isDefEq result.domain domain do
    throwError "second-order planning changed the decision domain"
  let expected ← withLocalDeclD `point domain fun point => do
    let remainder := conjunction (retained.map (mkApp · point))
    let target := mkApp result.rowPredicates[0]! point
    let equivalence ← mkAppM ``Iff #[mkApp source point, target]
    mkForallFVars #[point] (← mkArrow remainder equivalence)
  unless ← isDefEq (← inferType result.conditionalIff) expected do
    throwError "conditional certificate does not retain the exact source and remainder"
  let some row := result.certifiedRows[0]? | throwError "missing certified row"
  let constraintType ← whnf (← inferType row.constraint)
  let rowExpected ← withLocalDeclD `point domain fun point => do
    let holds := mkAppN
      (mkConst ``Morew.Conic.Constraint.Holds constraintType.getAppFn.constLevels!)
      (constraintType.getAppArgs ++ #[row.constraint, point])
    mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp result.rowPredicates[0]! point])
  unless ← isDefEq (← inferType row.pointwiseIff) rowExpected do
    throwError "the certified row does not match the generated membership"
  for expression in #[result.conditionalIff, row.constraint, row.pointwiseIff] do
    if expression.hasMVar || expression.hasSorry then
      throwError "second-order planning returned an incomplete certificate"
    checkWithKernel expression

private def rejectPlan (source : Expr) (retained : Array Expr) (fragment : String) :
    MetaM Unit := do
  let .error error ← plan source retained
    | throwError "unsupported second-order predicate was accepted: {source}"
  let message ← error.reason.toString
  unless message.contains fragment do
    throwError "expected diagnostic containing {fragment}, got {message}"

private def checkReplacement (source : Expr) (retained : Array Expr)
    (contextual : Bool) : MetaM Unit := do
  match ← planReplacement source retained with
  | .error error => throwError "expected a second-order replacement: {error.reason}"
  | .ok (.inl result) =>
    if contextual then throwError "a retained-margin rewrite escaped its context"
    if result.auxiliary?.isSome then throwError "an unconditional rewrite added an auxiliary"
    let domain ← Morew.Elab.Conic.Plan.predicateDomain source
    unless ← isDefEq result.nextDomain domain do throwError "exact rewrite changed the domain"
    discard <| Morew.Elab.Conic.Plan.checkLift source result.lift
    checkWithKernel result.targetIff
  | .ok (.inr result) =>
    unless contextual do throwError "an unconditional rewrite retained unused domain evidence"
    checkWithKernel result.conditionalIff

private def expectPlan (stx : TSyntax `term) (parameterCount : Nat := 0) : TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    checkPlan source
    checkReplacement source #[] false

private def expectRejected (stx : TSyntax `term) (fragment : String)
    (parameterCount : Nat := 0) : TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression parameterCount fun _ source => rejectPlan source #[] fragment

private def contextCase (stx : TSyntax `term) (parameterCount : Nat := 0)
    (failure? : Option String := none) : TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression parameterCount fun _ pair => do
    let pair ← Morew.Elab.Affine.reduceStructure pair
    unless pair.isAppOfArity ``Prod.mk 4 do throwError "expected a source/retained pair"
    let source := pair.getAppArgs[2]!
    let some retained ← getArrayLit? pair.getAppArgs[3]!
      | throwError "expected a literal array of retained predicates"
    match failure? with
    | none =>
      checkPlan source retained
      checkReplacement source retained true
    | some fragment => rejectPlan source retained fragment

/-! Both native vector interfaces, every built-in quadratic shape, and symbolic
or empty dimensions preserve the original decision space. -/

run_cmd liftTermElabM do
  expectPlan (← `(fun x : ℝ => (x + 1)^2 ≤ 3))
  expectPlan (← `(fun x : ℝ => 3 ≥ (x + 1)^2))
  expectPlan (← `(fun n : ℕ => fun x : Fin n → ℝ => ‖WithLp.toLp 2 x‖ ≤ 3)) 1
  expectPlan (← `(fun n : ℕ => fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ≤ 3)) 1
  expectPlan (← `(fun n : ℕ => fun x : Fin n → ℝ => ‖WithLp.toLp 2 x‖^2 ≤ 3)) 1
  expectPlan (← `(fun n : ℕ => fun x : EuclideanSpace ℝ (Fin n) => ‖x‖^2 ≤ 3)) 1
  expectPlan (← `(fun n : ℕ => fun x : Fin n → ℝ => (∑ i, (x i + 1)^2) ≤ 3)) 1
  expectPlan (← `(fun (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) =>
    fun x : (Fin n → ℝ) × ℝ => ‖WithLp.toLp 2 (A.mulVec x.1 + b)‖ ≤ x.2)) 4
  expectPlan (← `(fun x : EuclideanSpace ℝ (Fin 0) => ‖x‖ ≤ -1))
  expectPlan (← `(fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖^2 ≤ -1))
  expectPlan (← `(fun x : Fin 0 → ℝ => (∑ i, (x i)^2) ≤ -1))
  expectPlan (← `(fun x : ℝ => x^2 / (3 / 2) ≤ 1))
  expectPlan (← `(fun n : ℕ => fun x : Fin n → ℝ => (∑ i, (x i)^2) / 2 ≤ 3)) 1
  expectPlan (← `(fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖^2 / 2 ≤ 3))
  expectPlan (← `(fun [LT ℝ] => fun x : ℝ => x^2 / 2 ≤ 3)) 1
  expectPlan (← `(fun [LE ℝ] => fun x : ℝ =>
    @LE.le ℝ nativeLE (x^2 / 2) 3)) 1
  expectPlan (← `(fun [Preorder ℝ] => fun x : ℝ =>
    @LE.le ℝ nativeLE (x^2 / 2) 3)) 1
  expectPlan (← `(fun [PartialOrder ℝ] => fun x : ℝ =>
    @LE.le ℝ nativeLE (x^2 / 2) 3)) 1
  expectPlan (← `(fun [LinearOrder ℝ] => fun x : ℝ =>
    @LE.le ℝ nativeLE (x^2 / 2) 3)) 1
  expectPlan (← `(fun [NormedAddCommGroup ℝ] => fun x : ℝ => x^2 ≤ 3)) 1

/-! Margins retain their source position and conjunction path. An unusable
candidate must not prevent a later positive margin from certifying a quotient. -/

run_cmd liftTermElabM do
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)
    #[fun x : ℝ × ℝ => (1 : ℝ) ≤ x.2]))
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => 3 ≥ x.1^2 / x.2)
    #[fun x : ℝ × ℝ => x.1^3 ≤ 9 ∧ ((x.2 ≥ 1) ∧ x.1 ≤ 8)]))
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)
    #[fun x : ℝ × ℝ => 0 ≤ x.2,
      fun x : ℝ × ℝ => (1 / 3 : ℝ) ≤ x.2,
      fun x : ℝ × ℝ => 2 ≤ x.2]))
  contextCase (← `(fun (ε : ℝ) (_ : 0 < ε) =>
    ((fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3),
      #[fun x : ℝ × ℝ => ε ≤ x.2]))) 2
  contextCase (← `(fun ε : ℝ =>
    ((fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3),
      #[fun x : ℝ × ℝ => ε ≤ x.2, fun x : ℝ × ℝ => 1 ≤ x.2]))) 1
  contextCase (← `(fun n : ℕ =>
    ((fun x : (Fin n → ℝ) × ℝ => (∑ i, (x.1 i)^2) / x.2 ≤ 3),
      #[fun x : (Fin n → ℝ) × ℝ => 1 ≤ x.2]))) 1
  contextCase (← `(Prod.mk (fun x : EuclideanSpace ℝ (Fin 2) × ℝ => ‖x.1‖^2 / x.2 ≤ 3)
    #[fun x : EuclideanSpace ℝ (Fin 2) × ℝ => 1 ≤ x.2]))
  contextCase (← `(fun a : ℝ =>
    ((fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3),
      #[fun x : ℝ × ℝ =>
        let h : 0 < Real.exp a := Real.exp_pos a
        Real.exp a ≤ x.2]))) 1
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)
    #[fun x : ℝ × ℝ => let y := x.2; 1 ≤ y]))
  expectPlan (← `(fun (ε : ℝ) (_ : 0 < ε) => fun x : ℝ => x^2 / ε ≤ 3)) 2
  expectPlan (← `(fun a : ℝ => fun x : ℝ =>
    let h : 0 < Real.exp a := Real.exp_pos a
    x^2 / Real.exp a ≤ 3)) 1
  expectPlan (← `(fun a : ℝ => fun x : ℝ =>
    let h : Real.exp a ≠ 0 := Real.exp_ne_zero a
    (x / Real.exp a)^2 ≤ 1)) 1

run_cmd liftTermElabM do
  expectRejected (← `(fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)) "margin"
  expectRejected (← `(fun x : ℝ => x^2 / 0 ≤ 3)) "margin"
  expectRejected (← `(fun x : ℝ => x^2 / (-1) ≤ 3)) "margin"
  expectRejected (← `(fun [LT ℝ] (ε : ℝ) (_ : 0 < ε) =>
    fun x : ℝ => x^2 / ε ≤ 3)) "margin" 3
  expectRejected (← `(fun x : (Fin 0 → ℝ) × ℝ => (∑ i, (x.1 i)^2) / x.2 ≤ 3)) "margin"
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)
    #[fun x : ℝ × ℝ => 0 < x.2])) (failure? := some "margin")
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)
    #[fun x : ℝ × ℝ => 0 ≤ x.2])) (failure? := some "margin")
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)
    #[fun x : ℝ × ℝ => @LE.le ℝ ⟨fun _ _ => True⟩ 1 x.2])) (failure? := some "margin")
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)
    #[fun x : ℝ × ℝ => 1 ≤ x.2 + 1])) (failure? := some "margin")
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3)
    #[fun x : ℝ × ℝ => 0 < x.1 ∧ x.1 ≤ x.2])) (failure? := some "margin")
  contextCase (← `(fun (ε : ℝ) (_ : 0 ≤ ε) =>
    ((fun x : ℝ × ℝ => x.1^2 / x.2 ≤ 3),
      #[fun x : ℝ × ℝ => ε ≤ x.2]))) 2 (some "margin")

/-! Source operation instances, polarity, and affine coordinates are checked
independently of coincidence on particular values. -/

run_cmd liftTermElabM do
  expectRejected (← `(fun x : ℝ => x^2 = 3)) "upper bound"
  expectRejected (← `(fun x : ℝ => 3 ≤ x^2)) "upper-bound polarity"
  expectRejected (← `(fun x : ℝ => x^3 ≤ 3)) "exponent 2"
  expectRejected (← `(fun x : ℝ => (x^2)^2 ≤ 3)) "affine"
  expectRejected (← `(fun x : ℝ => x^2 ≤ x*x)) "affine"
  expectRejected (← `(fun x : Fin 2 → ℝ => ‖x‖^2 ≤ 3)) "Euclidean norm"
  expectRejected (← `(fun x : EuclideanSpace ℝ Bool => ‖x‖ ≤ 3)) "EuclideanSpace"
  expectRejected (← `(fun x : Fin 2 → ℝ => (∑ i ∈ ({0} : Finset (Fin 2)), (x i)^2) ≤ 3))
    "complete selected bound"
  expectRejected (← `(fun x : ℝ =>
    @HPow.hPow ℝ ℕ ℝ ⟨fun a _ => a*a⟩ x 2 ≤ 3)) "instance"
  expectRejected (← `(fun x : EuclideanSpace ℝ (Fin 2) =>
    @Norm.norm (EuclideanSpace ℝ (Fin 2)) ⟨fun _ => 0⟩ x ≤ 3)) "instance"
  expectRejected (← `(fun x : ℝ =>
    @HDiv.hDiv ℝ ℝ ℝ ⟨fun a _ => a⟩ (x^2) 2 ≤ 3)) "instance"
  expectRejected (← `(fun x : ℝ =>
    @LE.le ℝ ⟨fun a b => a ≤ b + 1⟩ (x^2) 3)) "order instance"
  expectRejected (← `(fun a : AddCommMonoid ℝ => fun x : Fin 2 → ℝ =>
    @Finset.sum (Fin 2) ℝ a Finset.univ (fun i => (x i)^2) ≤ 3)) "instance" 1
  contextCase (← `(Prod.mk (fun x : ℝ × ℝ => x.1^2 / (x.2^2 + 1) ≤ 3)
    #[fun x : ℝ × ℝ => 1 ≤ x.2^2 + 1])) (failure? := some "affine")

/-! Missing inputs remain unresolved; successful and failed planning both
restore the caller's metavariable state. -/

run_cmd liftTermElabM do
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => x^2 ≤ c))
  let missing ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  if ← isCandidate (mkApp builder missing) then
    throwError "candidate matching accepted an unresolved predicate"
  rejectPlan (mkApp builder missing) #[] "unresolved"
  if ← missing.mvarId!.isAssigned then throwError "planner assigned an unresolved bound"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "failed planning leaked scratch metavariables"
  withLetDecl `hiddenBound (mkConst ``Real) missing fun hidden =>
    rejectPlan (mkApp builder hidden) #[] "unresolved"
  let source ← elaborate (← `(fun x : ℝ => x^2 / 2 ≤ 3))
  let retainedBuilder ← elaborate (← `(fun c : ℝ => fun x : ℝ => c ≤ x))
  rejectPlan source #[mkApp retainedBuilder missing] "unresolved"
  let before ← getMCtx
  checkPlan source
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "successful planning leaked scratch metavariables"
  if ← missing.mvarId!.isAssigned then throwError "planner assigned an unrelated hole"

/-! Ordinary function-space norms continue through the L∞ planner; only their
explicit L2 wrapper selects second-order planning. -/

run_cmd liftTermElabM do
  let ordinary ← elaborate (← `(fun x : Fin 2 → ℝ => ‖x‖ ≤ 3))
  let euclidean ← elaborate (← `(fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ≤ 3))
  if ← isCandidate ordinary then throwError "ordinary L∞ norm was routed to the SOC planner"
  unless ← isCandidate euclidean do throwError "native Euclidean norm was not selected"

end MorewTest.Conic.SecondOrderElab
