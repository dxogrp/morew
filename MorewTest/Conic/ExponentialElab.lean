/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.Support

/-!
# Typed exponential planning and domain certificates

Every success is checked against its exact source, decision domain, ordered row
conjunction, and semantic cone rows. Domain facts come from retained margins;
finite lifts keep their nonempty-index proof separate from their coordinates.
-/

namespace MorewTest.Conic.ExponentialElab

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open MorewTest.Affine
open Morew.Elab.Conic

private def conjunction (rows : Array Expr) : Expr :=
  if rows.isEmpty then mkConst ``True
  else rows.pop.toList.foldr (mkApp2 (mkConst ``And)) rows.back!

private def checkRows (domain : Expr) (rows : Array Expr) (certificates : Array RowResult) :
    MetaM Unit := do
  unless rows.size == certificates.size do throwError "missing certified exponential row"
  for row in rows, certificate in certificates do
    let constraintType ← whnf (← inferType certificate.constraint)
    let expected ← withLocalDeclD `point domain fun point => do
      let holds := mkAppN
        (mkConst ``Morew.Conic.Constraint.Holds constraintType.getAppFn.constLevels!)
        (constraintType.getAppArgs ++ #[certificate.constraint, point])
      mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp row point])
    unless ← isDefEq (← inferType certificate.pointwiseIff) expected do
      throwError "the checked cone row does not match its presentation predicate"
    for expression in #[certificate.constraint, certificate.pointwiseIff] do
      if expression.hasMVar || expression.hasSorry then throwError "incomplete cone certificate"
      checkWithKernel expression

private def rowCone (constraint : Expr) : MetaM Expr := do
  let type ← whnf (← inferType constraint)
  return mkAppN (mkConst ``Morew.Conic.Constraint.cone type.getAppFn.constLevels!)
    (type.getAppArgs ++ #[constraint])

private def checkPlan (source : Expr) (retained : Array Expr := #[])
    (contextual : Bool := false) (auxiliary : Bool := false) : MetaM Unit := do
  let domain ← Morew.Elab.Rewrite.Plan.predicateDomain source
  match ← Rewrite.planUnique source retained with
  | .error error => throwError "expected an exponential plan: {error.reason}"
  | .ok (.inl result) =>
      if contextual then throwError "retained domain evidence escaped its contextual certificate"
      unless result.auxiliary?.isSome == auxiliary do throwError "unexpected auxiliary decision space"
      let expectedRows := if auxiliary then 2 else 1
      unless result.rowPredicates.size == expectedRows do throwError "unexpected generated row count"
      discard <| Morew.Elab.Rewrite.Plan.checkLift source result.lift
      checkWithKernel result.targetIff
      if result.lift.hasMVar || result.targetIff.hasMVar || result.lift.hasSorry then
        throwError "incomplete exact exponential lift"
      let nextDomain ← match result.auxiliary? with
        | none => pure domain
        | some auxiliary => mkAppM ``Prod #[domain, auxiliary]
      unless ← isDefEq result.nextDomain nextDomain do throwError "wrong lifted decision domain"
      checkRows result.nextDomain result.rowPredicates result.certifiedRows
      let some firstRow := result.certifiedRows[0]? | throwError "missing first certified row"
      if let some auxiliary := result.auxiliary? then
        let .forallE _ index range _ ← whnf auxiliary
          | throwError "exponential auxiliary is not a finite real vector"
        let index ← whnf index
        unless index.isAppOfArity ``Fin 1 && (← whnf range).isConstOf ``Real do
          throwError "exponential auxiliary is not Fin n → ℝ"
        lambdaTelescope result.rowPredicates[0]! fun _ body =>
          unless body.isForall do throwError "the finite membership row was expanded"
        let cone ← rowCone firstRow.constraint
        let expectedCone ← mkAppM ``Morew.Conic.Cone.exponentialProduct #[index.getAppArgs[0]!]
        unless ← isDefEq cone expectedCone do throwError "family was not certified as a product cone"
      else
        let cone ← rowCone firstRow.constraint
        unless ← isDefEq cone (mkConst ``Morew.Conic.Cone.exponential) do
          throwError "scalar rewrite was not certified as an exponential cone"
  | .ok (.inr result) =>
      unless contextual && !auxiliary do throwError "unexpected contextual exponential plan"
      unless ← isDefEq result.domain domain do throwError "contextual rewrite changed the domain"
      unless result.rowPredicates.size == 1 do throwError "contextual rewrite added extra rows"
      let expected ← withLocalDeclD `point domain fun point => do
        let remainder := conjunction (retained.map (mkApp · point))
        let rows := conjunction (result.rowPredicates.map (mkApp · point))
        mkForallFVars #[point]
          (← mkArrow remainder (← mkAppM ``Iff #[mkApp source point, rows]))
      unless ← isDefEq (← inferType result.conditionalIff) expected do
        throwError "contextual certificate changed the exact source or retained conjunction"
      if result.conditionalIff.hasMVar || result.conditionalIff.hasSorry then
        throwError "incomplete contextual exponential certificate"
      checkWithKernel result.conditionalIff
      checkRows domain result.rowPredicates result.certifiedRows

private def rejectPlan (source : Expr) (retained : Array Expr) (fragment : String) :
    MetaM Unit := do
  let .error error ← Rewrite.planUnique source retained
    | throwError "unsupported exponential predicate was accepted: {source}; retained: {retained}"
  unless (← error.reason.toString).contains fragment do
    throwError "expected diagnostic containing {fragment}, got {error.reason}"

private def expectPlan (stx : TSyntax `term) (parameterCount : Nat := 0)
    (auxiliary : Bool := false) : TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression parameterCount fun _ source =>
    checkPlan source (auxiliary := auxiliary)

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
    let some retained ← getArrayLit? pair.getAppArgs[3]!
      | throwError "expected a literal array of retained predicates"
    match failure? with
    | none => checkPlan pair.getAppArgs[2]! retained (contextual := true)
    | some fragment => rejectPlan pair.getAppArgs[2]! retained fragment

private noncomputable abbrev nativeLE : LE ℝ := inferInstance

run_cmd liftTermElabM do
  expectPlan (← `(fun p : ℝ × ℝ => Real.exp (2 * p.1 + 1) ≤ p.2 / 2))
  expectPlan (← `(fun p : ℝ × ℝ => p.2 ≥ Real.exp p.1))
  expectPlan (← `(fun t : ℝ => t ≤ Real.log (3 / 2)))
  expectPlan (← `(fun (a : ℝ) (_ : 0 < a) => fun t : ℝ => t ≤ Real.log a)) 2
  expectPlan (← `(fun t : ℝ => Morew.Fn.relativeEntropy 0 2 ≤ t))
  expectPlan (← `(fun t : ℝ => (1 / 2 : ℝ) * Real.log ((1 / 2) / 2) ≤ t))
  expectPlan (← `(fun (a b : ℝ) (_ : 0 ≤ a) (_ : 0 < b) =>
    fun t : ℝ => Morew.Fn.relativeEntropy a b ≤ t)) 4
  expectPlan (← `(fun p : ℝ × ℝ => Morew.Fn.softplus (2 * p.1 - 1) ≤ p.2))
    (auxiliary := true)
  expectPlan (← `(fun p : ℝ × ℝ => Real.log (1 + Real.exp p.1) ≤ p.2))
    (auxiliary := true)
  expectPlan (← `(fun p : ℝ × ℝ => p.2 ≥ Real.log (1 + Real.exp p.1)))
    (auxiliary := true)
  expectPlan (← `(fun p : (Fin 1 → ℝ) × ℝ => Morew.Fn.logSumExp p.1 ≤ p.2))
    (auxiliary := true)
  expectPlan (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    Real.log (∑ i, Real.exp (2 * p.1 i + 1)) ≤ p.2)) (auxiliary := true)
  expectPlan (← `(fun [LE ℝ] => fun p : ℝ × ℝ =>
    @LE.le ℝ nativeLE (Real.exp p.1) p.2)) 1
  expectPlan (← `(fun [LT ℝ] => fun t : ℝ => t ≤ Real.log 2)) 1
  expectPlan (← `(fun [NormedAddCommGroup ℝ] => fun p : ℝ × ℝ =>
    Real.exp p.1 ≤ p.2)) 1
  -- The logarithm is a constant bound here, so no logarithm-domain hypothesis
  -- may be imposed on a successful upper-exponential representation.
  expectPlan (← `(fun x : ℝ => Real.exp x ≤ Real.log 0))

/-! Nonempty dimensions can be certified by an exact local fact or standard
finite-index evidence. No positive-real domain assumption is needed for LSE. -/

run_cmd liftTermElabM do
  expectPlan (← `(fun (n : ℕ) (_ : 0 < n) => fun p : (Fin n → ℝ) × ℝ =>
    Morew.Fn.logSumExp p.1 ≤ p.2)) 2 true
  expectPlan (← `(fun (n : ℕ) (_ : n ≠ 0) => fun p : (Fin n → ℝ) × ℝ =>
    Morew.Fn.logSumExp p.1 ≤ p.2)) 2 true
  expectPlan (← `(fun (n : ℕ) [NeZero n] => fun p : (Fin n → ℝ) × ℝ =>
    Real.log (∑ i, Real.exp (p.1 i)) ≤ p.2)) 2 true
  expectPlan (← `(fun (n : ℕ) [Nonempty (Fin n)] => fun p : (Fin n → ℝ) × ℝ =>
    Morew.Fn.logSumExp p.1 ≤ p.2)) 2 true
  expectPlan (← `(fun (n : ℕ) (_ : Nonempty (Fin n)) => fun p : (Fin n → ℝ) × ℝ =>
    Morew.Fn.logSumExp p.1 ≤ p.2)) 2 true
  expectPlan (← `(fun (n : ℕ) (_ : NeZero n) => fun p : (Fin n → ℝ) × ℝ =>
    Morew.Fn.logSumExp p.1 ≤ p.2)) 2 true
  expectPlan (← `(fun (n : ℕ) (_ : 0 < n) =>
    fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      Morew.Fn.logSumExp (WithLp.ofLp p.1) ≤ p.2)) 2 true
  expectPlan (← `(fun (n m : ℕ) (_ : 0 < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) =>
    fun p : (Fin n → ℝ) × ℝ => Morew.Fn.logSumExp (A.mulVec p.1 + b) ≤ p.2)) 5 true

run_cmd liftTermElabM do
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ => p.2 ≤ Real.log p.1)
    #[fun p : ℝ × ℝ => 1 ≤ p.1]))
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ => Real.log p.1 ≥ p.2)
    #[fun p : ℝ × ℝ => Real.exp (p.2 ^ 2) ≤ 10 ∧ (p.1 ≥ 1 / 2 ∧ p.2 ≤ 3)]))
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ => p.2 ≤ Real.log p.1)
    #[fun p : ℝ × ℝ => 0 ≤ p.1, fun p : ℝ × ℝ => 1 / 3 ≤ p.1,
      fun p : ℝ × ℝ => 2 ≤ p.1]))
  contextCase (← `(fun ε : ℝ =>
    ((fun p : ℝ × ℝ => p.2 ≤ Real.log p.1),
      #[fun p : ℝ × ℝ => ε ≤ p.1, fun p : ℝ × ℝ => 1 ≤ p.1]))) 1
  contextCase (← `(fun (ε : ℝ) (_ : 0 < ε) =>
    ((fun p : ℝ × ℝ => p.2 ≤ Real.log p.1), #[fun p : ℝ × ℝ => ε ≤ p.1]))) 2
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ × ℝ =>
    Morew.Fn.relativeEntropy p.1 p.2.1 ≤ p.2.2)
    #[fun p : ℝ × ℝ × ℝ => 0 ≤ p.1, fun p : ℝ × ℝ × ℝ => 1 ≤ p.2.1]))
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ × ℝ =>
    p.2.2 ≥ p.1 * Real.log (p.1 / p.2.1))
    #[fun p : ℝ × ℝ × ℝ => p.1 ≥ 0 ∧ (p.1 ^ 2 ≤ 100 ∧ p.2.1 ≥ 1)]))
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ =>
    Morew.Fn.relativeEntropy 0 p.1 ≤ p.2)
    #[fun p : ℝ × ℝ => 1 ≤ p.1]))
  contextCase (← `(fun a : ℝ =>
    ((fun p : ℝ × ℝ => p.2 ≤ Real.log p.1),
      #[fun p : ℝ × ℝ => let h : 0 < Real.exp a := Real.exp_pos a; Real.exp a ≤ p.1]))) 1

/-! A supported composite may also be a constant lower bound for a logarithm.
Try complete certified orientations: a failed upper representation must not
hide the valid same-domain lower-log representation or retain its auxiliary. -/

run_cmd liftTermElabM do
  contextCase (← `(Prod.mk (fun x : ℝ => Morew.Fn.softplus 0 ≤ Real.log x)
    #[fun x : ℝ => 1 ≤ x]))
  contextCase (← `(Prod.mk (fun x : ℝ => Real.log (1 + Real.exp 0) ≤ Real.log x)
    #[fun x : ℝ => 1 ≤ x]))
  contextCase (← `(Prod.mk (fun x : ℝ => Real.exp 0 ≤ Real.log x)
    #[fun x : ℝ => 1 ≤ x]))
  contextCase (← `(Prod.mk (fun x : ℝ =>
    Morew.Fn.logSumExp (![0, 0] : Fin 2 → ℝ) ≤ Real.log x)
    #[fun x : ℝ => 1 ≤ x]))
  contextCase (← `(Prod.mk (fun x : ℝ =>
    Morew.Fn.logSumExp (0 : Fin 0 → ℝ) ≤ Real.log x)
    #[fun x : ℝ => 1 ≤ x]))
  contextCase (← `(Prod.mk (fun x : ℝ => Morew.Fn.relativeEntropy (-1) 0 ≤ Real.log x)
    #[fun x : ℝ => 1 ≤ x]))
  contextCase (← `(Prod.mk (fun x : ℝ => (-1 : ℝ) * Real.log ((-1) / 0) ≤ Real.log x)
    #[fun x : ℝ => 1 ≤ x]))
  contextCase (← `(Prod.mk (fun x : ℝ => Real.exp x ≤ Real.log x)
    #[fun x : ℝ => 1 ≤ x])) (failure? := some "affine")

private noncomputable def hiddenExp (a : ℝ) := Real.exp a
private noncomputable def hiddenSoftplus (a : ℝ) := Morew.Fn.softplus a

run_cmd liftTermElabM do
  expectRejected (← `(fun p : ℝ × ℝ => p.2 ≤ Real.log p.1)) "margin"
  expectRejected (← `(fun t : ℝ => t ≤ Real.log 0)) "margin"
  expectRejected (← `(fun p : ℝ × ℝ × ℝ =>
    Morew.Fn.relativeEntropy p.1 p.2.1 ≤ p.2.2)) "nonnegative"
  expectRejected (← `(fun t : ℝ => Morew.Fn.relativeEntropy 0 0 ≤ t)) "margin"
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ => p.2 ≤ Real.log p.1)
    #[fun p : ℝ × ℝ => 0 < p.1])) (failure? := some "margin")
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ => p.2 ≤ Real.log p.1)
    #[fun p : ℝ × ℝ => 0 ≤ p.1])) (failure? := some "margin")
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ × ℝ => p.2.2 ≤ Real.log p.1)
    #[fun p : ℝ × ℝ × ℝ => 1 ≤ p.2.1, fun p : ℝ × ℝ × ℝ => p.2.1 ≤ p.1]))
    (failure? := some "margin")
  contextCase (← `(fun (ε : ℝ) (_ : 0 ≤ ε) =>
    ((fun p : ℝ × ℝ => p.2 ≤ Real.log p.1), #[fun p : ℝ × ℝ => ε ≤ p.1])))
    2 (some "margin")
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ => p.2 ≤ Real.log p.1)
    #[fun p : ℝ × ℝ => @LE.le ℝ ⟨fun _ _ => True⟩ 1 p.1])) (failure? := some "margin")
  contextCase (← `(Prod.mk (fun p : ℝ × ℝ × ℝ =>
    Morew.Fn.relativeEntropy p.1 p.2.1 ≤ p.2.2)
    #[fun p : ℝ × ℝ × ℝ => 0 < p.1, fun p : ℝ × ℝ × ℝ => 1 ≤ p.2.1]))
    (failure? := some "nonnegative")
  expectRejected (← `(fun p : (Fin 0 → ℝ) × ℝ => Morew.Fn.logSumExp p.1 ≤ p.2)) "nonempty"
  expectRejected (← `(fun n : ℕ => fun p : (Fin n → ℝ) × ℝ =>
    Morew.Fn.logSumExp p.1 ≤ p.2)) "nonempty" 1
  expectRejected (← `(fun (n m : ℕ) (_ : 0 < m) => fun p : (Fin n → ℝ) × ℝ =>
    Morew.Fn.logSumExp p.1 ≤ p.2)) "nonempty" 3
  expectRejected (← `(fun p : ℝ × ℝ =>
    Morew.Fn.logSumExp (fun _i : Fin (if p.1 ≤ 0 then 1 else 2) => p.1) ≤ p.2))
    "dimension"
  expectRejected (← `(fun p : ℝ × ℝ => p.2 ≤ Real.exp p.1)) "bound"
  expectRejected (← `(fun p : ℝ × ℝ => Real.exp p.1 = p.2)) "polarity"
  expectRejected (← `(fun p : ℝ × ℝ => Morew.Fn.softplus p.1 ≥ p.2)) "polarity"
  expectRejected (← `(fun p : ℝ × ℝ => Real.log p.1 ≤ p.2)) "does not match point.1"
  expectRejected (← `(fun p : ℝ × ℝ => hiddenExp p.1 ≤ p.2)) "supported"
  expectRejected (← `(fun p : ℝ × ℝ => hiddenSoftplus p.1 ≤ p.2)) "supported"
  expectRejected (← `(fun p : ℝ × ℝ => Real.exp (p.1 * p.1) ≤ p.2)) "affine"
  expectRejected (← `(fun p : ℝ × ℝ => Morew.Fn.softplus p.1 ≤ p.2 * p.2)) "affine"
  expectRejected (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    Morew.Fn.logSumExp (fun i => (p.1 i)^2) ≤ p.2)) "affine"
  expectRejected (← `(fun p : (Fin 2 → ℝ) × ℝ =>
    Real.log (∑ i ∈ ({0} : Finset (Fin 2)), Real.exp (p.1 i)) ≤ p.2)) "Finset.univ does not match {0}"
  expectRejected (← `(fun p : ℝ × ℝ =>
    @LE.le ℝ ⟨fun _ _ => True⟩ (Real.exp p.1) p.2)) "instance"
  expectRejected (← `(fun p : ℝ × ℝ =>
    Real.log (@HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a + b + 1⟩ 1 (Real.exp p.1)) ≤ p.2)) "instance"
  expectRejected (← `(fun t : ℝ =>
    @HMul.hMul ℝ ℝ ℝ ⟨fun _ b => b⟩ 1 (Real.log (1 / 2)) ≤ t)) "instance"
  expectRejected (← `(fun t : ℝ =>
    (1 : ℝ) * Real.log (@HDiv.hDiv ℝ ℝ ℝ ⟨fun a _ => a / 2⟩ 1 2) ≤ t)) "instance"
  expectRejected (← `(fun (a : AddCommMonoid ℝ) => fun p : (Fin 2 → ℝ) × ℝ =>
    Real.log (@Finset.sum (Fin 2) ℝ a Finset.univ (fun i => Real.exp (p.1 i))) ≤ p.2))
    "instance" 1

/-! The shared contextual adapter must retain row conjunctions beyond the
singleton shape used by second-order rewrites. -/

run_cmd liftTermElabM do
  let domain := Lean.mkConst ``Real
  let source ← elaborate (← `(fun _x : ℝ => True))
  let proof ← elaborate (← `(fun (_x : ℝ) (_h : True) => (Iff.rfl : True ↔ True)))
  let .inl result ← Plan.prepareContextual source #[] {
      domain, rowPredicates := #[], certifiedRows := #[], conditionalIff := proof }
    | throwError "an unconditional empty replacement remained contextual"
  discard <| Morew.Elab.Rewrite.Plan.checkLift source result.lift
  checkWithKernel result.targetIff
  unless result.rowPredicates.isEmpty && result.auxiliary?.isNone do
    throwError "empty replacement gained rows or an auxiliary"
  let source ← elaborate (← `(fun x : ℝ => x ≤ 1 ∧ 0 ≤ x))
  let rows ← #[← elaborate (← `(fun x : ℝ => x ≤ 1)),
    ← elaborate (← `(fun x : ℝ => 0 ≤ x))].mapM pure
  let proof ← elaborate (← `(fun (x : ℝ) (_h : True) =>
    (Iff.rfl : (x ≤ 1 ∧ 0 ≤ x) ↔ (x ≤ 1 ∧ 0 ≤ x))))
  let .inl result ← Plan.prepareContextual source #[] {
      domain, rowPredicates := rows, certifiedRows := ← Plan.certifyRows rows,
      conditionalIff := proof }
    | throwError "an unconditional multi-row replacement remained contextual"
  discard <| Morew.Elab.Rewrite.Plan.checkLift source result.lift
  checkWithKernel result.targetIff
  checkRows domain result.rowPredicates result.certifiedRows
  unless result.rowPredicates.size == 2 && result.auxiliary?.isNone do
    throwError "multi-row replacement changed shape"

run_cmd liftTermElabM do
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => Real.exp x ≤ c))
  let missing ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  rejectPlan (mkApp builder missing) #[] "unresolved"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "failed planning leaked scratch metavariables"
  withLetDecl `hiddenBound (mkConst ``Real) missing fun hidden =>
    rejectPlan (mkApp builder hidden) #[] "unresolved"
  let source ← elaborate (← `(fun x : ℝ => Real.exp x ≤ 3))
  let wrongDomain ← elaborate (← `(fun p : ℝ × ℝ => 1 ≤ p.1))
  rejectPlan source #[wrongDomain] "different decision domain"
  let retainedBuilder ← elaborate (← `(fun c : ℝ => fun x : ℝ => c ≤ x))
  rejectPlan source #[mkApp retainedBuilder missing] "unresolved"
  let before ← getMCtx
  checkPlan source
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "successful planning leaked scratch metavariables"
  if ← missing.mvarId!.isAssigned then throwError "planner assigned an unrelated hole"

end MorewTest.Conic.ExponentialElab
