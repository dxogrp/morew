/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Plan
import MorewTest.Environment

/-!
# Checked finite families of power cones

Grouped rows retain exact, possibly index-dependent parameters and their range
proofs. Empty families still validate membership instances and affine coordinates.
-/

namespace MorewTest.Conic.PowerFamilies

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Conic
open scoped ENNReal

noncomputable section

example (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    (Cone.powerProduct n α hα).Space = (Fin n → (ℝ × ℝ × ℝ)) := rfl

example (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    FiniteDimensional ℝ (Cone.powerProduct n α hα).Space := inferInstance

example (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1)
    (v : Fin n → (ℝ × ℝ × ℝ)) :
    v ∈ (Cone.powerProduct n α hα).carrier ↔ ∀ i, v i ∈ POW (α i) :=
  Cone.mem_powerProduct α hα v

example (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    IsClosed (↑(Cone.powerProduct n α hα).carrier : Set (Cone.powerProduct n α hα).Space) :=
  Cone.isClosed_powerProduct n α hα

example (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    Convex ℝ (↑(Cone.powerProduct n α hα).carrier : Set (Cone.powerProduct n α hα).Space) :=
  (Cone.powerProduct n α hα).carrier.convex

example (v : Fin 0 → (ℝ × ℝ × ℝ)) :
    v ∈ (Cone.powerProduct 0 (fun _ => 0) (fun i => Fin.elim0 i)).carrier := by
  intro i
  exact Fin.elim0 i

structure CertifiedRow {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (predicate : X → Prop) where
  row : Morew.Conic.Constraint X
  equivalent : ∀ x, row.Holds x ↔ predicate x

private def elaborate (source : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

elab "certified_power_family% " source:term : term => do
  let predicate ← elaborate source
  let .ok result ← Morew.Elab.Conic.normalizeRow predicate
    | throwError "expected a checked finite power family"
  for expression in #[result.constraint, result.pointwiseIff] do
    if expression.hasMVar || expression.hasSorry then
      throwError "power family has an incomplete certificate"
    checkWithKernel expression
  mkAppM ``CertifiedRow.mk #[result.constraint, result.pointwiseIff]

def varying (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    CertifiedRow (fun x : Fin n → ℝ => ∀ i : Fin n, (x i, 1, 2 * x i - 1) ∈ POW (α i)) :=
  certified_power_family% (fun x : Fin n → ℝ =>
    ∀ i : Fin n, (x i, 1, 2 * x i - 1) ∈ POW (α i))

example (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    (varying n α hα).row.cone = Cone.powerProduct n α hα := rfl

def bundled (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    CertifiedRow (fun x : Fin n → ℝ =>
      ∀ i, (x i, 1, x i) ∈ (Cone.power (α i) (hα i)).carrier) :=
  certified_power_family% (fun x : Fin n → ℝ =>
    ∀ i, (x i, 1, x i) ∈ (Cone.power (α i) (hα i)).carrier)

def product (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    CertifiedRow (fun x : Fin n → ℝ =>
      (fun i => (x i + 1, 1, x i)) ∈ (Cone.powerProduct n α hα).carrier) :=
  certified_power_family% (fun x : Fin n → ℝ =>
    (fun i => (x i + 1, 1, x i)) ∈ (Cone.powerProduct n α hα).carrier)

def constant (n : Nat) : CertifiedRow (fun x : Fin n → ℝ =>
    ∀ i, (x i, 1, x i + 1) ∈ POW (1 / 2 : ℝ)) :=
  certified_power_family% (fun x : Fin n → ℝ =>
    ∀ i, (x i, 1, x i + 1) ∈ POW (1 / 2 : ℝ))

example (x : Fin 0 → ℝ) : (constant 0).row.Holds x := by
  apply ((constant 0).equivalent x).mpr
  intro i
  exact Fin.elim0 i

example (x : Fin 1 → ℝ) : (constant 1).row.Holds x ↔
    (x 0, 1, x 0 + 1) ∈ POW (1 / 2 : ℝ) := by
  rw [(constant 1).equivalent]
  simp only [Fin.forall_fin_one]

def conjunctionEvidence (n : Nat) (α : Fin n → ℝ)
    (hα : True ∧ ∀ i, True ∧ 0 < α i ∧ α i < 1) :
    CertifiedRow (fun x : Fin n → ℝ => ∀ i, (x i, 1, x i) ∈ POW (α i)) :=
  certified_power_family% (fun x : Fin n → ℝ => ∀ i, (x i, 1, x i) ∈ POW (α i))

-- The unused coordinate binding must not enter the product-cone parameter or
-- proof. Its dependent value still stays available to affine reification.
def scopedLets (n : Nat) (α a : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1) :
    CertifiedRow (fun x : Fin n → ℝ => ∀ i,
      let exponent := α i
      let _range : 0 < exponent ∧ exponent < 1 := hα i
      let _nonzero : Real.exp (a i) ≠ 0 := Real.exp_ne_zero (a i)
      let coordinate := x i / Real.exp (a i)
      (coordinate, 1, x i + 1) ∈ POW exponent) :=
  certified_power_family% (fun x : Fin n → ℝ => ∀ i,
    let exponent := α i
    let _range : 0 < exponent ∧ exponent < 1 := hα i
    let _nonzero : Real.exp (a i) ≠ 0 := Real.exp_ne_zero (a i)
    let coordinate := x i / Real.exp (a i)
    (coordinate, 1, x i + 1) ∈ POW exponent)

def euclidean (n : Nat) : CertifiedRow (fun x : EuclideanSpace ℝ (Fin n) =>
    ∀ i, (WithLp.ofLp x i, 1, 2 - WithLp.ofLp x i) ∈ POW (1 / 3 : ℝ)) :=
  certified_power_family% (fun x : EuclideanSpace ℝ (Fin n) =>
    ∀ i, (WithLp.ofLp x i, 1, 2 - WithLp.ofLp x i) ∈ POW (1 / 3 : ℝ))

private theorem inverseRange (q : ℝ) (hq : 1 < q) : 0 < 1 / q ∧ 1 / q < 1 := by
  refine ⟨one_div_pos.mpr (lt_trans zero_lt_one hq), ?_⟩
  simpa using one_div_lt_one_div_of_lt zero_lt_one hq

-- The symbolic inverse range cannot be inferred by numerical evaluation or
-- conjunction projection from `hq`; the index-local proof let is essential.
def localRange (n : Nat) (q : Fin n → ℝ) (hq : ∀ i, 1 < q i) :
    CertifiedRow (fun x : Fin n → ℝ => ∀ i,
      let exponent := 1 / q i
      let _range : 0 < exponent ∧ exponent < 1 := inverseRange (q i) (hq i)
      let coordinate := x i + 1
      (coordinate, 1, x i) ∈ POW exponent) :=
  certified_power_family% (fun x : Fin n → ℝ => ∀ i,
    let exponent := 1 / q i
    let _range : 0 < exponent ∧ exponent < 1 := inverseRange (q i) (hq i)
    let coordinate := x i + 1
    (coordinate, 1, x i) ∈ POW exponent)

private def reject (predicate : Expr) (fragment : String) : MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let .error error ← Morew.Elab.Conic.normalizeRow predicate (label? := some `power_family)
    | throwError "unsupported power family was accepted: {predicate}"
  let diagnostic ← error.reason.toString
  unless diagnostic.contains "power_family" && diagnostic.contains fragment do
    throwError "unexpected power-family diagnostic: {diagnostic}"
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter &&
      MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "rejected power family changed caller state"

run_cmd liftTermElabM do
  for dimension in [0, 2] do
    let n := Syntax.mkNumLit (toString dimension)
    reject (← elaborate (← `(fun x : ℝ =>
      ∀ _i : Fin $n, (x * x, 1, x) ∈ POW (1 / 2 : ℝ)))) "cone coordinates"
    reject (← elaborate (← `(fun x : ℝ =>
      ∀ _i : Fin $n, (x, 1, x) ∈ POW (0 : ℝ)))) "required"
    reject (← elaborate (← `(fun x : ℝ =>
      ∀ _i : Fin $n, (x, 1, x) ∈ POW x))) "decision"
    reject (← elaborate (← `(fun x : ℝ => ∀ _i : Fin $n,
      @Membership.mem (ℝ × ℝ × ℝ) (Set (ℝ × ℝ × ℝ))
        ⟨fun _ _ => True⟩ (POW (1 / 2 : ℝ)) (x, 1, x)))) "membership instance"
  reject (← elaborate (← `(fun x : ℝ =>
    ∀ _i : Bool, (x, 1, x) ∈ POW (1 / 2 : ℝ)))) "Fin n"
  reject (← elaborate (← `(fun x : ℝ =>
    ∀ _i : Fin 2, ∀ _j : Fin 2, (x, 1, x) ∈ POW (1 / 2 : ℝ)))) "one exponential membership"
  reject (← elaborate (← `(fun x : ℝ =>
    ∀ _i : Fin 2, (x, 1, x) ∈ POW (1 / 2 : ℝ) ∧ True))) "one exponential membership"
  reject (← elaborate (← `(fun x : ℝ =>
    ∀ _i : Fin (if x ≤ 0 then 1 else 2), (x, 1, x) ∈ POW (1 / 2 : ℝ)))) "dimension depends"
  reject (← elaborate (← `(fun _x : ℝ =>
    @Membership.mem (Fin 0 → ℝ × ℝ × ℝ) (ConvexCone ℝ (Fin 0 → ℝ × ℝ × ℝ))
      ⟨fun _ _ => True⟩ (Cone.powerProduct 0 (fun _ => 0) (fun i => Fin.elim0 i)).carrier
      (fun _ => (0, 0, 0))))) "membership instance"
  reject (← elaborate (← `(fun x : ℝ => ∀ _i : Fin 2,
    let range := (fun _ : ℝ => (show (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 by norm_num)) x
    (x, 1, x) ∈ (Cone.power (1 / 2) range).carrier))) "decision"
  let missing ← elaborate (← `(fun (α : Fin 2 → ℝ) (_ : 0 < α 0 ∧ α 0 < 1) =>
    fun x : Fin 2 → ℝ => ∀ i, (x i, 1, x i) ∈ POW (α i)))
  lambdaBoundedTelescope missing 2 fun _ predicate => reject predicate "required"
  let missingLocal ← elaborate (← `(fun (q : Fin 2 → ℝ) (_hq : ∀ i, 1 < q i) =>
    fun x : Fin 2 → ℝ => ∀ i, (x i + 1, 1, x i) ∈ POW (1 / q i)))
  lambdaBoundedTelescope missingLocal 2 fun _ predicate => reject predicate "required"

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun α : ℝ => fun x : ℝ =>
    ∀ _i : Fin 0, (x, 1, x) ∈ POW α))
  let hole ← mkFreshExprMVar (mkConst ``Real)
  withLetDecl `hiddenExponent (mkConst ``Real) hole fun exponent =>
    reject (mkApp source exponent) "unresolved"
  if ← hole.mvarId!.isAssigned then throwError "family recognition assigned a caller exponent"
  let bundled ← elaborate (← `(fun (α : ℝ) (h : 0 < α ∧ α < 1) => fun x : ℝ =>
    ∀ _i : Fin 0, (x, 1, x) ∈ (Cone.power α h).carrier))
  withLocalDeclD `α (mkConst ``Real) fun exponent => do
    let range ← elaborate (← `(fun α : ℝ => 0 < α ∧ α < 1))
    let obligation := range.beta #[exponent]
    withLetDecl `hiddenRange obligation (← mkSorry obligation true) fun proof =>
      reject (mkAppN bundled #[exponent, proof]) "placeholders"

private def checkEvidence (source : TSyntax `term) (parameters : Nat)
    (indexed accepted : Bool) : TermElabM Unit := do
  let expression ← elaborate source
  lambdaBoundedTelescope expression parameters fun _ source =>
    lambdaBoundedTelescope source 1 fun points rest => do
      let check (goal : Expr) (index? : Option Expr) : MetaM Unit := do
        let before ← getMCtx
        let environment ← getEnv
        let proof? ← Morew.Elab.Conic.Evidence.proveIndependent? points[0]! goal index?
        unless proof?.isSome == accepted do throwError "unexpected parameter evidence for {goal}"
        if let some proof := proof? then
          unless ← isDefEq (← inferType proof) goal do throwError "parameter evidence has wrong type"
          if proof.hasSorry || proof.hasMVar then throwError "parameter evidence is incomplete"
          checkWithKernel proof
        unless before.mvarCounter == (← getMCtx).mvarCounter &&
            before.lmvarCounter == (← getMCtx).lmvarCounter &&
            MorewTest.sameLocalDeclarationNames environment (← getEnv) do
          throwError "parameter evidence changed caller state"
      if indexed then
        lambdaBoundedTelescope rest 1 fun indices goal => check goal (some indices[0]!)
      else check rest none

run_cmd liftTermElabM do
  checkEvidence (← `(fun _x : ℝ => 1 < (2 : ℝ≥0∞).toReal)) 0 false true
  checkEvidence (← `(fun _x : ℝ => 1 < (3 / 2 : ℝ≥0∞).toReal)) 0 false true
  checkEvidence (← `(fun _x : ℝ => 1 < (1 : ℝ≥0∞).toReal)) 0 false false
  checkEvidence (← `(fun (q : ℝ) (_h : 1 < q) (_x : ℝ) =>
    1 < (ENNReal.ofReal q).toReal)) 2 false true
  checkEvidence (← `(fun (q : ℝ) (_h : 1 ≤ q) (_x : ℝ) =>
    1 < (ENNReal.ofReal q).toReal)) 2 false false
  checkEvidence (← `(fun x : ℝ => 1 < (ENNReal.ofReal x).toReal)) 0 false false
  checkEvidence (← `(fun (q : Fin 2 → ℝ) (_h : ∀ i, 1 < q i) (_x : ℝ) (i : Fin 2) =>
    1 < (ENNReal.ofReal (q i)).toReal)) 2 true true
  checkEvidence (← `(fun (q : Fin 2 → ℝ) (_h : 1 < q 0) (_x : ℝ) (i : Fin 2) =>
    1 < (ENNReal.ofReal (q i)).toReal)) 2 true false

def rationalFamilyLift : ExactConstraintLift (fun x : ℝ =>
    ∀ _i : Fin 2, (x, 1, x) ∈ POW (1 / (3 / 2 : ℝ))) where
  Auxiliary := Unit
  target x _ := ∀ _i : Fin 2,
    (x, 1, x) ∈ (Cone.power (1 / (3 / 2 : ℝ)) (by norm_num)).carrier
  source_iff_exists x := by simp only [exists_const]; rfl

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun x : ℝ =>
    ∀ _i : Fin 2, (x, 1, x) ∈ POW (1 / (3 / 2 : ℝ))))
  let .ok result ← Morew.Elab.Conic.Plan.plan source (mkConst ``rationalFamilyLift)
    | throwError "exact grouped power lift was rejected"
  result.toResult.check source #[]
  unless result.rowPredicates.size == 1 && result.certifiedRows.size == 1 &&
      result.auxiliary?.isNone do throwError "grouped power lift changed row or auxiliary count"
  lambdaTelescope result.rowPredicates[0]! fun _ body =>
    forallTelescope body fun indices membership => do
      unless indices.size == 1 && membership.isAppOfArity ``Membership.mem 5 do
        throwError "power normalization changed the quantified row"
      let cone := membership.getAppArgs[3]!.getAppArgs[0]!
      unless cone.isAppOfArity ``Cone.power 2 do throwError "missing normalized power cone"
      unless ← isDefEq cone.getAppArgs[0]! (← elaborate (← `((2 / 3 : ℝ)))) do
        throwError "literal rational exponent was not normalized under the quantifier"

def extendedFamilyLift (p : ℝ≥0∞) (hp : 1 < p.toReal) :
    ExactConstraintLift (fun x : ℝ => ∀ _i : Fin 2, (x, 1, x) ∈ POW (1 / p.toReal)) where
  Auxiliary := Unit
  target x _ := ∀ _i : Fin 2,
    (x, 1, x) ∈ (Cone.power (1 / p.toReal) (inverseRange p.toReal hp)).carrier
  source_iff_exists x := by simp only [exists_const]; rfl

private def checkExtendedPlan (parameter evidence expected : TSyntax `term)
    (retainedName? : Option Name := none) : TermElabM Unit := do
  let source ← elaborate (← `(fun x : ℝ =>
    ∀ _i : Fin 2, (x, 1, x) ∈ POW (1 / ($parameter : ℝ≥0∞).toReal)))
  let rule ← elaborate (← `(extendedFamilyLift $parameter $evidence))
  let .ok result ← Morew.Elab.Conic.Plan.plan source rule
    | throwError "extended-real parameter family was rejected"
  result.toResult.check source #[]
  lambdaTelescope result.rowPredicates[0]! fun _ body =>
    forallTelescope body fun _ membership => do
      let cone := membership.getAppArgs[3]!.getAppArgs[0]!
      let exponent := cone.getAppArgs[0]!
      unless ← isDefEq exponent (← elaborate expected) do
        throwError "incorrect normalized extended-real parameter: {exponent}"
      if let some name := retainedName? then
        unless (exponent.find? (·.isConstOf name)).isSome do
          throwError "power normalization unfolded a named parameter"
      else
        if (exponent.find? (·.isConstOf ``ENNReal.toReal)).isSome then
          throwError "numeric exponent still contains visible toReal scaffolding"

def namedExponent : ℝ≥0∞ := 2

run_cmd liftTermElabM do
  checkExtendedPlan (← `((2 : ℝ≥0∞))) (← `(by norm_num)) (← `((1 / 2 : ℝ)))
  checkExtendedPlan (← `((3 / 2 : ℝ≥0∞))) (← `(by norm_num)) (← `((2 / 3 : ℝ)))
  checkExtendedPlan (← `(namedExponent)) (← `(by norm_num [namedExponent]))
    (← `((1 / namedExponent.toReal : ℝ))) (some ``namedExponent)

def castFamilyLift (n : ℕ) (hn : 0 < n) : ExactConstraintLift (fun x : ℝ =>
    ∀ _i : Fin 2, (x, 1, x) ∈ POW (1 / ((n : ℝ) + 1))) where
  Auxiliary := Unit
  target x _ := ∀ _i : Fin 2,
    (x, 1, x) ∈ (Cone.power (1 / ((n : ℝ) + 1))
      (inverseRange _ (by exact_mod_cast Nat.lt_add_one_iff.mpr hn))).carrier
  source_iff_exists x := by simp only [exists_const]; rfl

def namedDimension : ℕ := 3

run_cmd liftTermElabM do
  for (dimension, named) in #[(← `((3 : ℕ)), false), (← `(namedDimension), true)] do
    let source ← elaborate (← `(fun x : ℝ =>
      ∀ _i : Fin 2, (x, 1, x) ∈ POW (1 / (($dimension : ℕ) + 1 : ℝ))))
    let rule ← elaborate (← `(castFamilyLift $dimension (by decide)))
    let .ok result ← Morew.Elab.Conic.Plan.plan source rule
      | throwError "cast-parameter family was rejected"
    result.toResult.check source #[]
    lambdaTelescope result.rowPredicates[0]! fun _ body =>
      forallTelescope body fun _ membership => do
        let exponent := membership.getAppArgs[3]!.getAppArgs[0]!.getAppArgs[0]!
        if named then
          unless (exponent.find? (·.isConstOf ``namedDimension)).isSome do
            throwError "normalization unfolded a named dimension"
        else
          unless (← isDefEq exponent (← elaborate (← `((1 / 4 : ℝ))))) &&
              (exponent.find? (·.isConstOf ``Nat.cast)).isNone do
            throwError "literal dimension cast was not normalized: {exponent}"

end

end MorewTest.Conic.PowerFamilies
