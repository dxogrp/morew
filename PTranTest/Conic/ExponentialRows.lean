import PTran.Elab.Conic

/-!
# Checked exponential rows and finite families

A quantified family remains one row and is certified against the finite product
cone. Empty families have their exact vacuous meaning, but still undergo the
same structural and affine checks as nonempty families.
-/

namespace PTranTest.Conic.ExponentialRows

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open PTran

noncomputable section

structure CertifiedRow {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (predicate : X → Prop) where
  row : PTran.Conic.Constraint X
  equivalent : ∀ x, row.Holds x ↔ predicate x

elab "certified_exp_row% " source:term : term => do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  match ← PTran.Elab.Conic.normalizeRow predicate with
  | .error error => throwError "expected an exponential row: {error.reason}"
  | .ok result =>
      for expression in #[result.constraint, result.pointwiseIff] do
        if expression.hasMVar || expression.hasSorry then
          throwError "exponential row has an incomplete certificate"
        checkWithKernel expression
      mkAppM ``CertifiedRow.mk #[result.constraint, result.pointwiseIff]

def scalar : CertifiedRow (fun p : ℝ × ℝ × ℝ =>
    (p.1 + 2, p.2.1 / 2, 3 * p.2.2 - 1) ∈ Conic.Cone.exponential.carrier) :=
  certified_exp_row% (fun p : ℝ × ℝ × ℝ =>
    (p.1 + 2, p.2.1 / 2, 3 * p.2.2 - 1) ∈ Conic.Cone.exponential.carrier)

example : scalar.row.cone = Conic.Cone.exponential := rfl

def product (n : Nat) : CertifiedRow (fun p : (Fin n → ℝ) × ℝ =>
    (fun i => (p.1 i - p.2, (1 : ℝ), p.1 i + 2)) ∈
      (Conic.Cone.exponentialProduct n).carrier) :=
  certified_exp_row% (fun p : (Fin n → ℝ) × ℝ =>
    (fun i => (p.1 i - p.2, (1 : ℝ), p.1 i + 2)) ∈
      (Conic.Cone.exponentialProduct n).carrier)

def quantified (n : Nat) : CertifiedRow (fun p : (Fin n → ℝ) × ℝ × (Fin n → ℝ) =>
    ∀ i : Fin n, (p.1 i - p.2.1, (1 : ℝ), p.2.2 i) ∈ Conic.Cone.exponential.carrier) :=
  certified_exp_row% (fun p : (Fin n → ℝ) × ℝ × (Fin n → ℝ) =>
    ∀ i : Fin n, (p.1 i - p.2.1, (1 : ℝ), p.2.2 i) ∈ Conic.Cone.exponential.carrier)

example (n : Nat) : (quantified n).row.cone = Conic.Cone.exponentialProduct n := rfl

def softplusCoordinates : CertifiedRow (fun p : ℝ × ℝ × (Fin 2 → ℝ) =>
    ∀ i : Fin 2, ((![0, p.1] : Fin 2 → ℝ) i - p.2.1, (1 : ℝ), p.2.2 i) ∈
      Conic.Cone.exponential.carrier) :=
  certified_exp_row% (fun p : ℝ × ℝ × (Fin 2 → ℝ) =>
    ∀ i : Fin 2, ((![0, p.1] : Fin 2 → ℝ) i - p.2.1, (1 : ℝ), p.2.2 i) ∈
      Conic.Cone.exponential.carrier)

private abbrev Indices (n : Nat) := Fin n

def indexAlias (n : Nat) : CertifiedRow (fun x : Fin n → ℝ =>
    ∀ i : Indices n, (x i + 1, (1 : ℝ), 3 * x i) ∈ Conic.Cone.exponential.carrier) :=
  certified_exp_row% (fun x : Fin n → ℝ =>
    ∀ i : Indices n, (x i + 1, (1 : ℝ), 3 * x i) ∈ Conic.Cone.exponential.carrier)

def euclidean (n : Nat) : CertifiedRow (fun x : EuclideanSpace ℝ (Fin n) =>
    ∀ i : Fin n, (WithLp.ofLp x i, (1 : ℝ), 2 - WithLp.ofLp x i) ∈
      Conic.Cone.exponential.carrier) :=
  certified_exp_row% (fun x : EuclideanSpace ℝ (Fin n) =>
    ∀ i : Fin n, (WithLp.ofLp x i, (1 : ℝ), 2 - WithLp.ofLp x i) ∈
      Conic.Cone.exponential.carrier)

def evidenceLets (n : Nat) (a : Fin n → ℝ) :
    CertifiedRow (fun x : Fin n → ℝ =>
      ∀ i : Fin n,
        let _h : Real.exp (a i) ≠ 0 := Real.exp_ne_zero (a i)
        let coordinate := x i / Real.exp (a i)
        (coordinate, (1 : ℝ), x i + 1) ∈ Conic.Cone.exponential.carrier) :=
  certified_exp_row% (fun x : Fin n → ℝ =>
    ∀ i : Fin n,
      let _h : Real.exp (a i) ≠ 0 := Real.exp_ne_zero (a i)
      let coordinate := x i / Real.exp (a i)
      (coordinate, (1 : ℝ), x i + 1) ∈ Conic.Cone.exponential.carrier)

def emptyFamily : CertifiedRow (fun x : ℝ =>
    ∀ _i : Fin 0, (x, (1 : ℝ), x - 1) ∈ Conic.Cone.exponential.carrier) :=
  certified_exp_row% (fun x : ℝ =>
    ∀ _i : Fin 0, (x, (1 : ℝ), x - 1) ∈ Conic.Cone.exponential.carrier)

example (x : ℝ) : emptyFamily.row.Holds x := by
  apply (emptyFamily.equivalent x).mpr
  intro i
  exact Fin.elim0 i

def singletonFamily : CertifiedRow (fun x : ℝ =>
    ∀ _i : Fin 1, (x, (1 : ℝ), x + 1) ∈ Conic.Cone.exponential.carrier) :=
  certified_exp_row% (fun x : ℝ =>
    ∀ _i : Fin 1, (x, (1 : ℝ), x + 1) ∈ Conic.Cone.exponential.carrier)

example (x : ℝ) : singletonFamily.row.Holds x ↔
    (x, (1 : ℝ), x + 1) ∈ Conic.Cone.exponential.carrier := by
  rw [singletonFamily.equivalent]
  simp

private def expectRejected (source : TSyntax `term) (fragment : String) : TermElabM Unit := do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  let .error error ← PTran.Elab.Conic.normalizeRow predicate (label? := some `bad_exp)
    | throwError "unsupported exponential row was accepted"
  let diagnostic ← error.reason.toString
  unless diagnostic.contains "bad_exp" && diagnostic.contains fragment do
    throwError "missing diagnostic context: {diagnostic}"

private noncomputable def hiddenCone : Conic.Cone := Conic.Cone.exponential

private def hiddenPredicate (x : ℝ) : Prop :=
  (x, (1 : ℝ), x + 1) ∈ Conic.Cone.exponential.carrier

run_cmd Lean.Elab.Command.liftTermElabM do
  expectRejected (← `(fun x : ℝ =>
    (x * x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier)) "cone coordinates"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 2, (x, (1 : ℝ), x * x) ∈ Conic.Cone.exponential.carrier)) "cone coordinates"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 0, (x * x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier)) "cone coordinates"
  expectRejected (← `(fun x : ℝ =>
    (fun _i : Fin 2 => (x, (1 : ℝ), x * x)) ∈
      (Conic.Cone.exponentialProduct 2).carrier)) "cone coordinates"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 2,
      (@HAdd.hAdd ℝ ℝ ℝ ⟨fun a _ => a + a⟩ x x, (1 : ℝ), x) ∈
        Conic.Cone.exponential.carrier)) "arithmetic instance"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : ℕ, (x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier)) "Fin n"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Bool, (x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier)) "Fin n"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 2, ∀ _j : Fin 2,
      (x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier)) "one exponential membership"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 2, (x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier ∧ True))
    "one exponential membership"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 2, 0 ≤ x → (x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier))
    "one exponential membership"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 2, (x, (0 : Fin 1 → ℝ)) ∈ (Conic.Cone.secondOrder 1).carrier))
    "native exponential cone"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 2, (x, (1 : ℝ), x) ∈ hiddenCone.carrier)) "unsupported cone"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin 2, hiddenPredicate x)) "one exponential membership"
  expectRejected (← `(fun x : ℝ =>
    ∀ _i : Fin (if x ≤ 0 then 1 else 2),
      (x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier)) "dimension depends"
  expectRejected (← `(fun _x : ℝ =>
    @Membership.mem (ℝ × ℝ × ℝ) (ConvexCone ℝ (ℝ × ℝ × ℝ))
      ⟨fun _ _ => True⟩ Conic.Cone.exponential.carrier
      ((0 : ℝ), (0 : ℝ), (0 : ℝ)))) "unsupported membership instance"
  expectRejected (← `(fun _x : ℝ =>
    ∀ _i : Fin 0,
      @Membership.mem (ℝ × ℝ × ℝ) (ConvexCone ℝ (ℝ × ℝ × ℝ))
        ⟨fun _ _ => True⟩ Conic.Cone.exponential.carrier
        ((0 : ℝ), (0 : ℝ), (0 : ℝ)))) "unsupported membership instance"
  expectRejected (← `(fun _x : ℝ =>
    @Membership.mem (Fin 0 → ℝ × ℝ × ℝ)
      (ConvexCone ℝ (Fin 0 → ℝ × ℝ × ℝ))
      ⟨fun _ _ => True⟩ (Conic.Cone.exponentialProduct 0).carrier
      (fun _ => ((0 : ℝ), (0 : ℝ), (0 : ℝ))))) "unsupported membership instance"

-- An unresolved relation hidden in a local declaration must not be solved by
-- the recognizer, even when the finite family happens to be empty.
run_cmd Lean.Elab.Command.liftTermElabM do
  let predicate ← elabTerm (← `(fun x : ℝ =>
    ∀ _i : Fin 0, (x, (1 : ℝ), x) ∈ Conic.Cone.exponential.carrier)) none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  lambdaTelescope predicate fun points body => do
    forallTelescope body fun indices membership => do
      let args := membership.getAppArgs
      let type ← inferType args[2]!
      let hole ← mkFreshExprMVar type
      withLetDecl `hiddenMembership type hole fun binding => do
        let body ← mkForallFVars indices (mkAppN membership.getAppFn (args.set! 2 binding))
        let source ← mkLambdaFVars points body
        let .error error ← PTran.Elab.Conic.normalizeRow source
          | throwError "unresolved membership instance was accepted"
        unless (← error.reason.toString).contains "unresolved metavariables" do
          throwError "missing hidden-instance diagnostic: {error.reason}"
        if ← hole.mvarId!.isAssigned then
          throwError "row recognition assigned a caller metavariable"

end

end PTranTest.Conic.ExponentialRows
