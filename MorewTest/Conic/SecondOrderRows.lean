import Morew.Elab.Conic

/-!
# Checked second-order cone rows

Both cone families certify the entire affine coordinate tuple. Native cone
and membership instances are checked independently of whether a particular
tuple happens to satisfy the predicate.
-/

namespace MorewTest.Conic.SecondOrderRows

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Morew

noncomputable section

structure CertifiedRow {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (predicate : X → Prop) where
  row : Morew.Conic.Constraint X
  equivalent : ∀ x, row.Holds x ↔ predicate x

elab "certified_soc_row% " source:term : term => do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  match ← Morew.Elab.Conic.normalizeRow predicate with
  | .error error => throwError "expected a cone row: {error.reason}"
  | .ok result => mkAppM ``CertifiedRow.mk #[result.constraint, result.pointwiseIff]

def secondOrder (n : Nat) :
    CertifiedRow (fun p : ℝ × (Fin n → ℝ) =>
      (p.1 + 2, fun i => 3 * p.2 i - 1) ∈ (Morew.Conic.Cone.secondOrder n).carrier) :=
  certified_soc_row% (fun p : ℝ × (Fin n → ℝ) =>
    (p.1 + 2, fun i => 3 * p.2 i - 1) ∈ (Morew.Conic.Cone.secondOrder n).carrier)

def rotatedSecondOrder (n : Nat) :
    CertifiedRow (fun p : ℝ × ℝ × (Fin n → ℝ) =>
      (p.1 + 1, 2 * p.2.1, fun i => p.2.2 i - 3) ∈
        (Morew.Conic.Cone.rotatedSecondOrder n).carrier) :=
  certified_soc_row% (fun p : ℝ × ℝ × (Fin n → ℝ) =>
    (p.1 + 1, 2 * p.2.1, fun i => p.2.2 i - 3) ∈
      (Morew.Conic.Cone.rotatedSecondOrder n).carrier)

def euclideanCoordinates (n : Nat) :
    CertifiedRow (fun x : EuclideanSpace ℝ (Fin n) =>
      ((4 : ℝ), WithLp.ofLp (2 • x)) ∈ (Morew.Conic.Cone.secondOrder n).carrier) :=
  certified_soc_row% (fun x : EuclideanSpace ℝ (Fin n) =>
    ((4 : ℝ), WithLp.ofLp (2 • x)) ∈ (Morew.Conic.Cone.secondOrder n).carrier)

def euclideanVectorRow (n : Nat) :
    CertifiedRow (fun x : EuclideanSpace ℝ (Fin n) => WithLp.ofLp x ≤ fun _ => (2 : ℝ)) :=
  certified_soc_row% (fun x : EuclideanSpace ℝ (Fin n) => WithLp.ofLp x ≤ fun _ => (2 : ℝ))

def retainedEvidence (a : ℝ) :
    CertifiedRow (fun x : ℝ =>
      let _h : Real.exp a ≠ 0 := Real.exp_ne_zero a
      (x / Real.exp a, (0 : Fin 1 → ℝ)) ∈ (Morew.Conic.Cone.secondOrder 1).carrier) :=
  certified_soc_row% (fun x : ℝ =>
    let _h : Real.exp a ≠ 0 := Real.exp_ne_zero a
    (x / Real.exp a, (0 : Fin 1 → ℝ)) ∈ (Morew.Conic.Cone.secondOrder 1).carrier)

def emptySecondOrder : CertifiedRow (fun x : ℝ =>
    (x, (0 : Fin 0 → ℝ)) ∈ (Morew.Conic.Cone.secondOrder 0).carrier) :=
  certified_soc_row% (fun x : ℝ =>
    (x, (0 : Fin 0 → ℝ)) ∈ (Morew.Conic.Cone.secondOrder 0).carrier)

def emptyRotatedSecondOrder : CertifiedRow (fun p : ℝ × ℝ =>
    (p.1, p.2, (0 : Fin 0 → ℝ)) ∈ (Morew.Conic.Cone.rotatedSecondOrder 0).carrier) :=
  certified_soc_row% (fun p : ℝ × ℝ =>
    (p.1, p.2, (0 : Fin 0 → ℝ)) ∈ (Morew.Conic.Cone.rotatedSecondOrder 0).carrier)

example (x : ℝ) : emptySecondOrder.row.Holds x ↔ 0 ≤ x := by
  rw [emptySecondOrder.equivalent, Morew.Conic.Cone.mem_secondOrder]
  change ‖(0 : EuclideanSpace ℝ (Fin 0))‖ ≤ x ↔ 0 ≤ x
  simp

example (p : ℝ × ℝ) :
    emptyRotatedSecondOrder.row.Holds p ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  rw [emptyRotatedSecondOrder.equivalent, Morew.Conic.Cone.mem_rotatedSecondOrder]
  change (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ ‖(0 : EuclideanSpace ℝ (Fin 0))‖ ^ 2 ≤
    2 * p.1 * p.2) ↔ _
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hu, hv⟩
    exact ⟨hu, hv, mul_nonneg (mul_nonneg (by norm_num) hu) hv⟩

private def expectRejected (source : TSyntax `term) (fragment : String) : TermElabM Unit := do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  let .error error ← Morew.Elab.Conic.normalizeRow predicate (label? := some `bad_soc)
    | throwError "unsupported cone row was accepted"
  let diagnostic ← error.reason.toString
  unless diagnostic.contains "bad_soc" && diagnostic.contains fragment do
    throwError "missing diagnostic context: {diagnostic}"

private noncomputable def coneAlias (n : Nat) : Morew.Conic.Cone :=
  Morew.Conic.Cone.secondOrder n

run_cmd Lean.Elab.Command.liftTermElabM do
  expectRejected (← `(fun x : ℝ =>
    (x * x, (0 : Fin 0 → ℝ)) ∈ (Morew.Conic.Cone.secondOrder 0).carrier))
    "cone coordinates"
  expectRejected (← `(fun x : ℝ =>
    ((1 : ℝ), fun _ : Fin 2 => x * x) ∈ (Morew.Conic.Cone.secondOrder 2).carrier))
    "cone coordinates"
  expectRejected (← `(fun x : ℝ =>
    ((1 : ℝ), x * x, (0 : Fin 0 → ℝ)) ∈
      (Morew.Conic.Cone.rotatedSecondOrder 0).carrier)) "cone coordinates"
  expectRejected (← `(fun x : ℝ =>
    (x, (0 : Fin 2 → ℝ)) ∈ (coneAlias 2).carrier)) "unsupported cone"
  expectRejected (← `(fun x : Fin 2 → ℝ =>
    x ∈ (Morew.Conic.Cone.nonnegative 2).carrier)) "unsupported cone"
  expectRejected (← `(fun x : ℝ =>
    @Membership.mem (ℝ × (Fin 2 → ℝ)) (ConvexCone ℝ (ℝ × (Fin 2 → ℝ)))
      ⟨fun _ _ => True⟩ (Morew.Conic.Cone.secondOrder 2).carrier
      ((0 : ℝ), (0 : Fin 2 → ℝ))))
    "unsupported membership instance"
  expectRejected (← `(fun x : ℝ =>
    @Membership.mem (ℝ × ℝ × (Fin 2 → ℝ)) (ConvexCone ℝ (ℝ × ℝ × (Fin 2 → ℝ)))
      ⟨fun _ _ => True⟩ (Morew.Conic.Cone.rotatedSecondOrder 2).carrier
      ((0 : ℝ), (0 : ℝ), (0 : Fin 2 → ℝ)))) "unsupported membership instance"

-- A local membership alias must not hide an unresolved instance that a
-- definitional-equality comparison could accidentally complete for the caller.
run_cmd Lean.Elab.Command.liftTermElabM do
  let predicate ← elabTerm (← `(fun x : ℝ =>
    (x, (0 : Fin 1 → ℝ)) ∈ (Morew.Conic.Cone.secondOrder 1).carrier)) none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  lambdaTelescope predicate fun points body => do
    let args := body.getAppArgs
    let type ← inferType args[2]!
    let hole ← mkFreshExprMVar type
    withLetDecl `hiddenMembership type hole fun binding => do
      let source ← mkLambdaFVars points (mkAppN body.getAppFn (args.set! 2 binding))
      let .error error ← Morew.Elab.Conic.normalizeRow source (label? := some `hidden_soc)
        | throwError "unresolved membership instance was accepted"
      let diagnostic ← error.reason.toString
      unless diagnostic.contains "hidden_soc" && diagnostic.contains "unresolved metavariables" do
        throwError "missing hidden-instance diagnostic: {diagnostic}"
      if ← hole.mvarId!.isAssigned then
        throwError "row recognition assigned a caller metavariable"

end

end MorewTest.Conic.SecondOrderRows
