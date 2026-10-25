/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Domain

/-!
# Native affine cone memberships

Scalar and finite-vector nonnegative and zero rows retain their actual spaces.
Canonical membership and singleton instances are checked before certification.
-/

namespace MorewTest.Conic.AffineMembership

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Morew

noncomputable section

structure CertifiedRow {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (predicate : X → Prop) where
  row : Morew.Conic.Constraint X
  equivalent : ∀ x, row.Holds x ↔ predicate x

elab "certified_membership% " source:term : term => do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  match ← Morew.Elab.Conic.normalizeRow predicate with
  | .error error => throwError "expected an affine membership: {error.reason}"
  | .ok result => mkAppM ``CertifiedRow.mk #[result.constraint, result.pointwiseIff]

def scalar : CertifiedRow (fun x : ℝ => 3 - (2 * x + 1) ∈ ℝ₊) :=
  certified_membership% (fun x : ℝ => 3 - (2 * x + 1) ∈ ℝ₊)

example : 3 - 2 ∈ ℝ₊ := by
  change (0 : ℝ) ≤ 3 - 2
  norm_num

def scalarZero : CertifiedRow (fun x : ℝ => x - 1 ∈ ({0} : Set ℝ)) :=
  certified_membership% (fun x : ℝ => x - 1 ∈ ({0} : Set ℝ))

def explicitSingleton : CertifiedRow (fun x : ℝ => x ∈ Set.singleton (0 : ℝ)) :=
  certified_membership% (fun x : ℝ => x ∈ Set.singleton (0 : ℝ))

def explicitZero : CertifiedRow (fun x : ℝ => x ∈ ({Zero.zero} : Set ℝ)) :=
  certified_membership% (fun x : ℝ => x ∈ ({Zero.zero} : Set ℝ))

private abbrev Reals := Set ℝ
private abbrev Coordinate {n : Nat} (_ : Fin n) := ℝ
private abbrev Vectors (n : Nat) := Set ((i : Fin n) → Coordinate i)

def scalarZeroAlias : CertifiedRow (fun x : ℝ => x ∈ ({0} : Reals)) :=
  certified_membership% (fun x : ℝ => x ∈ ({0} : Reals))

def vectorZeroAlias (n : Nat) : CertifiedRow
    (fun x : (i : Fin n) → Coordinate i => x ∈ ({0} : Vectors n)) :=
  certified_membership% (fun x : (i : Fin n) → Coordinate i => x ∈ ({0} : Vectors n))

def vector (n : Nat) : CertifiedRow (fun x : Fin n → ℝ => x ∈ ℝ₊^n) :=
  certified_membership% (fun x : Fin n → ℝ => x ∈ ℝ₊^n)

def vectorZero (n : Nat) : CertifiedRow (fun x : Fin n → ℝ => x ∈ ({0} : Set (Fin n → ℝ))) :=
  certified_membership% (fun x : Fin n → ℝ => x ∈ ({0} : Set (Fin n → ℝ)))

def bundledVectorZero (n : Nat) : CertifiedRow
    (fun x : Fin n → ℝ => x ∈ (Morew.Conic.Cone.zero n).carrier) :=
  certified_membership% (fun x : Fin n → ℝ => x ∈ (Morew.Conic.Cone.zero n).carrier)

example : scalar.row.cone.Space = ℝ := rfl
example : scalarZero.row.cone.Space = ℝ := rfl
example : scalarZeroAlias.row.cone.Space = ℝ := rfl
example (n : Nat) : (vectorZeroAlias n).row.cone.Space = (Fin n → ℝ) := rfl
example (n : Nat) : (vector n).row.cone.Space = (Fin n → ℝ) := rfl
example (n : Nat) : (vectorZero n).row.cone.Space = (Fin n → ℝ) := rfl

example (x : Fin 0 → ℝ) : (vector 0).row.Holds x := by
  rw [(vector 0).equivalent, Morew.Conic.Cone.mem_nonnegative]
  exact fun i => Fin.elim0 i

example (x : Fin 0 → ℝ) : (vectorZero 0).row.Holds x := by
  rw [(vectorZero 0).equivalent, Set.mem_singleton_iff]
  exact funext fun i => Fin.elim0 i

private def expectRejected (source : TSyntax `term) (fragment : String) : TermElabM Unit := do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  let .error error ← Morew.Elab.Conic.normalizeRow predicate (label? := some `affine_member)
    | throwError "unsupported affine membership was accepted"
  let diagnostic ← error.reason.toString
  unless diagnostic.contains "affine_member" && diagnostic.contains fragment do
    throwError "missing diagnostic context: {diagnostic}"

run_cmd Lean.Elab.Command.liftTermElabM do
  expectRejected (← `(fun x : ℝ => x * x ∈ ℝ₊)) "cone coordinates"
  expectRejected (← `(fun x : ℝ => x ∈ ({1} : Set ℝ))) "canonical zero"
  expectRejected (← `(fun x : ℝ =>
    @Membership.mem ℝ (ConvexCone ℝ ℝ) ⟨fun _ _ => True⟩ ℝ₊ x))
    "unsupported membership instance"
  expectRejected (← `(fun x : ℝ =>
    @Membership.mem ℝ (Set ℝ) ⟨fun _ _ => True⟩ ({0} : Set ℝ) x))
    "unsupported membership instance"
  expectRejected (← `(fun x : ℝ =>
    @Membership.mem ℝ Reals ⟨fun _ _ => True⟩ ({0} : Reals) x))
    "unsupported membership instance"
  expectRejected (← `(fun x : ℝ =>
    x ∈ @Singleton.singleton ℝ (Set ℝ) ⟨fun _ => {0}⟩ 0))
    "unsupported singleton instance"
  expectRejected (← `(fun x : ℝ =>
    x ∈ ({@OfNat.ofNat ℝ 0 ⟨1⟩} : Set ℝ))) "canonical zero"
  expectRejected (← `(fun x : Fin 0 → ℝ =>
    x ∈ ({@OfNat.ofNat (Fin 0 → ℝ) 0 ⟨fun _ => 1⟩} : Set (Fin 0 → ℝ))))
    "canonical zero"
  expectRejected (← `(fun x : ℝ =>
    x ∈ ({@Zero.zero ℝ ⟨1⟩} : Set ℝ))) "canonical zero"
  expectRejected (← `(fun x : ℝ =>
    x ∈ ({@Zero.zero ℝ ⟨1⟩} : Reals))) "canonical zero"
  expectRejected (← `(fun x : ℝ =>
    (fun _ : Fin (if x ≤ 0 then 1 else 2) => x) ∈ ℝ₊^(if x ≤ 0 then 1 else 2)))
    "dimension depends"
  expectRejected (← `(fun x : ℝ =>
    (fun _ : Fin (if x ≤ 0 then 1 else 2) => x) ∈
      ({0} : Vectors (if x ≤ 0 then 1 else 2)))) "dimension depends"

run_cmd Lean.Elab.Command.liftTermElabM do
  let predicate ← elabTerm (← `(fun x : ℝ => x ∈ ({0} : Set ℝ))) none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  lambdaTelescope predicate fun points body => do
    let args := body.getAppArgs
    let type ← inferType args[2]!
    let hole ← mkFreshExprMVar type
    withLetDecl `hiddenMembership type hole fun binding => do
      let source ← mkLambdaFVars points (mkAppN body.getAppFn (args.set! 2 binding))
      let .error error ← Morew.Elab.Conic.normalizeRow source
        | throwError "unresolved singleton membership was accepted"
      unless (← error.reason.toString).contains "unresolved metavariables" do
        throwError "missing unresolved singleton diagnostic"
      if ← hole.mvarId!.isAssigned then
        throwError "singleton recognition assigned a caller metavariable"

private def expectSign (source : TSyntax `term) (strict accepted : Bool) : TermElabM Unit := do
  let predicate ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  let predicate ← instantiateMVars predicate
  lambdaTelescope predicate fun points body => do
    withLocalDeclD `retained body fun evidence => do
      let result ← Morew.Elab.Conic.Domain.signFromRetained? points[0]! points[0]!
        #[body] evidence strict
      unless result.isSome == accepted do
        throwError "unexpected retained membership sign result for {body}"
      if let some proof := result then
        checkWithKernel (← mkLambdaFVars (points.push evidence) proof)

run_cmd Lean.Elab.Command.liftTermElabM do
  expectSign (← `(fun x : ℝ => x ∈ ℝ₊)) false true
  expectSign (← `(fun x : ℝ => x ∈ ℝ₊)) true false
  expectSign (← `(fun x : ℝ => x - 2 ∈ ℝ₊)) true true
  expectSign (← `(fun x : ℝ => x - 2 ∈ ℝ₊)) false true
  expectSign (← `(fun x : ℝ => 2 - x ∈ ℝ₊)) true false
  expectSign (← `(fun x : ℝ => x - (-2) ∈ ℝ₊)) true false
  expectSign (← `(fun x : ℝ => x + (-2) ∈ ℝ₊)) true false
  expectSign (← `(fun x : ℝ => True ∧ (x - 1 ∈ ℝ₊ ∧ True))) true true
  expectSign (← `(fun x : ℝ =>
    @Membership.mem ℝ (ConvexCone ℝ ℝ) ⟨fun _ _ => True⟩ ℝ₊ (x - 2))) true false
  expectSign (← `(fun x : ℝ =>
    @HSub.hSub ℝ ℝ ℝ ⟨fun a _ => a⟩ x 2 ∈ ℝ₊)) true false

end

end MorewTest.Conic.AffineMembership
