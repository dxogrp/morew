/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Affine.Support
import MorewTest.Affine.HelperFixtures
import Morew.Elab.Atom

/-!
# Affine certificates through imported helper definitions

Every success assertion checks the certificate against the original application,
including helpers whose arguments disappear only after expansion.
-/

namespace MorewTest.Affine.Helpers

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Affine MorewTest.Affine HelperFixtures Matrix

noncomputable def customAffine (x : ℝ) : ℝ := 2 * x + 1
noncomputable abbrev customAlias (x : ℝ) : ℝ := 2 * x

private opaque coefficientProblem : Morew.Problem ℝ ℝ := ⟨id, fun _ => True⟩

@[irreducible] private def sealedCoefficientProblem : Morew.Problem ℝ ℝ :=
  ⟨id, fun _ => True⟩

private noncomputable def evidenceProblem (c : ℝ) (h : c ≠ 0 ∧ True) :
    Morew.Problem ℝ ℝ :=
  let _nonzero : c ≠ 0 := h.1
  ⟨fun x => x / c, fun _ => True⟩

private noncomputable def evidenceObjective (c : ℝ) (h : c ≠ 0 ∧ True) : ℝ → ℝ :=
  (evidenceProblem c h).objective

private noncomputable def finiteProblem {ι : Type} (e : Fin 2 ≃ ι) (a : ι → ℝ) :
    Morew.Problem (ι → ℝ) ℝ :=
  letI := Fintype.ofEquiv (Fin 2) e
  ⟨fun x => dotProduct a x, fun _ => True⟩

private noncomputable def finiteObjective {ι : Type} (e : Fin 2 ≃ ι) (a : ι → ℝ) :
    (ι → ℝ) → ℝ := (finiteProblem e a).objective

private noncomputable def finiteProofProblem {ι : Type} (h : Finite ι ∧ True) (i : ι) :
    Morew.Problem (ι → ℝ) ℝ :=
  let _finite : Finite ι := h.1
  ⟨fun x => x i + 1, fun _ => True⟩

private noncomputable def finiteProofObjective {ι : Type} (h : Finite ι ∧ True) (i : ι) :
    (ι → ℝ) → ℝ := (finiteProofProblem h i).objective

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => customAffine x))
  assertAffine (← `(fun x : ℝ => customAlias x))
  assertAffine (← `(fun x : ℝ => cost 2 1 x))
  assertAffine (← `(fun a b : ℝ => fun x : ℝ => cost a b x)) 2
  assertAffine (← `(fun a b : ℝ => fun x : ℝ => nestedCost a b x)) 2
  assertAffine (← `(fun x : ℝ => shift (shift x)))
  assertAffine (← `(fun a b : ℝ => fun x : ℝ => sectionCost a b x)) 2
  assertAffine (← `(fun x : ℝ => ignored x))
  assertAffine (← `(fun x : ℝ => ignored (Real.exp x)))
  assertAffine (← `(fun x : ℝ => discard (x + 1) (Real.exp x)))
  assertAffine (← `(fun x : ℝ => constantFactor 2 x * x))
  assertAffine (← `(fun a : ℝ => fun x : ℝ => constantFactor a x * x)) 1
  assertAffine (← `(fun a : ℝ => fun x : ℝ => hiddenProduct a * x)) 1
  assertAffine (← `(fun a : ℝ => fun x : ℝ => opaqueCost a * x)) 1
  assertAffine (← `(fun x : ℝ => x / constantFactor 2 x))
  assertAffine (← `(fun x : ℝ => quotient 2 x))
  assertAffine (← `(fun a : ℝ => fun (_h : a ≠ 0) => fun x : ℝ => quotient a x)) 2
  assertAffine (← `(fun a : ℝ => fun h : a ≠ 0 => fun x : ℝ =>
    checkedQuotient a h x)) 2
  assertAffine (← `(fun a : ℝ => fun h : a ≠ 0 ∧ True => fun x : ℝ =>
    evidencedQuotient a h x)) 2
  assertAffine (← `(fun x : ℝ => taggedCost (ULift.up.{1} ()) x))
  assertAffine (← `(fun (α : Type 1) (tag : α) => fun x : ℝ => taggedCost tag x)) 2
  assertRow (← `(fun a b : ℝ => fun x : ℝ => residual a b x ≤ 0)) 2
  assertRow (← `(fun x : ℝ => cost 2 1 x ≤ cost 3 4 x))

/-! An explicit evidence callback still proves division against the original helper. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate
    (← `(fun a : ℝ => fun (_h : a ≠ 0 ∧ True) => fun x : ℝ => quotient a x))
  lambdaBoundedTelescope expression 2 fun parameters source => do
    let config : Morew.Elab.Affine.Config := {
      nonzeroEvidence? := some fun obligation => do
        let proof ← mkAppM ``And.left #[parameters[1]!]
        unless ← isDefEq (← inferType proof) obligation do return none
        return some proof
    }
    match ← reifyAffine source config with
    | .ok result => checkResult source result
    | .error error => throwError "helper ignored supplied denominator evidence: {error.reason}"

/-! Structured helpers preserve symbolic dimensions and finite evidence. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => vector x))
  assertAffine (← `(fun x : ℝ => vector x 0))
  assertAffine (← `(fun x : ℝ => (vector x + vector x) 0))
  assertAffine (← `(fun i : Fin 2 => fun x : ℝ => vector x i)) 1
  assertAffine (← `(fun point : ℝ × ℝ => productCost point))
  assertAffine (← `(fun m n : ℕ => fun A : Matrix (Fin m) (Fin n) ℝ =>
    fun x : Fin n → ℝ => matrixProduct A x)) 3
  assertAffine (← `(fun m n : ℕ => fun A : Matrix (Fin m) (Fin n) ℝ =>
    fun i : Fin m => fun x : Fin n → ℝ => matrixProduct A x i)) 4
  assertAffine (← `(fun m n : ℕ => fun A : Matrix (Fin m) (Fin n) ℝ =>
    fun x : Fin m → ℝ => rowProduct A x)) 3
  assertAffine (← `(fun m n : ℕ => fun A : Matrix (Fin m) (Fin n) ℝ =>
    fun i : Fin n => fun x : Fin m → ℝ => rowProduct A x i)) 4
  assertAffine (← `(fun n : ℕ => fun a : Fin n → ℝ =>
    fun x : Fin n → ℝ => dot a x)) 2
  assertAffine (← `(fun n : ℕ => fun x : Fin n → ℝ => total x)) 1
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) =>
    fun x : ι → ℝ => finiteDot e a x)) 3
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) (i : ι) =>
    fun x : ι → ℝ => x i + finiteDot e a x)) 4
  assertAffine (← `(fun (ι : Type) (h : Finite ι ∧ True) (i : ι) =>
    fun x : ι → ℝ => finiteCoordinate h i x)) 3
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (A : Matrix ι ι ℝ) =>
    fun x : ι → ℝ => finiteMatrix e A x)) 3
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (A : Matrix ι ι ℝ) (i : ι) =>
    fun x : ι → ℝ => finiteMatrix e A x i)) 4
  assertRow (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) (i : ι) =>
    fun x : ι → ℝ => x i ≤ finiteDot e a x)) 4
  assertRow (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) (i : ι) =>
    fun x : ι → ℝ => finiteDot e a x ≤ x i)) 4

/-! Bounded container selection retains proof/instance lets and independent
coefficients whose containers cannot be unfolded. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun p : Morew.Problem ℝ ℝ => fun x : ℝ =>
    cost 2 1 x + p.objective 0)) 1
  assertAffine (← `(fun x : ℝ => cost 2 1 x + coefficientProblem.objective 0))
  assertAffine (← `(fun x : ℝ => cost 2 1 x + sealedCoefficientProblem.objective 0))
  assertAffine (← `(fun (b : Bool) (p q : Morew.Problem ℝ ℝ) => fun x : ℝ =>
    cost 2 1 x + (if b then p else q).objective 0)) 3
  assertAffine (← `(fun c : ℝ => fun h : c ≠ 0 ∧ True => fun x : ℝ =>
    evidenceObjective c h x)) 2
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) => fun x : ι → ℝ =>
    finiteObjective e a x)) 3
  assertAffine (← `(fun (ι : Type) (h : Finite ι ∧ True) (i : ι) => fun x : ι → ℝ =>
    finiteProofObjective h i x)) 3

/-! A blocked container stays opaque while helper arguments can still expose
decision-independent coefficients, with or without another expanded helper. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun p : Morew.Problem ℝ ℝ => fun _x : ℝ => p.objective 7)) 1
  assertAffine (← `(fun f : ℝ → ℝ => fun x : ℝ => f (ignored x))) 1
  assertAffine (← `(fun p : Morew.Problem ℝ ℝ => fun x : ℝ =>
    p.objective (ignored x))) 1
  assertAffine (← `(fun p : Morew.Problem ℝ ℝ => fun x : ℝ =>
    cost 2 1 x + p.objective (ignored x))) 1
  assertAffine (← `(fun x : ℝ => coefficientProblem.objective (ignored x)))
  assertAffine (← `(fun x : ℝ => sealedCoefficientProblem.objective (ignored x)))

/-! Expansion exposes the unsupported expression without crossing native boundaries. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => hiddenProduct x)) 0 (some ``HMul.hMul)
  assertUnsupported (← `(fun x : ℝ => hiddenDivision x)) 0 (some ``HAdd.hAdd)
  assertUnsupported (← `(fun x : ℝ => hiddenExponential x)) 0 (some ``Real.exp)
  assertUnsupported (← `(fun x : ℝ => hiddenChangedAdd x)) 0 (some ``HAdd.hAdd)
  assertUnsupported (← `(fun x : ℝ => hiddenCoercion x)) 0 (some ``Coe.coe)
  assertUnsupported (← `(fun a : ℝ => fun x : ℝ => quotient a x)) 1
  assertUnsupported (← `(fun x : ℝ => quotient 0 x))
  assertUnsupported (← `(fun x : ℝ => cost x 1 x))
  assertUnsupported (← `(fun x : ℝ => sealedCost x)) 0 (some ``sealedCost)
  assertUnsupported (← `(fun x : ℝ => opaqueCost x)) 0 (some ``opaqueCost)
  assertUnsupported (← `(fun x : ℝ => recursiveCost 0 x))
  assertUnsupported (← `(fun n : ℕ => fun x : ℝ => recursiveCost n x)) 1
  assertRowUnsupported (← `(fun x : ℝ => hiddenProduct x ≤ 0))
  assertRowUnsupported (← `(fun x : ℝ => helperPredicate x))
  let expression ← elaborate (← `(fun x : ℝ => hiddenProduct x + 1))
  match ← reifyAffine expression with
  | .ok _ => throwError "nonlinear helper was accepted"
  | .error error =>
    unless (← error.reason.toString).contains "hiddenProduct" do
      throwError "helper diagnostic lost the original application"

/-! The atom recognizer still sees the original application, without expansion. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate (← `(fun x : ℝ => hiddenExponential x))
  lambdaTelescope expression fun _ body => do
    if (← Morew.Elab.Atom.recognizeAtom? body).isSome then
      throwError "affine helper support changed native atom recognition"

/-! Expansion must not hide an unresolved argument, even when it is unused. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let hole ← mkFreshExprMVar (mkConst ``Real)
  let source ← withLocalDeclD `x (mkConst ``Real) fun point =>
    mkLambdaFVars #[point] (mkApp (mkConst ``ignored) hole)
  match ← reifyAffine source with
  | .ok _ => throwError "helper expansion discarded an unresolved argument"
  | .error error =>
    unless (← error.reason.toString).contains "unresolved metavariables" do
      throwError "helper expansion lost the unresolved-input diagnostic"
  if ← hole.mvarId!.isAssigned then
    throwError "helper expansion assigned an unresolved caller argument"

end MorewTest.Affine.Helpers
