/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic

/-!
# Manual conic representations

The narrow semantic import provides conic certificates without loading the
surface language or the typed reformulation runner.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.Conic

open Morew Morew.Conic

universe u

noncomputable section

/-! ## Base cones and bundled instances -/

example (cone : Cone) : NormedAddCommGroup cone.Space := inferInstance
example (cone : Cone) : NormedSpace ℝ cone.Space := inferInstance
example (cone : Cone) : FiniteDimensional ℝ cone.Space := inferInstance

example (n : Nat) (x : Fin n → ℝ) : x ∈ (Cone.zero n).carrier ↔ x = 0 := by
  simp

example (n : Nat) (x : Fin n → ℝ) :
    x ∈ (Cone.nonnegative n).carrier ↔ ∀ i, 0 ≤ x i := by
  simp

example (x : Fin 0 → ℝ) : x ∈ (Cone.zero 0).carrier := by
  simp [Subsingleton.elim x 0]

example (x : Fin 0 → ℝ) : x ∈ (Cone.nonnegative 0).carrier := by
  simp

example : (0 : Fin 1 → ℝ) ∈ (Cone.zero 1).carrier := by
  simp

example : (fun _ : Fin 1 => (1 : ℝ)) ∉ (Cone.zero 1).carrier := by
  simp [funext_iff]

example : (fun _ : Fin 1 => (-1 : ℝ)) ∉ (Cone.nonnegative 1).carrier := by
  simp

/-- Custom cones retain mathlib's contract, which permits the empty cone. -/
def emptyCone : Cone where
  Space := ℝ
  carrier := ⊥

example : (0 : ℝ) ∉ emptyCone.carrier := by
  exact Set.notMem_empty 0

example {X : Type u} [AddCommGroup X] [Module ℝ X]
    (c : Constraint X) : Convex ℝ {x | c.Holds x} :=
  c.feasibleSetConvex

example {X : Type u} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] {p : Problem X ℝ} (form : Form p) : IsConic p :=
  form.isConic

/-! ## Algebraic decision spaces need no ambient norm -/

namespace Algebraic

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

-- Individual rows do not require finite-dimensional decision spaces either.
def row (f : X →ᵃ[ℝ] ℝ) : Constraint X where
  cone := Cone.nonnegativeScalar
  map := f

example (f : X →ᵃ[ℝ] ℝ) (x : X) : (row f).Holds x ↔ 0 ≤ f x := Iff.rfl

example (f : X →ᵃ[ℝ] ℝ) (x : X) :
    (Constraint.eqZero f).Holds x ↔ f x = 0 := by simp

example (f : X →ᵃ[ℝ] ℝ) (x : X) :
    (Constraint.nonnegative f).Holds x ↔ 0 ≤ f x := by simp

example (f : X →ᵃ[ℝ] ℝ) : Convex ℝ {x | (row f).Holds x} :=
  (row f).feasibleSetConvex

variable [FiniteDimensional ℝ X]

def data (sense : ObjectiveSense) (f : X →ᵃ[ℝ] ℝ) (c : Constraint X) : Data X where
  sense := sense
  objective := f
  rowCount := 1
  constraints := fun _ => c

def form (sense : ObjectiveSense) (f : X →ᵃ[ℝ] ℝ) (c : Constraint X) :
    Form (data sense f c).toProblem where
  data := data sense f c
  represents := rfl

example (f : X →ᵃ[ℝ] ℝ) (c : Constraint X) : IsConic (data .minimize f c).toProblem :=
  (form .minimize f c).isConic

example (f : X →ᵃ[ℝ] ℝ) (c : Constraint X) :
    Convex ℝ {x | (data .maximize f c).toProblem.feasible x} :=
  (data .maximize f c).feasibleSetConvex

def unconstrainedData (f : X →ᵃ[ℝ] ℝ) : Data X where
  sense := .minimize
  objective := f
  rowCount := 0
  constraints := Fin.elim0

def unconstrainedForm (f : X →ᵃ[ℝ] ℝ) : Form (unconstrainedData f).toProblem where
  data := unconstrainedData f
  represents := rfl

example (f : X →ᵃ[ℝ] ℝ) : IsConic (unconstrainedData f).toProblem :=
  (unconstrainedForm f).isConic

example (f : X →ᵃ[ℝ] ℝ) (x : X) : (unconstrainedData f).toProblem.feasible x := by
  simp [unconstrainedData]

example (f : X →ᵃ[ℝ] ℝ) : Convex ℝ {x | (unconstrainedData f).toProblem.feasible x} :=
  (unconstrainedData f).feasibleSetConvex

end Algebraic

/-! ## Scalar minimization and maximization -/

def scalarNonnegative : Constraint ℝ where
  cone := Cone.nonnegative 1
  map := AffineMap.pi fun _ => AffineMap.id ℝ ℝ

def scalarMinimumData : Data ℝ where
  sense := .minimize
  objective := AffineMap.id ℝ ℝ
  rowCount := 1
  constraints := fun _ => scalarNonnegative

def scalarMinimum : Problem ℝ ℝ where
  objective := fun x => x
  feasible := fun x => ∀ _ : Fin 1, scalarNonnegative.Holds x

def scalarMinimumForm : Form scalarMinimum where
  data := scalarMinimumData
  represents := rfl

example : scalarMinimumForm.data = scalarMinimumData := rfl
example : scalarMinimumForm.data.sense = .minimize := rfl
example : scalarMinimumData.toProblem = scalarMinimum := scalarMinimumForm.represents
example : IsConic scalarMinimum := scalarMinimumForm.isConic
example (x : ℝ) : scalarMinimumData.toProblem.objective x = x := by
  simp [scalarMinimumData]

theorem scalarNonnegative_holds (x : ℝ) : scalarNonnegative.Holds x ↔ 0 ≤ x := by
  change (fun _ : Fin 1 => x) ∈ (Cone.nonnegative 1).carrier ↔ 0 ≤ x
  simp

example (x : ℝ) : scalarMinimumData.toProblem.feasible x ↔ 0 ≤ x := by
  change (∀ _ : Fin 1, scalarNonnegative.Holds x) ↔ 0 ≤ x
  simp [scalarNonnegative_holds]

example : Convex ℝ {x | scalarNonnegative.Holds x} :=
  scalarNonnegative.feasibleSetConvex

example : Convex ℝ {x | scalarMinimumData.toProblem.feasible x} :=
  scalarMinimumData.feasibleSetConvex

def scalarMaximumData : Data ℝ where
  sense := .maximize
  objective := AffineMap.id ℝ ℝ
  rowCount := 1
  constraints := fun _ => scalarNonnegative

/-- The source problem keeps the dual order explicit; the certificate keeps the
optimization sense explicit independently of representation equality. -/
def scalarMaximum : Problem ℝ (OrderDual ℝ) where
  objective := fun x => x
  feasible := fun x => ∀ _ : Fin 1, scalarNonnegative.Holds x

def scalarMaximumForm : Form scalarMaximum where
  data := scalarMaximumData
  represents := rfl

example : scalarMaximumForm.data = scalarMaximumData := rfl
example : scalarMaximumForm.data.sense = .maximize := rfl
example : scalarMaximumData.toProblem = scalarMaximum := scalarMaximumForm.represents
example : IsConic scalarMaximum := scalarMaximumForm.isConic

/-! ## Product decisions and heterogeneous cone dimensions -/

def productEquality : Constraint (ℝ × ℝ) where
  cone := Cone.zero 1
  map := AffineMap.pi fun _ => AffineMap.snd

def productInequalities : Constraint (ℝ × ℝ) where
  cone := Cone.nonnegative 2
  map := AffineMap.pi fun i : Fin 2 =>
    if i = 0 then AffineMap.fst + AffineMap.const ℝ (ℝ × ℝ) 1
    else AffineMap.snd

def productData : Data (ℝ × ℝ) where
  sense := .minimize
  objective := AffineMap.fst + AffineMap.const ℝ (ℝ × ℝ) 2
  rowCount := 2
  constraints := fun i => if i = 0 then productEquality else productInequalities

theorem productEquality_holds (x : ℝ × ℝ) : productEquality.Holds x ↔ x.2 = 0 := by
  change (fun _ : Fin 1 => x.2) ∈ (Cone.zero 1).carrier ↔ x.2 = 0
  simp [funext_iff]

theorem productInequalities_holds (x : ℝ × ℝ) :
    productInequalities.Holds x ↔ 0 ≤ x.1 + 1 ∧ 0 ≤ x.2 := by
  change (∀ i : Fin 2, 0 ≤
    (if i = 0 then AffineMap.fst + AffineMap.const ℝ (ℝ × ℝ) 1
      else AffineMap.snd) x) ↔ 0 ≤ x.1 + 1 ∧ 0 ≤ x.2
  simp [Fin.forall_fin_succ]

example (x : ℝ × ℝ) : productData.toProblem.objective x = x.1 + 2 := by
  simp [productData]

theorem productData_feasible (x : ℝ × ℝ) :
    productData.toProblem.feasible x ↔ x.2 = 0 ∧ 0 ≤ x.1 + 1 ∧ 0 ≤ x.2 := by
  change (∀ i : Fin 2, (if i = 0 then productEquality else productInequalities).Holds x) ↔
    x.2 = 0 ∧ 0 ≤ x.1 + 1 ∧ 0 ≤ x.2
  simp [Fin.forall_fin_succ, productEquality_holds, productInequalities_holds]

example : productData.toProblem.feasible (0, 0) := by
  rw [productData_feasible]
  simp

example : ¬ productData.toProblem.feasible (0, 1) := by
  rw [productData_feasible]
  simp

example : Convex ℝ {x | productData.toProblem.feasible x} :=
  productData.feasibleSetConvex

/-! ## Finite-vector decisions and the zero-row case -/

def vectorData : Data (Fin 3 → ℝ) where
  sense := .minimize
  objective := AffineMap.proj 0
  rowCount := 1
  constraints := fun _ => {
    cone := Cone.nonnegative 3
    map := AffineMap.id ℝ (Fin 3 → ℝ)
  }

example (x : Fin 3 → ℝ) : vectorData.toProblem.feasible x ↔ ∀ i, 0 ≤ x i := by
  change (∀ _ : Fin 1, x ∈ (Cone.nonnegative 3).carrier) ↔ ∀ i, 0 ≤ x i
  simp

example : Convex ℝ {x | vectorData.toProblem.feasible x} :=
  vectorData.feasibleSetConvex

def unconstrainedData : Data ℝ where
  sense := .minimize
  objective := AffineMap.const ℝ ℝ 4
  rowCount := 0
  constraints := Fin.elim0

example (x : ℝ) : unconstrainedData.toProblem.feasible x := by
  simp [unconstrainedData]

example (x : ℝ) : unconstrainedData.toProblem.objective x = 4 := by
  simp [unconstrainedData]

example : Convex ℝ {x | unconstrainedData.toProblem.feasible x} :=
  unconstrainedData.feasibleSetConvex

/-! ## Malformed constructions are rejected -/

-- An arbitrary carrier predicate cannot stand in for the checked cone laws.
example : True := by
  fail_if_success
    let _ : Cone := { Space := ℝ, carrier := { carrier := {x | x = 1} } }
  trivial

-- A row's affine map must land in its selected cone's space.
example : True := by
  fail_if_success
    let _ : Constraint ℝ := {
      cone := Cone.zero 2
      map := AffineMap.pi fun _ : Fin 1 => AffineMap.id ℝ ℝ
    }
  trivial

-- Matching types alone do not certify a different objective.
example : True := by
  fail_if_success
    let _ : Form (Problem.mk (fun _ : ℝ => (0 : ℝ)) fun _ => True) := {
      data := unconstrainedData
      represents := rfl
    }
  trivial

end

end MorewTest.Conic
