/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Basic
import Morew.NLP.Domain
import Mathlib.Algebra.BigOperators.Fin

/-!
# Smoothness evidence for generated constraint rows

`Block` represents a predicate by smooth scalar residuals with closed bounds.
Finite families are ordered by coordinate.
-/

namespace Morew.NLP.Rows

/-- The bound `lhs ≤ rhs` is equivalent to `lhs - rhs ≤ 0`. -/
theorem upper_residual_iff (lhs rhs : ℝ) :
    (Bounds.upperBound 0).Contains (lhs - rhs) ↔ lhs ≤ rhs := by
  rw [Bounds.contains_upperBound]
  exact sub_nonpos

/-- The bound `rhs ≤ lhs` is equivalent to `0 ≤ lhs - rhs`. -/
theorem lower_residual_iff (lhs rhs : ℝ) :
    (Bounds.lowerBound 0).Contains (lhs - rhs) ↔ lhs ≥ rhs := by
  rw [Bounds.contains_lowerBound]
  exact sub_nonneg

/-- The equality `lhs = rhs` is equivalent to `lhs - rhs = 0`. -/
theorem fixed_residual_iff (lhs rhs : ℝ) :
    (Bounds.fixed 0).Contains (lhs - rhs) ↔ lhs = rhs := by
  rw [Bounds.contains_fixed]
  exact sub_eq_zero

/-- Vector upper bounds are equivalent to componentwise scalar bounds. -/
theorem vector_le_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs ≤ rhs ↔ ∀ i, lhs i ≤ rhs i := Iff.rfl

/-- Vector lower bounds are equivalent to componentwise scalar bounds. -/
theorem vector_ge_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs ≥ rhs ↔ ∀ i, lhs i ≥ rhs i := Iff.rfl

/-- Vector equality is exactly coordinatewise scalar equality. -/
theorem vector_eq_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs = rhs ↔ ∀ i, lhs i = rhs i := funext_iff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A predicate assembled from smooth scalar residuals with closed bounds on one domain. -/
inductive Certified (domain : Set X) : (X → Prop) → Prop where
  /-- The empty row imposes no condition. -/
  | truth : Certified domain (fun _ => True)
  /-- Both constituent rows use the same evaluation domain. -/
  | and {p q : X → Prop} : Certified domain p → Certified domain q →
      Certified domain (fun x => p x ∧ q x)
  /-- An upper bound has residual `lhs - rhs` bounded above by zero. -/
  | le (lhs rhs : X → ℝ)
      (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
      Certified domain (fun x => lhs x ≤ rhs x)
  /-- A lower bound has residual `lhs - rhs` bounded below by zero. -/
  | ge (lhs rhs : X → ℝ)
      (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
      Certified domain (fun x => lhs x ≥ rhs x)
  /-- Equality fixes the residual `lhs - rhs` at zero. -/
  | eq (lhs rhs : X → ℝ)
      (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
      Certified domain (fun x => lhs x = rhs x)
  /-- A symbolic finite family retains its coordinate predicates. -/
  | family {n : ℕ} (p : Fin n → X → Prop)
      (certified : ∀ i, Certified domain (p i)) :
      Certified domain (fun x => ∀ i, p i x)
  /-- A constraint equivalent to one represented by smooth residuals has the same representation. -/
  | of_iff (p q : X → Prop) (equivalent : ∀ x, p x ↔ q x)
      (certified : Certified domain q) : Certified domain p

/-- A generated row remains certified on a smaller common domain. -/
theorem Certified.mono {s t : Set X} {p : X → Prop}
    (certified : Certified s p) (subset : t ⊆ s) : Certified t p := by
  induction certified with
  | truth => exact .truth
  | and _ _ left right => exact .and left right
  | le lhs rhs smooth => exact .le lhs rhs (smooth.mono subset)
  | ge lhs rhs smooth => exact .ge lhs rhs (smooth.mono subset)
  | eq lhs rhs smooth => exact .eq lhs rhs (smooth.mono subset)
  | family p _ ih => exact .family p ih
  | of_iff p q equivalent _ ih => exact .of_iff p q equivalent ih

/-- Pull back row certificates along a globally smooth map. -/
theorem Certified.pullback {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {domain : Set X} {p : X → Prop} (certified : Certified domain p)
    (f : Y → X) (smooth : ContDiff ℝ 2 f) :
    Certified (f ⁻¹' domain) (fun y => p (f y)) := by
  induction certified with
  | truth => exact .truth
  | and _ _ left right => exact .and left right
  | le lhs rhs residual =>
    exact .le (fun y => lhs (f y)) (fun y => rhs (f y))
      (residual.comp smooth.contDiffOn (fun _ h => h))
  | ge lhs rhs residual =>
    exact .ge (fun y => lhs (f y)) (fun y => rhs (f y))
      (residual.comp smooth.contDiffOn (fun _ h => h))
  | eq lhs rhs residual =>
    exact .eq (fun y => lhs (f y)) (fun y => rhs (f y))
      (residual.comp smooth.contDiffOn (fun _ h => h))
  | family p _ ih => exact .family (fun i y => p i (f y)) ih
  | of_iff p q equivalent _ ih =>
    exact .of_iff (fun y => p (f y)) (fun y => q (f y)) (fun y => equivalent (f y)) ih

/-- The preimage of an open domain under a smooth map is open. -/
theorem preimage_open {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (domain : Set X) (f : Y → X) (open_domain : IsOpen domain)
    (smooth : ContDiff ℝ 2 f) : IsOpen (f ⁻¹' domain) :=
  open_domain.preimage smooth.continuous

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Feasibility after composition implies membership in the preimage domain. -/
theorem preimage_includes {Y : Type*} (domain : Set X) (p : X → Prop)
    (f : Y → X) (includes : ∀ x, p x → x ∈ domain) :
    ∀ y, p (f y) → y ∈ f ⁻¹' domain :=
  fun y hy => includes (f y) hy

/-- Smooth scalar constraints whose conjunction is equivalent to one predicate.
The domain specifies where the residuals are smooth. -/
structure Block (domain : Set X) (predicate : X → Prop) where
  /-- The number of scalar rows. -/
  rowCount : Nat
  /-- The actual residuals and bounds, with smoothness on the shared domain. -/
  rows : Fin rowCount → Row X domain
  /-- Satisfaction of all rows is equivalent to the original predicate. -/
  holds_iff : ∀ x, (∀ i, (rows i).Holds x) ↔ predicate x

namespace Block

variable {domain : Set X} {p q : X → Prop}

/-- The predicate `True` contributes no scalar constraints. -/
def truth (domain : Set X) : Block domain (fun _ => True) where
  rowCount := 0
  rows := Fin.elim0
  holds_iff _ := ⟨fun _ => trivial, fun _ i => Fin.elim0 i⟩

/-- Bound `lhs - rhs` above by zero. -/
def le (domain : Set X) (lhs rhs : X → ℝ)
    (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
    Block domain (fun x => lhs x ≤ rhs x) where
  rowCount := 1
  rows := fun _ => ⟨fun x => lhs x - rhs x, .upperBound 0, smooth⟩
  holds_iff _ := (forall_const (Fin 1)).trans (upper_residual_iff _ _)

/-- Bound `lhs - rhs` below by zero. -/
def ge (domain : Set X) (lhs rhs : X → ℝ)
    (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
    Block domain (fun x => lhs x ≥ rhs x) where
  rowCount := 1
  rows := fun _ => ⟨fun x => lhs x - rhs x, .lowerBound 0, smooth⟩
  holds_iff _ := (forall_const (Fin 1)).trans (lower_residual_iff _ _)

/-- Set `lhs - rhs` equal to zero. -/
def eq (domain : Set X) (lhs rhs : X → ℝ)
    (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
    Block domain (fun x => lhs x = rhs x) where
  rowCount := 1
  rows := fun _ => ⟨fun x => lhs x - rhs x, .fixed 0, smooth⟩
  holds_iff _ := (forall_const (Fin 1)).trans (fixed_residual_iff _ _)

/-- Concatenate the rows of a conjunction in left-to-right order. -/
def and (left : Block domain p) (right : Block domain q) :
    Block domain (fun x => p x ∧ q x) where
  rowCount := left.rowCount + right.rowCount
  rows := Fin.addCases left.rows right.rows
  holds_iff x := by
    simp only [Fin.forall_fin_add, Fin.addCases_left, Fin.addCases_right,
      left.holds_iff, right.holds_iff]

/-- Left rows retain their indices when a conjunction is appended. -/
@[simp]
theorem and_rows_left (left : Block domain p) (right : Block domain q)
    (i : Fin left.rowCount) :
    (left.and right).rows (Fin.castAdd right.rowCount i) = left.rows i := by
  simp [and]

/-- Right rows follow all of the left rows. -/
@[simp]
theorem and_rows_right (left : Block domain p) (right : Block domain q)
    (i : Fin right.rowCount) :
    (left.and right).rows (Fin.natAdd left.rowCount i) = right.rows i := by
  simp [and]

/-- Concatenate a finite family in increasing coordinate order.
Each coordinate may itself contribute a different number of scalar rows. -/
def family {n : Nat} (p : Fin n → X → Prop)
    (blocks : ∀ i, Block domain (p i)) :
    Block domain (fun x => ∀ i, p i x) where
  rowCount := ∑ i, (blocks i).rowCount
  rows := fun j =>
    let ij := finSigmaFinEquiv.symm j
    (blocks ij.1).rows ij.2
  holds_iff x := by
    rw [← finSigmaFinEquiv.forall_congr_left
      (p := fun ij : (i : Fin n) × Fin (blocks i).rowCount =>
        ((blocks ij.1).rows ij.2).Holds x)]
    simp only [Sigma.forall, Block.holds_iff]

/-- The ordered finite-sum index recovers the original coordinate row. -/
@[simp]
theorem family_rows {n : Nat} (p : Fin n → X → Prop)
    (blocks : ∀ i, Block domain (p i)) (i : Fin n) (j : Fin (blocks i).rowCount) :
    (family p blocks).rows (finSigmaFinEquiv ⟨i, j⟩) = (blocks i).rows j := by
  dsimp only [family]
  exact congrArg (fun ij : (i : Fin n) × Fin (blocks i).rowCount => (blocks ij.1).rows ij.2)
    (finSigmaFinEquiv.symm_apply_apply ⟨i, j⟩)

/-- Represent an equivalent predicate using the same residuals and bounds. -/
def ofIff (p q : X → Prop) (equivalent : ∀ x, p x ↔ q x)
    (block : Block domain q) : Block domain p where
  rowCount := block.rowCount
  rows := block.rows
  holds_iff x := (block.holds_iff x).trans (equivalent x).symm

/-- Restrict the evaluation domain, preserving residuals, bounds, and row order. -/
def mono {s t : Set X} (block : Block s p) (subset : t ⊆ s) : Block t p where
  rowCount := block.rowCount
  rows i := { block.rows i with smooth := (block.rows i).smooth.mono subset }
  holds_iff := block.holds_iff

/-- Pull back rows along a smooth map, including a projection from auxiliary variables. -/
def pullback {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (block : Block domain p) (f : Y → X) (smooth : ContDiff ℝ 2 f) :
    Block (f ⁻¹' domain) (fun y => p (f y)) where
  rowCount := block.rowCount
  rows i := {
    residual := fun y => (block.rows i).residual (f y)
    bounds := (block.rows i).bounds
    smooth := (block.rows i).smooth.comp smooth.contDiffOn (fun _ h => h) }
  holds_iff y := block.holds_iff (f y)

/-- Assemble an exact form from row data, an objective, smoothness and domain
proofs, and the separately supplied objective sense. -/
def toForm [FiniteDimensional ℝ X] (problem : Problem X ℝ)
    (block : Block domain problem.feasible) (sense : ObjectiveSense)
    (domain_isOpen : IsOpen domain)
    (objective_smooth : ContDiffOn ℝ 2 problem.objective domain)
    (feasible_mem_domain : ∀ x, problem.feasible x → x ∈ domain) : Form problem where
  data := {
    sense := sense
    domain := domain
    domain_isOpen := domain_isOpen
    objective := problem.objective
    objective_smooth := objective_smooth
    rowCount := block.rowCount
    rows := block.rows
    feasible_mem_domain := fun x hx => feasible_mem_domain x ((block.holds_iff x).mp hx) }
  represents := congrArg (Problem.mk problem.objective)
    (funext fun x => propext (block.holds_iff x))

end Block

end Morew.NLP.Rows
