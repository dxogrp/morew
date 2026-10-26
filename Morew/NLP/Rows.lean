/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Basic
import Morew.NLP.Domain
import Mathlib.Algebra.BigOperators.Fin

/-!
# Smoothness evidence for generated constraint rows

These certificates describe only the supplied predicates. They make no claim
about an objective or any other constraints. Finite families stay grouped, and
each closed scalar comparison records smoothness of its exact difference.

`Block` additionally retains the concrete scalar rows in `Type`, so terminal
validation can construct NLP data without extracting data from a proof. Finite
families use the ordered finite-sum equivalence; symbolic dimensions and empty
families need no enumeration during elaboration.
-/

namespace Morew.NLP.Rows

/-- The exact upper-bound normalization recorded by a scalar row certificate. -/
theorem upper_residual_iff (lhs rhs : ℝ) :
    (Bounds.upperBound 0).Contains (lhs - rhs) ↔ lhs ≤ rhs := by
  rw [Bounds.contains_upperBound]
  exact sub_nonpos

/-- The exact lower-bound normalization recorded by a scalar row certificate. -/
theorem lower_residual_iff (lhs rhs : ℝ) :
    (Bounds.lowerBound 0).Contains (lhs - rhs) ↔ lhs ≥ rhs := by
  rw [Bounds.contains_lowerBound]
  exact sub_nonneg

/-- The exact equality normalization recorded by a scalar row certificate. -/
theorem fixed_residual_iff (lhs rhs : ℝ) :
    (Bounds.fixed 0).Contains (lhs - rhs) ↔ lhs = rhs := by
  rw [Bounds.contains_fixed]
  exact sub_eq_zero

/-- Canonical vector upper bounds are coordinatewise scalar bounds. -/
theorem vector_le_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs ≤ rhs ↔ ∀ i, lhs i ≤ rhs i := Iff.rfl

/-- Canonical vector lower bounds are coordinatewise scalar bounds. -/
theorem vector_ge_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs ≥ rhs ↔ ∀ i, lhs i ≥ rhs i := Iff.rfl

/-- Vector equality is exactly coordinatewise scalar equality. -/
theorem vector_eq_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs = rhs ↔ ∀ i, lhs i = rhs i := funext_iff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A predicate assembled from smooth closed scalar residuals on one domain. -/
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
  /-- Checked logical transport preserves the original row predicate. -/
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

/-- Rebase existing grammatical certificates along a globally smooth map. -/
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

/-- Smooth rebasing preserves openness of the evaluation domain. -/
theorem preimage_open {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (domain : Set X) (f : Y → X) (open_domain : IsOpen domain)
    (smooth : ContDiff ℝ 2 f) : IsOpen (f ⁻¹' domain) :=
  open_domain.preimage smooth.continuous

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Rebased feasibility supplies membership in the pulled-back domain. -/
theorem preimage_includes {Y : Type*} (domain : Set X) (p : X → Prop)
    (f : Y → X) (includes : ∀ x, p x → x ∈ domain) :
    ∀ y, p (f y) → y ∈ f ⁻¹' domain :=
  fun y hy => includes (f y) hy

/-- Concrete smooth scalar rows representing exactly one predicate.
The domain is evaluation evidence and is not included in `holds_iff`. -/
structure Block (domain : Set X) (predicate : X → Prop) where
  /-- The number of normalized scalar rows, possibly symbolic or zero. -/
  rowCount : Nat
  /-- The actual residuals and bounds, with smoothness on the shared domain. -/
  rows : Fin rowCount → Row X domain
  /-- Row-only satisfaction is equivalent to the original predicate. -/
  holds_iff : ∀ x, (∀ i, (rows i).Holds x) ↔ predicate x

namespace Block

variable {domain : Set X} {p q : X → Prop}

/-- An exposed `True` predicate contributes no scalar rows. -/
def truth (domain : Set X) : Block domain (fun _ => True) where
  rowCount := 0
  rows := Fin.elim0
  holds_iff _ := ⟨fun _ => trivial, fun _ i => Fin.elim0 i⟩

/-- Retain the exact difference with its closed upper bound at zero. -/
def le (domain : Set X) (lhs rhs : X → ℝ)
    (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
    Block domain (fun x => lhs x ≤ rhs x) where
  rowCount := 1
  rows := fun _ => ⟨fun x => lhs x - rhs x, .upperBound 0, smooth⟩
  holds_iff _ := ⟨fun h => (upper_residual_iff _ _).mp (h 0),
    fun h _ => (upper_residual_iff _ _).mpr h⟩

/-- Retain the exact difference with its closed lower bound at zero. -/
def ge (domain : Set X) (lhs rhs : X → ℝ)
    (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
    Block domain (fun x => lhs x ≥ rhs x) where
  rowCount := 1
  rows := fun _ => ⟨fun x => lhs x - rhs x, .lowerBound 0, smooth⟩
  holds_iff _ := ⟨fun h => (lower_residual_iff _ _).mp (h 0),
    fun h _ => (lower_residual_iff _ _).mpr h⟩

/-- Retain the exact difference fixed at zero. -/
def eq (domain : Set X) (lhs rhs : X → ℝ)
    (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
    Block domain (fun x => lhs x = rhs x) where
  rowCount := 1
  rows := fun _ => ⟨fun x => lhs x - rhs x, .fixed 0, smooth⟩
  holds_iff _ := ⟨fun h => (fixed_residual_iff _ _).mp (h 0),
    fun h _ => (fixed_residual_iff _ _).mpr h⟩

/-- Append conjunction rows in left-to-right order, without merging bounds. -/
def and (left : Block domain p) (right : Block domain q) :
    Block domain (fun x => p x ∧ q x) where
  rowCount := left.rowCount + right.rowCount
  rows := Fin.addCases left.rows right.rows
  holds_iff x := by
    constructor
    · intro h
      exact ⟨(left.holds_iff x).mp (fun i => by simpa using h (Fin.castAdd _ i)),
        (right.holds_iff x).mp (fun i => by simpa using h (Fin.natAdd _ i))⟩
    · rintro ⟨hl, hr⟩ i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using (left.holds_iff x).mpr hl j
      · simpa using (right.holds_iff x).mpr hr j

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
    constructor
    · intro h i
      apply ((blocks i).holds_iff x).mp
      intro j
      have hi := h (finSigmaFinEquiv ⟨i, j⟩)
      dsimp only at hi
      exact Eq.mp (congrArg
        (fun ij : (i : Fin n) × Fin (blocks i).rowCount =>
          ((blocks ij.1).rows ij.2).Holds x)
        (finSigmaFinEquiv.symm_apply_apply ⟨i, j⟩)) hi
    · intro h j
      exact ((blocks _).holds_iff x).mpr (h _) _

/-- The ordered finite-sum index recovers the original coordinate row. -/
@[simp]
theorem family_rows {n : Nat} (p : Fin n → X → Prop)
    (blocks : ∀ i, Block domain (p i)) (i : Fin n) (j : Fin (blocks i).rowCount) :
    (family p blocks).rows (finSigmaFinEquiv ⟨i, j⟩) = (blocks i).rows j := by
  dsimp only [family]
  exact congrArg (fun ij : (i : Fin n) × Fin (blocks i).rowCount => (blocks ij.1).rows ij.2)
    (finSigmaFinEquiv.symm_apply_apply ⟨i, j⟩)

/-- Logical transport changes only the predicate represented by the row block. -/
def ofIff (p q : X → Prop) (equivalent : ∀ x, p x ↔ q x)
    (block : Block domain q) : Block domain p where
  rowCount := block.rowCount
  rows := block.rows
  holds_iff x := (block.holds_iff x).trans (equivalent x).symm

/-- Restrict evaluation evidence without changing residuals, bounds, or order. -/
def mono {s t : Set X} (block : Block s p) (subset : t ⊆ s) : Block t p where
  rowCount := block.rowCount
  rows i := { block.rows i with smooth := (block.rows i).smooth.mono subset }
  holds_iff := block.holds_iff

/-- Rebase accepted rows along a smooth map, in particular an auxiliary-variable
projection, without discovering their expressions or evidence again. -/
def pullback {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (block : Block domain p) (f : Y → X) (smooth : ContDiff ℝ 2 f) :
    Block (f ⁻¹' domain) (fun y => p (f y)) where
  rowCount := block.rowCount
  rows i := {
    residual := fun y => (block.rows i).residual (f y)
    bounds := (block.rows i).bounds
    smooth := (block.rows i).smooth.comp smooth.contDiffOn (fun _ h => h) }
  holds_iff y := block.holds_iff (f y)

/-- Assemble an exact form from complete row data and objective/domain proofs.
The separately supplied sense does not follow from representation equality. -/
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
  represents := by
    cases problem with
    | mk objective feasible =>
      change ({ objective := objective, feasible := _ } : Problem X ℝ) =
        { objective := objective, feasible := feasible }
      congr 1
      exact funext fun x => propext (block.holds_iff x)

end Block

end Morew.NLP.Rows
