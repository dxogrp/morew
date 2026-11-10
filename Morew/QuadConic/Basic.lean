/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Certified quadratic cone programs

The objective is a homogeneous quadratic form plus an affine map. Its quadratic
part is nonnegative for minimization and nonpositive for maximization. Rows use
the existing affine cone constraints.

Objective sense is stored separately because `OrderDual ℝ` is definitionally
equal to `ℝ`. `Form` certifies the represented objective and feasible set; the
terminal command also checks the stored sense against the problem declaration.
-/

namespace Morew

universe u

namespace QuadConic

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- The sign of a homogeneous quadratic form required by an objective sense. -/
def Curvature (sense : ObjectiveSense) (quadratic : QuadraticForm ℝ X) : Prop :=
  match sense with
  | .minimize => ∀ x, 0 ≤ quadratic x
  | .maximize => ∀ x, quadratic x ≤ 0

/-- The zero quadratic form has the required curvature for either sense. -/
theorem curvature_zero (sense : ObjectiveSense) :
    Curvature sense (0 : QuadraticForm ℝ X) := by
  cases sense <;> intro x <;> simp

/-- A nonnegative homogeneous quadratic form is convex. -/
theorem convexOn_quadratic (quadratic : QuadraticForm ℝ X)
    (nonnegative : ∀ x, 0 ≤ quadratic x) : ConvexOn ℝ Set.univ quadratic := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hsub : quadratic (x - y) =
      quadratic x + quadratic y - QuadraticMap.polar quadratic x y := by
    simp only [sub_eq_add_neg, QuadraticMap.map_add,
      quadratic.map_neg, quadratic.polar_neg_right]
  have hcombo : quadratic (a • x + b • y) = a * a * quadratic x +
      b * b * quadratic y + a * b * QuadraticMap.polar quadratic x y := by
    simp only [QuadraticMap.map_add, quadratic.map_smul,
      quadratic.polar_smul_left, quadratic.polar_smul_right, smul_eq_mul]
    ring
  simp only [smul_eq_mul]
  calc
    quadratic (a • x + b • y) =
        a * quadratic x + b * quadratic y - a * b * quadratic (x - y) := by
      rw [hcombo, hsub]
      have ha' : a = 1 - b := by linarith
      rw [ha']
      ring
    _ ≤ a * quadratic x + b * quadratic y :=
      sub_le_self _ (mul_nonneg (mul_nonneg ha hb) (nonnegative (x - y)))

/-- A nonpositive homogeneous quadratic form is concave. -/
theorem concaveOn_quadratic (quadratic : QuadraticForm ℝ X)
    (nonpositive : ∀ x, quadratic x ≤ 0) : ConcaveOn ℝ Set.univ quadratic := by
  have hconvex : ConvexOn ℝ Set.univ (-(quadratic : X → ℝ)) :=
    convexOn_quadratic (-quadratic) (fun x => neg_nonneg.mpr (nonpositive x))
  simpa only [neg_neg] using hconvex.neg

/-- Finite-dimensional quadratic cone-program data.

The objective is `quadratic x + affine x`, without an implicit factor of one
half. The original objective, including its constant term, is retained. -/
structure Data (X : Type u) [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] where
  /-- The optimization direction. -/
  sense : ObjectiveSense
  /-- The homogeneous quadratic part of the objective. -/
  quadratic : QuadraticForm ℝ X
  /-- The affine part of the objective, including its constant term. -/
  affine : X →ᵃ[ℝ] ℝ
  /-- Curvature has the sign required by the stored direction. -/
  curvature : Curvature sense quadratic
  /-- The number of cone constraints. -/
  rowCount : Nat
  /-- The affine cone-membership rows. -/
  constraints : Fin rowCount → Conic.Constraint X

variable [FiniteDimensional ℝ X]

namespace Data

/-- The full real-valued objective, without changing its sign for maximization. -/
def objective (data : Data X) (x : X) : ℝ :=
  data.quadratic x + data.affine x

/-- The problem with the stored objective and all stored rows. -/
def toProblem (data : Data X) : Problem X ℝ where
  objective := data.objective
  feasible x := ∀ i, (data.constraints i).Holds x

/-- Conversion to a problem preserves the complete objective. -/
@[simp]
theorem toProblem_objective (data : Data X) (x : X) :
    data.toProblem.objective x = data.quadratic x + data.affine x := rfl

/-- Conversion to a problem requires exactly all stored rows. -/
@[simp]
theorem toProblem_feasible (data : Data X) (x : X) :
    data.toProblem.feasible x ↔ ∀ i, (data.constraints i).Holds x := Iff.rfl

/-- The feasible set of a quadratic cone program is convex. -/
theorem feasibleSetConvex (data : Data X) :
    Convex ℝ {x | data.toProblem.feasible x} := by
  simpa only [toProblem_feasible, Set.ofPred_forall] using
    convex_iInter (fun i => (data.constraints i).feasibleSetConvex)

/-- A minimizing quadratic cone program has a convex objective. -/
theorem objective_convexOn (data : Data X) (sense : data.sense = .minimize) :
    ConvexOn ℝ Set.univ data.objective := by
  have hquadratic := convexOn_quadratic data.quadratic
    (by simpa only [Curvature, sense] using data.curvature)
  have haffine : ConvexOn ℝ Set.univ data.affine := by
    simpa using (convexOn_id (𝕜 := ℝ) (s := Set.univ) convex_univ).comp_affineMap data.affine
  exact hquadratic.add haffine

/-- A maximizing quadratic cone program has a concave objective. -/
theorem objective_concaveOn (data : Data X) (sense : data.sense = .maximize) :
    ConcaveOn ℝ Set.univ data.objective := by
  have hquadratic := concaveOn_quadratic data.quadratic
    (by simpa only [Curvature, sense] using data.curvature)
  have haffine : ConcaveOn ℝ Set.univ data.affine := by
    simpa using (concaveOn_id (𝕜 := ℝ) (s := Set.univ) convex_univ).comp_affineMap data.affine
  exact hquadratic.add haffine

/-- Embed affine cone-program data with zero quadratic part. -/
def ofConic (data : Conic.Data X) : Data X where
  sense := data.sense
  quadratic := 0
  affine := data.objective
  curvature := curvature_zero data.sense
  rowCount := data.rowCount
  constraints := data.constraints

/-- Affine embedding preserves the original objective and feasible set. -/
@[simp]
theorem ofConic_toProblem (data : Conic.Data X) :
    (ofConic data).toProblem = data.toProblem := by
  apply congrArg₂ Problem.mk
  · funext x
    exact zero_add (data.objective x)
  · rfl

/-- Affine embedding preserves the stored optimization direction. -/
@[simp]
theorem ofConic_sense (data : Conic.Data X) :
    (ofConic data).sense = data.sense := rfl

end Data

/-- A quadratic conic representation with the same objective and feasible set.
Its optimization direction is stored in `data.sense`. -/
structure Form (p : Problem X ℝ) where
  /-- The quadratic cone-program data, including curvature evidence. -/
  data : Data X
  /-- The data represents the entire problem exactly. -/
  represents : data.toProblem = p

/-- A represented quadratic cone program has a convex feasible set. -/
theorem Form.feasibleSetConvex {p : Problem X ℝ} (form : Form p) :
    Convex ℝ {x | p.feasible x} := by
  rw [← form.represents]
  exact form.data.feasibleSetConvex

/-- A representation with minimizing sense certifies convexity of the objective. -/
theorem Form.objective_convexOn {p : Problem X ℝ} (form : Form p)
    (sense : form.data.sense = .minimize) : ConvexOn ℝ Set.univ p.objective := by
  rw [← form.represents]
  exact form.data.objective_convexOn sense

/-- A representation with maximizing sense certifies concavity of the objective. -/
theorem Form.objective_concaveOn {p : Problem X ℝ} (form : Form p)
    (sense : form.data.sense = .maximize) : ConcaveOn ℝ Set.univ p.objective := by
  rw [← form.represents]
  exact form.data.objective_concaveOn sense

/-- Embed an affine conic form, preserving its objective, rows, and stored sense. -/
def Form.ofConic {p : Problem X ℝ} (form : Conic.Form p) : Form p where
  data := Data.ofConic form.data
  represents := (Data.ofConic_toProblem form.data).trans form.represents

/-- Embedding an affine form preserves its optimization direction. -/
@[simp]
theorem Form.ofConic_sense {p : Problem X ℝ} (form : Conic.Form p) :
    (Form.ofConic form).data.sense = form.data.sense := rfl

end QuadConic

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]

/-- Existence of a quadratic conic representation with a stored objective sense.
`QuadConic.Form` carries the data and its curvature certificate. -/
def IsQuadConic (p : Problem X ℝ) : Prop :=
  Nonempty (QuadConic.Form p)

/-- A quadratic conic representation implies `IsQuadConic`. -/
theorem QuadConic.Form.isQuadConic {p : Problem X ℝ} (form : QuadConic.Form p) :
    IsQuadConic p := ⟨form⟩

end Morew
