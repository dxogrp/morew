/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.QuadConic.Basic
import Morew.Affine
import Morew.Fn.Norm
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Certified quadratic objectives

These constructions retain a homogeneous quadratic form, an affine remainder,
and pointwise equality with the original objective, including its constant term.
`Certified` records this decomposition without a curvature assumption. Separate
lemmas prove the global sign of the quadratic part; affine terms impose no sign
condition.
-/

namespace Morew.QuadConic

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- A quadratic form and an affine map representing a scalar function exactly. -/
structure Certified (f : X → ℝ) where
  /-- The homogeneous quadratic part. -/
  quadratic : QuadraticForm ℝ X
  /-- The affine remainder, including the constant term. -/
  affine : X →ᵃ[ℝ] ℝ
  /-- The two parts sum to the original function at every point. -/
  correct : ∀ x, quadratic x + affine x = f x

namespace Certified

variable {f g : X → ℝ}

/-- The homogeneous quadratic part is nonnegative. -/
def Nonnegative (a : Certified f) : Prop := ∀ x, 0 ≤ a.quadratic x

/-- The homogeneous quadratic part is nonpositive. -/
def Nonpositive (a : Certified f) : Prop := ∀ x, a.quadratic x ≤ 0

/-- An affine expression has zero homogeneous quadratic part. -/
def ofAffine (a : Affine.Certified f) : Certified f where
  quadratic := 0
  affine := a.map
  correct x := by simpa using a.correct x

/-- Transfer a representation along a pointwise equality. -/
def transport (a : Certified f) (h : ∀ x, f x = g x) : Certified g where
  quadratic := a.quadratic
  affine := a.affine
  correct x := (a.correct x).trans (h x)

/-- Add two quadratic objectives. -/
def add (a : Certified f) (b : Certified g) : Certified (fun x => f x + g x) where
  quadratic := a.quadratic + b.quadratic
  affine := a.affine + b.affine
  correct x := by
    change a.quadratic x + b.quadratic x + (a.affine x + b.affine x) = _
    rw [← a.correct x, ← b.correct x]
    ring

/-- Subtract two quadratic objectives. -/
def sub (a : Certified f) (b : Certified g) : Certified (fun x => f x - g x) where
  quadratic := a.quadratic - b.quadratic
  affine := a.affine - b.affine
  correct x := by
    change a.quadratic x - b.quadratic x + (a.affine x - b.affine x) = _
    rw [← a.correct x, ← b.correct x]
    ring

/-- Negate a quadratic objective. -/
def neg (a : Certified f) : Certified (fun x => -f x) where
  quadratic := -a.quadratic
  affine := -a.affine
  correct x := by
    change -a.quadratic x + -a.affine x = _
    rw [← a.correct x]
    ring

/-- Scale a quadratic objective by a fixed real scalar. -/
def smul (c : ℝ) (a : Certified f) : Certified (fun x => c • f x) where
  quadratic := c • a.quadratic
  affine := c • a.affine
  correct x := by
    change c * a.quadratic x + c * a.affine x = c * f x
    rw [← mul_add, a.correct]

/-- Multiply a quadratic objective by a constant on the left. -/
def mulConstLeft (c : ℝ) (a : Certified f) : Certified (fun x => c * f x) := smul c a

/-- Multiply a quadratic objective by a constant on the right. -/
def mulConstRight (a : Certified f) (c : ℝ) : Certified (fun x => f x * c) :=
  (smul c a).transport fun x => mul_comm c (f x)

/-- Divide a quadratic objective by a fixed nonzero constant. -/
noncomputable def divConst (a : Certified f) (c : ℝ) (_h : c ≠ 0) :
    Certified (fun x => f x / c) :=
  (mulConstRight a c⁻¹).transport fun x => (div_eq_mul_inv (f x) c).symm

/-- Sum a finite family of quadratic objectives. -/
def sum {ι : Type*} {f : ι → X → ℝ} (s : Finset ι)
    (a : ∀ i, Certified (f i)) : Certified (fun x => ∑ i ∈ s, f i x) where
  quadratic := ∑ i ∈ s, (a i).quadratic
  affine := ∑ i ∈ s, (a i).affine
  correct x := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, add_apply,
          AffineMap.coe_add, Pi.add_apply]
        rw [← (a i).correct x, ← ih]
        ring

/-- Split `(L x + b)²` into the quadratic part `(L x)²` and the affine remainder
`2 * b * L x + b²`. -/
def square (a : Affine.Certified f) : Certified (fun x => f x ^ (2 : ℕ)) where
  quadratic := (QuadraticMap.sq (R := ℝ)).comp a.map.linear
  affine := (2 * a.map 0) • a.map.linear.toAffineMap +
    AffineMap.const ℝ X (a.map 0 ^ (2 : ℕ))
  correct x := by
    have hx : a.map x = a.map.linear x + a.map 0 := congrFun a.map.decomp x
    rw [← a.correct x, hx]
    change a.map.linear x * a.map.linear x +
      (2 * a.map 0 * a.map.linear x + a.map 0 ^ (2 : ℕ)) = _
    ring

/-- Split `‖L x + b‖²` into the quadratic part `‖L x‖²` and the affine remainder
`2 * ⟪b, L x⟫ + ‖b‖²` in a real inner product space. -/
noncomputable def normSq {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {f : X → Y} (a : Affine.Certified f) : Certified (fun x => ‖f x‖ ^ (2 : ℕ)) where
  quadratic := (LinearMap.BilinMap.toQuadraticMap (innerₗ Y)).comp a.map.linear
  affine := (2 : ℝ) • ((innerₗ Y (a.map 0)).comp a.map.linear).toAffineMap +
    AffineMap.const ℝ X (‖a.map 0‖ ^ (2 : ℕ))
  correct x := by
    have hx : a.map x = a.map.linear x + a.map 0 := congrFun a.map.decomp x
    rw [← a.correct x, hx, norm_add_sq_real]
    change inner (𝕜 := ℝ) (a.map.linear x) (a.map.linear x) +
      (2 * inner (𝕜 := ℝ) (a.map 0) (a.map.linear x) + ‖a.map 0‖ ^ (2 : ℕ)) = _
    rw [real_inner_self_eq_norm_sq, real_inner_comm (a.map 0)]
    ring

/-- The square of the named Euclidean norm of an affine coordinate vector. -/
noncomputable def fnNorm2Sq {n : Nat} {f : X → Fin n → ℝ} (a : Affine.Certified f) :
    Certified (fun x => Fn.norm2 (f x) ^ (2 : ℕ)) :=
  normSq a.toEuclidean

/-- Affine objectives have zero quadratic part. -/
@[simp] theorem ofAffine_quadratic (a : Affine.Certified f) :
    (ofAffine a).quadratic = 0 := rfl

/-- An affine objective satisfies the minimization curvature condition. -/
theorem ofAffine_nonnegative (a : Affine.Certified f) : (ofAffine a).Nonnegative :=
  fun _ => le_rfl

/-- An affine objective satisfies the maximization curvature condition. -/
theorem ofAffine_nonpositive (a : Affine.Certified f) : (ofAffine a).Nonpositive :=
  fun _ => le_rfl

/-- A squared affine scalar expression has nonnegative quadratic curvature. -/
theorem square_nonnegative (a : Affine.Certified f) : (square a).Nonnegative :=
  fun x => mul_self_nonneg (a.map.linear x)

/-- The squared norm of an affine map into a real inner product space has
nonnegative quadratic curvature. -/
theorem normSq_nonnegative {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {f : X → Y} (a : Affine.Certified f) : (normSq a).Nonnegative :=
  fun _ => real_inner_self_nonneg

/-- A squared named Euclidean norm has nonnegative quadratic curvature. -/
theorem fnNorm2Sq_nonnegative {n : Nat} {f : X → Fin n → ℝ} (a : Affine.Certified f) :
    (fnNorm2Sq a).Nonnegative := normSq_nonnegative a.toEuclidean

/-- In dimension zero, the squared norm has zero quadratic part and hence
nonpositive curvature. -/
theorem fnNorm2Sq_empty_nonpositive {f : X → Fin 0 → ℝ} (a : Affine.Certified f) :
    (fnNorm2Sq a).Nonpositive := by
  intro x
  change inner (𝕜 := ℝ) (a.toEuclidean.map.linear x) (a.toEuclidean.map.linear x) ≤ 0
  rw [Subsingleton.elim (a.toEuclidean.map.linear x) 0]
  simp

/-- Nonnegative quadratic parts remain nonnegative under addition. -/
theorem add_nonnegative (a : Certified f) (b : Certified g)
    (ha : a.Nonnegative) (hb : b.Nonnegative) : (add a b).Nonnegative :=
  fun x => add_nonneg (ha x) (hb x)

/-- Nonpositive quadratic parts remain nonpositive under addition. -/
theorem add_nonpositive (a : Certified f) (b : Certified g)
    (ha : a.Nonpositive) (hb : b.Nonpositive) : (add a b).Nonpositive :=
  fun x => add_nonpos (ha x) (hb x)

/-- Subtracting nonpositive curvature from nonnegative curvature preserves nonnegativity. -/
theorem sub_nonnegative (a : Certified f) (b : Certified g)
    (ha : a.Nonnegative) (hb : b.Nonpositive) : (sub a b).Nonnegative :=
  fun x => sub_nonneg.mpr ((hb x).trans (ha x))

/-- Subtracting nonnegative curvature from nonpositive curvature preserves nonpositivity. -/
theorem sub_nonpositive (a : Certified f) (b : Certified g)
    (ha : a.Nonpositive) (hb : b.Nonnegative) : (sub a b).Nonpositive :=
  fun x => sub_nonpos.mpr ((ha x).trans (hb x))

/-- Negation turns nonpositive curvature into nonnegative curvature. -/
theorem neg_nonnegative (a : Certified f) (ha : a.Nonpositive) : (neg a).Nonnegative :=
  fun x => neg_nonneg.mpr (ha x)

/-- Negation turns nonnegative curvature into nonpositive curvature. -/
theorem neg_nonpositive (a : Certified f) (ha : a.Nonnegative) : (neg a).Nonpositive :=
  fun x => neg_nonpos.mpr (ha x)

/-- A nonnegative coefficient preserves nonnegative quadratic curvature. -/
theorem smul_nonnegative_of_nonneg (c : ℝ) (a : Certified f)
    (hc : 0 ≤ c) (ha : a.Nonnegative) : (smul c a).Nonnegative :=
  fun x => mul_nonneg hc (ha x)

/-- A nonpositive coefficient turns nonpositive curvature into nonnegative curvature. -/
theorem smul_nonnegative_of_nonpos (c : ℝ) (a : Certified f)
    (hc : c ≤ 0) (ha : a.Nonpositive) : (smul c a).Nonnegative :=
  fun x => mul_nonneg_of_nonpos_of_nonpos hc (ha x)

/-- A nonnegative coefficient preserves nonpositive quadratic curvature. -/
theorem smul_nonpositive_of_nonneg (c : ℝ) (a : Certified f)
    (hc : 0 ≤ c) (ha : a.Nonpositive) : (smul c a).Nonpositive :=
  fun x => mul_nonpos_of_nonneg_of_nonpos hc (ha x)

/-- A nonpositive coefficient turns nonnegative curvature into nonpositive curvature. -/
theorem smul_nonpositive_of_nonpos (c : ℝ) (a : Certified f)
    (hc : c ≤ 0) (ha : a.Nonnegative) : (smul c a).Nonpositive :=
  fun x => mul_nonpos_of_nonpos_of_nonneg hc (ha x)

/-- A finite sum of nonnegative quadratic parts has nonnegative curvature. -/
theorem sum_nonnegative {ι : Type*} {f : ι → X → ℝ} (s : Finset ι)
    (a : ∀ i, Certified (f i)) (ha : ∀ i ∈ s, (a i).Nonnegative) :
    (sum s a).Nonnegative := by
  intro x
  change 0 ≤ (∑ i ∈ s, (a i).quadratic) x
  rw [sum_apply]
  exact Finset.sum_nonneg fun i hi => ha i hi x

/-- A finite sum of nonpositive quadratic parts has nonpositive curvature. -/
theorem sum_nonpositive {ι : Type*} {f : ι → X → ℝ} (s : Finset ι)
    (a : ∀ i, Certified (f i)) (ha : ∀ i ∈ s, (a i).Nonpositive) :
    (sum s a).Nonpositive := by
  intro x
  change (∑ i ∈ s, (a i).quadratic) x ≤ 0
  rw [sum_apply]
  exact Finset.sum_nonpos fun i hi => ha i hi x

end Certified

end Morew.QuadConic
