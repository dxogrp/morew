/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Matrix.Mul
import Morew.Fn.Norm

/-!
# Smooth expression closure rules

Closure rules for $C^2$ functions on domains in real normed spaces.
-/

namespace Morew.NLP.Smooth

open scoped Matrix

universe u v w z

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {Z : Type w} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {domain : Set X}

/-- A constant function is smooth on every domain. -/
theorem const (domain : Set X) (value : Y) :
    ContDiffOn ℝ 2 (fun _ : X => value) domain :=
  contDiffOn_const

/-- The decision itself is smooth on every domain. -/
theorem id (domain : Set X) : ContDiffOn ℝ 2 (fun x : X => x) domain :=
  contDiffOn_id

/-- Add two smooth functions on the same domain. -/
theorem add (f g : X → Y) (hf : ContDiffOn ℝ 2 f domain)
    (hg : ContDiffOn ℝ 2 g domain) : ContDiffOn ℝ 2 (fun x => f x + g x) domain :=
  hf.add hg

/-- Subtract two smooth functions on the same domain. -/
theorem sub (f g : X → Y) (hf : ContDiffOn ℝ 2 f domain)
    (hg : ContDiffOn ℝ 2 g domain) : ContDiffOn ℝ 2 (fun x => f x - g x) domain :=
  hf.sub hg

/-- Negate a smooth function. -/
theorem neg (f : X → Y) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => -f x) domain :=
  hf.neg

/-- Multiply two smooth real functions. -/
theorem mul (f g : X → ℝ) (hf : ContDiffOn ℝ 2 f domain)
    (hg : ContDiffOn ℝ 2 g domain) : ContDiffOn ℝ 2 (fun x => f x * g x) domain :=
  hf.mul hg

/-- A fixed natural power of a smooth real function is smooth. -/
theorem pow (f : X → ℝ) (exponent : Nat) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => f x ^ exponent) domain :=
  hf.pow exponent

/-- Sum smooth functions over the supplied fixed finite set. -/
theorem sum {ι : Type z} (indices : Finset ι) (f : ι → X → Y)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) domain) :
    ContDiffOn ℝ 2 (fun x => ∑ i ∈ indices, f i x) domain :=
  ContDiffOn.sum fun i _ => hf i

/-- Pair two smooth functions on the same domain. -/
theorem pair (f : X → Y) (g : X → Z) (hf : ContDiffOn ℝ 2 f domain)
    (hg : ContDiffOn ℝ 2 g domain) : ContDiffOn ℝ 2 (fun x => (f x, g x)) domain :=
  hf.prodMk hg

/-- Project the first component of a smooth product-valued function. -/
theorem fst (f : X → Y × Z) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => (f x).1) domain :=
  hf.fst

/-- Project the second component of a smooth product-valued function. -/
theorem snd (f : X → Y × Z) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => (f x).2) domain :=
  hf.snd

/-- View a smooth coordinate vector in Euclidean space. -/
theorem toEuclidean {n : Nat} (f : X → Fin n → ℝ)
    (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => WithLp.toLp 2 (f x)) domain :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.comp_contDiffOn hf

/-- Extract the coordinates of a smooth Euclidean vector. -/
theorem ofEuclidean {n : Nat} (f : X → EuclideanSpace ℝ (Fin n))
    (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => WithLp.ofLp (f x)) domain :=
  (EuclideanSpace.equiv (Fin n) ℝ).contDiff.comp_contDiffOn hf

/-- Build a smooth finite function from smooth components, including dependent fibers. -/
theorem pi {ι : Type z} [Fintype ι] {F : ι → Type v}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (f : X → ∀ i, F i) (hf : ∀ i, ContDiffOn ℝ 2 (fun x => f x i) domain) :
    ContDiffOn ℝ 2 f domain :=
  contDiffOn_pi' hf

/-- The squared Euclidean norm of a smooth vector is smooth, including at zero. -/
theorem norm2_sq {n : Nat} (f : X → Fin n → ℝ)
    (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => Fn.norm2 (f x) ^ 2) domain := by
  simp_rw [Fn.norm2_sq_eq_sum]
  exact ContDiffOn.sum fun i _ => (contDiffOn_pi.mp hf i).pow 2

/-- Multiply a smooth real matrix by a smooth vector on the same domain. -/
theorem mulVec {m n : Nat} (A : X → Fin m → Fin n → ℝ)
    (f : X → Fin n → ℝ) (hA : ContDiffOn ℝ 2 A domain)
    (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => A x *ᵥ f x) domain := by
  apply contDiffOn_pi'
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun j _ =>
    (contDiffOn_pi.mp (contDiffOn_pi.mp hA i) j).mul (contDiffOn_pi.mp hf j)

/-- Project a fixed component of a smooth finite dependent function. -/
theorem component {ι : Type z} [Fintype ι] {F : ι → Type v}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (f : X → ∀ i, F i) (index : ι) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => f x index) domain :=
  contDiffOn_pi.mp hf index

/-- Compose a globally smooth function with one smooth on the common domain. -/
theorem comp (g : Y → Z) (f : X → Y) (hg : ContDiff ℝ 2 g)
    (hf : ContDiffOn ℝ 2 f domain) : ContDiffOn ℝ 2 (fun x => g (f x)) domain :=
  hg.comp_contDiffOn hf

/-- The exponential of a smooth function is smooth. -/
theorem exp (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => Real.exp (f x)) domain :=
  hf.exp

/-- Sine preserves smoothness on the domain. -/
theorem sin (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => Real.sin (f x)) domain :=
  hf.sin

/-- Cosine preserves smoothness on the domain. -/
theorem cos (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => Real.cos (f x)) domain :=
  hf.cos

/-- Hyperbolic sine preserves smoothness on the domain. -/
theorem sinh (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => Real.sinh (f x)) domain :=
  hf.sinh

/-- Hyperbolic cosine preserves smoothness on the domain. -/
theorem cosh (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => Real.cosh (f x)) domain :=
  hf.cosh

/-- The real hyperbolic tangent is globally $C^2$. -/
theorem contDiff_tanh : ContDiff ℝ 2 Real.tanh := by
  have repr : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [repr]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

/-- The hyperbolic tangent of a smooth function is smooth. -/
theorem tanh (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain) :
    ContDiffOn ℝ 2 (fun x => Real.tanh (f x)) domain :=
  contDiff_tanh.comp_contDiffOn hf

end Morew.NLP.Smooth
