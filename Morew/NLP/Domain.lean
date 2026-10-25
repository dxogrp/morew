/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Smooth
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Open evaluation domains for smooth nonlinear expressions

Domains combine through intersections and finite families. Positivity and
nonzero restrictions use continuity on the current domain, so nested restricted
functions need no extension to a globally continuous function. Feasibility
inclusion is separate evidence and does not alter the represented constraints.

The smoothness rules apply to arbitrary domains in real normed spaces. They
retain the native total expressions, including their values outside the domain.
-/

namespace Morew.NLP.Domain

universe u v w

variable {X : Type u} {Y : Type v} {domain : Set X}

/-- The common domain of two expressions. -/
def inter (s t : Set X) : Set X := s ∩ t

/-- Intersecting open evaluation domains preserves openness. -/
theorem inter_open [TopologicalSpace X] (s t : Set X) (hs : IsOpen s) (ht : IsOpen t) :
    IsOpen (inter s t) :=
  hs.inter ht

/-- A common domain is contained in its left operand. -/
theorem inter_left (s t : Set X) : inter s t ⊆ s :=
  Set.inter_subset_left

/-- A common domain is contained in its right operand. -/
theorem inter_right (s t : Set X) : inter s t ⊆ t :=
  Set.inter_subset_right

/-- Feasible points remain in the intersection of two containing domains. -/
theorem inter_includes (feasible : X → Prop) (s t : Set X)
    (hs : ∀ x, feasible x → x ∈ s) (ht : ∀ x, feasible x → x ∈ t) :
    ∀ x, feasible x → x ∈ inter s t :=
  fun x hx => ⟨hs x hx, ht x hx⟩

/-- The unrestricted evaluation domain is open. -/
theorem univ_open (X : Type u) [TopologicalSpace X] : IsOpen (Set.univ : Set X) :=
  isOpen_univ

/-- Every feasible point is in the unrestricted evaluation domain. -/
theorem univ_includes (feasible : X → Prop) :
    ∀ x, feasible x → x ∈ (Set.univ : Set X) :=
  fun _ _ => Set.mem_univ _

/-- Restrict smoothness to a smaller evaluation domain. -/
theorem restrict [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (s t : Set X) (hf : ContDiffOn ℝ 2 f s)
    (hst : t ⊆ s) : ContDiffOn ℝ 2 f t :=
  hf.mono hst

/-- Restrict a domain to the points where a real expression is positive. -/
def positive (s : Set X) (f : X → ℝ) : Set X := s ∩ {x | 0 < f x}

/-- Positivity defines an open restriction of the current smooth domain. -/
theorem positive_open [NormedAddCommGroup X] [NormedSpace ℝ X]
    (s : Set X) (f : X → ℝ) (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) : IsOpen (positive s f) :=
  hf.continuousOn.isOpen_inter_preimage hs isOpen_Ioi

/-- A positivity restriction is contained in its original domain. -/
theorem positive_subset (s : Set X) (f : X → ℝ) : positive s f ⊆ s :=
  Set.inter_subset_left

/-- The defining positivity condition holds throughout the restricted domain. -/
theorem positive_holds (s : Set X) (f : X → ℝ) :
    ∀ x ∈ positive s f, 0 < f x :=
  fun _ hx => hx.2

/-- Feasible positivity preserves inclusion in a restricted domain. -/
theorem positive_includes (feasible : X → Prop) (s : Set X) (f : X → ℝ)
    (hs : ∀ x, feasible x → x ∈ s) (h : ∀ x, feasible x → 0 < f x) :
    ∀ x, feasible x → x ∈ positive s f :=
  fun x hx => ⟨hs x hx, h x hx⟩

/-- Restrict a domain to the points where a real expression is nonzero. -/
def nonzero (s : Set X) (f : X → ℝ) : Set X := s ∩ {x | f x ≠ 0}

/-- A nonzero condition defines an open restriction of the current domain. -/
theorem nonzero_open [NormedAddCommGroup X] [NormedSpace ℝ X]
    (s : Set X) (f : X → ℝ) (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) : IsOpen (nonzero s f) :=
  hf.continuousOn.isOpen_inter_preimage hs isOpen_ne

/-- A nonzero restriction is contained in its original domain. -/
theorem nonzero_subset (s : Set X) (f : X → ℝ) : nonzero s f ⊆ s :=
  Set.inter_subset_left

/-- The defining nonzero condition holds throughout the restricted domain. -/
theorem nonzero_holds (s : Set X) (f : X → ℝ) :
    ∀ x ∈ nonzero s f, f x ≠ 0 :=
  fun _ hx => hx.2

/-- Feasible nonvanishing preserves inclusion in a restricted domain. -/
theorem nonzero_includes (feasible : X → Prop) (s : Set X) (f : X → ℝ)
    (hs : ∀ x, feasible x → x ∈ s) (h : ∀ x, feasible x → f x ≠ 0) :
    ∀ x, feasible x → x ∈ nonzero s f :=
  fun x hx => ⟨hs x hx, h x hx⟩

section RestrictedFunctions

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Native logarithms are smooth where their argument is positive. -/
theorem log (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain)
    (hpos : ∀ x ∈ domain, 0 < f x) :
    ContDiffOn ℝ 2 (fun x => Real.log (f x)) domain :=
  hf.log fun x hx => (hpos x hx).ne'

/-- Native square roots are smooth where their argument is positive. -/
theorem sqrt (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain)
    (hpos : ∀ x ∈ domain, 0 < f x) :
    ContDiffOn ℝ 2 (fun x => Real.sqrt (f x)) domain :=
  hf.sqrt fun x hx => (hpos x hx).ne'

/-- Native reciprocals are smooth where their argument is nonzero. -/
theorem inv (f : X → ℝ) (hf : ContDiffOn ℝ 2 f domain)
    (hne : ∀ x ∈ domain, f x ≠ 0) :
    ContDiffOn ℝ 2 (fun x => (f x)⁻¹) domain :=
  hf.inv hne

/-- Native quotients are smooth where the denominator is nonzero. -/
theorem div (f g : X → ℝ) (hf : ContDiffOn ℝ 2 f domain)
    (hg : ContDiffOn ℝ 2 g domain) (hne : ∀ x ∈ domain, g x ≠ 0) :
    ContDiffOn ℝ 2 (fun x => f x / g x) domain :=
  hf.div hg hne

/-- Fixed real powers are smooth where their base is positive. -/
theorem rpow (f : X → ℝ) (exponent : ℝ) (hf : ContDiffOn ℝ 2 f domain)
    (hpos : ∀ x ∈ domain, 0 < f x) :
    ContDiffOn ℝ 2 (fun x => f x ^ exponent) domain :=
  hf.rpow_const_of_ne fun x hx => (hpos x hx).ne'

end RestrictedFunctions

/-- The common domain of a family of expressions. -/
def family {ι : Type w} (sets : ι → Set X) : Set X := ⋂ i, sets i

/-- A finite family of open domains has an open common domain. -/
theorem family_open [TopologicalSpace X] {ι : Type w} [Fintype ι] (sets : ι → Set X)
    (h : ∀ i, IsOpen (sets i)) : IsOpen (family sets) :=
  isOpen_iInter_of_finite h

/-- A family domain is contained in each component domain. -/
theorem family_subset {ι : Type w} (sets : ι → Set X) (i : ι) :
    family sets ⊆ sets i :=
  Set.iInter_subset sets i

/-- Feasible points remain in the common domain of a containing family. -/
theorem family_includes {ι : Type w} (feasible : X → Prop) (sets : ι → Set X)
    (h : ∀ i x, feasible x → x ∈ sets i) :
    ∀ x, feasible x → x ∈ family sets :=
  fun x hx => Set.mem_iInter.mpr fun i => h i x hx

/-- The common domain of expressions indexed by a supplied finite set. -/
def bounded {ι : Type w} (indices : Finset ι) (sets : ι → Set X) : Set X :=
  ⋂ i ∈ indices, sets i

/-- Openness is needed only for the components included in the finite set. -/
theorem bounded_open [TopologicalSpace X] {ι : Type w}
    (indices : Finset ι) (sets : ι → Set X)
    (h : ∀ i ∈ indices, IsOpen (sets i)) : IsOpen (bounded indices sets) :=
  isOpen_biInter_finset h

/-- A bounded family domain is contained in each included component domain. -/
theorem bounded_subset {ι : Type w} (indices : Finset ι) (sets : ι → Set X)
    (i : ι) (hi : i ∈ indices) : bounded indices sets ⊆ sets i :=
  fun _ hx => Set.mem_iInter.mp (Set.mem_iInter.mp hx i) hi

/-- Feasible inclusion is needed only for the included component domains. -/
theorem bounded_includes {ι : Type w} (feasible : X → Prop) (indices : Finset ι)
    (sets : ι → Set X) (h : ∀ i ∈ indices, ∀ x, feasible x → x ∈ sets i) :
    ∀ x, feasible x → x ∈ bounded indices sets :=
  fun x hx => Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun hi => h i hi x hx

/-- Sum smooth functions using evidence only for included summands. -/
theorem sum [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {ι : Type w} (indices : Finset ι) (f : ι → X → Y)
    (hf : ∀ i ∈ indices, ContDiffOn ℝ 2 (f i) domain) :
    ContDiffOn ℝ 2 (fun x => ∑ i ∈ indices, f i x) domain :=
  ContDiffOn.sum hf

end Morew.NLP.Domain
