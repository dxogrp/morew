/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Rewrite.Sum.Lemmas

/-!
# Exact finite-sum representations

Compose scalar epigraph or hypograph representations for functions on a common
input space. Each summand has a scalar bound and its own auxiliary values.
-/

namespace Morew

universe u v w

namespace EpigraphRepr

/-- Represent a finite sum using scalar upper bounds and the constituents'
auxiliary values. -/
def sum {I : Type v} [Fintype I] {X : Type u} {f : I → X → ℝ}
    (repr : ∀ i, EpigraphRepr.{u, 0, w} (f i)) :
    EpigraphRepr (fun x => ∑ i, f i x) where
  Auxiliary := (I → ℝ) × (∀ i, (repr i).Auxiliary)
  target x t a := (∀ i, (repr i).target x (a.1 i) (a.2 i)) ∧ (∑ i, a.1 i) ≤ t
  source_iff_exists x t := by
    simpa only [Prod.exists, Classical.skolem, exists_and_right] using
      Rewrite.Sum.sum_le_iff_exists (fun i => f i x)
        (fun i s => ∃ a, (repr i).target x s a)
        (fun i s => (repr i).source_iff_exists x s) t

/-- Represent a finite sum from exact scalar upper-bound predicates, using only
the vector of upper bounds as auxiliary values. -/
def sumOfIff {I : Type v} [Fintype I] {X : Type u} {f : I → X → ℝ}
    (R : I → X → ℝ → Prop) (hR : ∀ i x s, f i x ≤ s ↔ R i x s) :
    EpigraphRepr (fun x => ∑ i, f i x) where
  Auxiliary := I → ℝ
  target x t s := (∀ i, R i x (s i)) ∧ (∑ i, s i) ≤ t
  source_iff_exists x t :=
    Rewrite.Sum.sum_le_iff_exists (fun i => f i x) (fun i s => R i x s)
      (fun i s => hR i x s) t

end EpigraphRepr

namespace HypographRepr

/-- Represent a finite sum using scalar lower bounds and the constituents'
auxiliary values. -/
def sum {I : Type v} [Fintype I] {X : Type u} {f : I → X → ℝ}
    (repr : ∀ i, HypographRepr.{u, 0, w} (f i)) :
    HypographRepr (fun x => ∑ i, f i x) where
  Auxiliary := (I → ℝ) × (∀ i, (repr i).Auxiliary)
  target x t a := (∀ i, (repr i).target x (a.1 i) (a.2 i)) ∧ t ≤ (∑ i, a.1 i)
  source_iff_exists x t := by
    simpa only [Prod.exists, Classical.skolem, exists_and_right] using
      Rewrite.Sum.le_sum_iff_exists (fun i => f i x)
        (fun i s => ∃ a, (repr i).target x s a)
        (fun i s => (repr i).source_iff_exists x s) t

/-- Represent a finite sum from exact scalar lower-bound predicates, using only
the vector of lower bounds as auxiliary values. -/
def sumOfIff {I : Type v} [Fintype I] {X : Type u} {f : I → X → ℝ}
    (R : I → X → ℝ → Prop) (hR : ∀ i x s, s ≤ f i x ↔ R i x s) :
    HypographRepr (fun x => ∑ i, f i x) where
  Auxiliary := I → ℝ
  target x t s := (∀ i, R i x (s i)) ∧ t ≤ (∑ i, s i)
  source_iff_exists x t :=
    Rewrite.Sum.le_sum_iff_exists (fun i => f i x) (fun i s => R i x s)
      (fun i s => hR i x s) t

end HypographRepr

end Morew
