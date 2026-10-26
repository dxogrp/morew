/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Exact

/-!
# Exact scalar and finite-dimensional smooth targets

The records expose ordinary rows and retain symbolic dimensions. Empty norm
coordinates still impose a nonnegative scalar bound; finite extrema preserve
the supplied nonempty support and its enumeration.
-/

namespace MorewTest.NLP.Exact

open Morew
open scoped ENNReal

example (a t : ℝ) : |a| ≤ t ↔ ∃ u, Exact.absEpigraph.target a t u :=
  Exact.absEpigraph.source_iff_exists a t

example (a t : ℝ) : a⁺ ≤ t ↔ ∃ u, Exact.posEpigraph.target a t u :=
  Exact.posEpigraph.source_iff_exists a t

example (a b t : ℝ) : max a b ≤ t ↔ ∃ u, Exact.maxEpigraph.target (a, b) t u :=
  Exact.maxEpigraph.source_iff_exists (a, b) t

example (a b t : ℝ) : t ≤ min a b ↔ ∃ u, Exact.minHypograph.target (a, b) t u :=
  Exact.minHypograph.source_iff_exists (a, b) t

example (a t : ℝ) : Exact.absEpigraph.target a t () = (a ≤ t ∧ -a ≤ t) := rfl
example (a t : ℝ) : Exact.posEpigraph.target a t () = (a ≤ t ∧ 0 ≤ t) := rfl
example (a b t : ℝ) :
    Exact.maxEpigraph.target (a, b) t () = (a ≤ t ∧ b ≤ t) := rfl
example (a b t : ℝ) :
    Exact.minHypograph.target (a, b) t () = (t ≤ a ∧ t ≤ b) := rfl

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    s.sup' hs f ≤ t ↔ ∃ u, (Exact.finsetSupEpigraph s hs).target f t u :=
  (Exact.finsetSupEpigraph s hs).source_iff_exists f t

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    t ≤ s.inf' hs f ↔ ∃ u, (Exact.finsetInfHypograph s hs).target f t u :=
  (Exact.finsetInfHypograph s hs).source_iff_exists f t

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    (Exact.finsetSupEpigraph s hs).target f t () =
      ((fun j : Fin s.card => f (s.equivFin.symm j)) ≤ (fun _ => t)) := rfl

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    (Exact.finsetInfHypograph s hs).target f t () =
      ((fun _ : Fin s.card => t) ≤ (fun j => f (s.equivFin.symm j))) := rfl

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 1 v‖ ≤ t ↔ ∃ u, Exact.norm1Epigraph.target v t u :=
  Exact.norm1Epigraph.source_iff_exists v t

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖v‖ ≤ t ↔ ∃ u, Exact.normInfEpigraph.target v t u :=
  Exact.normInfEpigraph.source_iff_exists v t

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp ∞ v‖ ≤ t ↔ ∃ u, Exact.normInfToLpEpigraph.target v t u :=
  Exact.normInfToLpEpigraph.source_iff_exists v t

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ t ↔ ∃ u, Exact.norm2Epigraph.target v t u :=
  Exact.norm2Epigraph.source_iff_exists v t

example {n : Nat} (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖v‖ ≤ t ↔ ∃ u, Exact.euclideanNormEpigraph.target v t u :=
  Exact.euclideanNormEpigraph.source_iff_exists v t

example {n : Nat} (v u : Fin n → ℝ) (t : ℝ) :
    Exact.norm1Epigraph.target v t u = (v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t) := rfl

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    Exact.normInfEpigraph.target v t () =
      (0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t)) := rfl

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    Exact.norm2Epigraph.target v t () = (0 ≤ t ∧ (∑ i, v i ^ 2) ≤ t ^ 2) := rfl

example (v : Fin 0 → ℝ) (t : ℝ) :
    (∃ u, Exact.norm1Epigraph.target v t u) ↔ 0 ≤ t := by
  simp [Exact.norm1Epigraph]

example (v : Fin 0 → ℝ) (t : ℝ) :
    Exact.normInfEpigraph.target v t () ↔ 0 ≤ t := by
  simp [Exact.normInfEpigraph]

example (v : Fin 0 → ℝ) (t : ℝ) :
    Exact.norm2Epigraph.target v t () ↔ 0 ≤ t := by
  simp [Exact.norm2Epigraph, sq_nonneg]

example (v : EuclideanSpace ℝ (Fin 0)) (t : ℝ) :
    Exact.euclideanNormEpigraph.target v t () ↔ 0 ≤ t := by
  simp [Exact.euclideanNormEpigraph, sq_nonneg]

example (v : Fin 0 → ℝ) : ¬ Exact.norm2Epigraph.target v (-1) () := by
  change ¬ (0 ≤ (-1 : ℝ) ∧ _)
  norm_num

example (v : Fin 2 → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ t ↔ 0 ≤ t ∧ v 0 ^ 2 + v 1 ^ 2 ≤ t ^ 2 := by
  simpa [Fin.sum_univ_two] using Exact.norm2_le_iff v t

end MorewTest.NLP.Exact
