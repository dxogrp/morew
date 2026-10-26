/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite

/-!
# Exact scalar and finite-dimensional smooth targets

The records expose ordinary rows and retain symbolic dimensions. Empty norm
coordinates still impose a nonnegative scalar bound; finite extrema preserve
the supplied nonempty support and its enumeration.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState
assert_not_exists Morew.Conic.Cone Morew.Conic.Polyhedral.abs_le_iff

namespace MorewTest.Rewrite

open Morew
open scoped ENNReal

example (a t : ℝ) : |a| ≤ t ↔ ∃ u, Rewrite.absEpigraph.target a t u :=
  Rewrite.absEpigraph.source_iff_exists a t

example (a t : ℝ) : a⁺ ≤ t ↔ ∃ u, Rewrite.posEpigraph.target a t u :=
  Rewrite.posEpigraph.source_iff_exists a t

example (a b t : ℝ) : max a b ≤ t ↔ ∃ u, Rewrite.maxEpigraph.target (a, b) t u :=
  Rewrite.maxEpigraph.source_iff_exists (a, b) t

example (a b t : ℝ) : t ≤ min a b ↔ ∃ u, Rewrite.minHypograph.target (a, b) t u :=
  Rewrite.minHypograph.source_iff_exists (a, b) t

example (a t : ℝ) : Rewrite.absEpigraph.target a t () = (a ≤ t ∧ -a ≤ t) := rfl
example (a t : ℝ) : Rewrite.posEpigraph.target a t () = (a ≤ t ∧ 0 ≤ t) := rfl
example (a b t : ℝ) :
    Rewrite.maxEpigraph.target (a, b) t () = (a ≤ t ∧ b ≤ t) := rfl
example (a b t : ℝ) :
    Rewrite.minHypograph.target (a, b) t () = (t ≤ a ∧ t ≤ b) := rfl

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    s.sup' hs f ≤ t ↔ ∃ u, (Rewrite.finsetSupEpigraph s hs).target f t u :=
  (Rewrite.finsetSupEpigraph s hs).source_iff_exists f t

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    t ≤ s.inf' hs f ↔ ∃ u, (Rewrite.finsetInfHypograph s hs).target f t u :=
  (Rewrite.finsetInfHypograph s hs).source_iff_exists f t

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    (Rewrite.finsetSupEpigraph s hs).target f t () =
      ((fun j : Fin s.card => f (s.equivFin.symm j)) ≤ (fun _ => t)) := rfl

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    (Rewrite.finsetInfHypograph s hs).target f t () =
      ((fun _ : Fin s.card => t) ≤ (fun j => f (s.equivFin.symm j))) := rfl

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 1 v‖ ≤ t ↔ ∃ u, Rewrite.norm1Epigraph.target v t u :=
  Rewrite.norm1Epigraph.source_iff_exists v t

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖v‖ ≤ t ↔ ∃ u, Rewrite.normInfEpigraph.target v t u :=
  Rewrite.normInfEpigraph.source_iff_exists v t

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp ∞ v‖ ≤ t ↔ ∃ u, Rewrite.normInfToLpEpigraph.target v t u :=
  Rewrite.normInfToLpEpigraph.source_iff_exists v t

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ t ↔ ∃ u, Rewrite.norm2Epigraph.target v t u :=
  Rewrite.norm2Epigraph.source_iff_exists v t

example {n : Nat} (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖v‖ ≤ t ↔ ∃ u, Rewrite.euclideanNormEpigraph.target v t u :=
  Rewrite.euclideanNormEpigraph.source_iff_exists v t

example {n : Nat} (v u : Fin n → ℝ) (t : ℝ) :
    Rewrite.norm1Epigraph.target v t u = (v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t) := rfl

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    Rewrite.normInfEpigraph.target v t () =
      (0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t)) := rfl

example {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    Rewrite.norm2Epigraph.target v t () = (0 ≤ t ∧ (∑ i, v i ^ 2) ≤ t ^ 2) := rfl

example (v : Fin 0 → ℝ) (t : ℝ) :
    (∃ u, Rewrite.norm1Epigraph.target v t u) ↔ 0 ≤ t := by
  simp [Rewrite.norm1Epigraph]

example (v : Fin 0 → ℝ) (t : ℝ) :
    Rewrite.normInfEpigraph.target v t () ↔ 0 ≤ t := by
  simp [Rewrite.normInfEpigraph]

example (v : Fin 0 → ℝ) (t : ℝ) :
    Rewrite.norm2Epigraph.target v t () ↔ 0 ≤ t := by
  simp [Rewrite.norm2Epigraph, sq_nonneg]

example (v : EuclideanSpace ℝ (Fin 0)) (t : ℝ) :
    Rewrite.euclideanNormEpigraph.target v t () ↔ 0 ≤ t := by
  simp [Rewrite.euclideanNormEpigraph, sq_nonneg]

example (v : Fin 0 → ℝ) : ¬ Rewrite.norm2Epigraph.target v (-1) () := by
  change ¬ (0 ≤ (-1 : ℝ) ∧ _)
  norm_num

example (v : Fin 2 → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ t ↔ 0 ≤ t ∧ v 0 ^ 2 + v 1 ^ 2 ≤ t ^ 2 := by
  simpa [Fin.sum_univ_two] using Rewrite.norm2_le_iff v t

end MorewTest.Rewrite
