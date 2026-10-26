/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Rewrite.Polyhedral.Lemmas

/-!
# Exact polyhedral representations

These target-independent records expose ordinary scalar and coordinatewise
inequalities. Their existential equivalences require no smoothness or convexity.
Finite-function norms use the infinity norm; the explicit one-norm introduces an
auxiliary vector. Every norm retains its scalar bound in dimension zero, and
finite extrema retain the supplied nonempty support.
-/

namespace Morew.Rewrite

open scoped ENNReal

/-- Exact absolute-value epigraph, with no auxiliary coordinates. -/
noncomputable def absEpigraph : EpigraphRepresentation (fun a : ℝ => |a|) where
  Auxiliary := Unit
  target a t _ := a ≤ t ∧ -a ≤ t
  source_iff_exists a t := by
    simpa only [exists_const] using Polyhedral.abs_le_iff a t

/-- Exact positive-part epigraph, retaining the nonnegative upper bound. -/
noncomputable def posEpigraph : EpigraphRepresentation (fun a : ℝ => a⁺) where
  Auxiliary := Unit
  target a t _ := a ≤ t ∧ 0 ≤ t
  source_iff_exists a t := by
    simpa only [exists_const] using Polyhedral.posPart_le_iff a t

/-- Exact binary-maximum epigraph on a pair of real operands. -/
noncomputable def maxEpigraph :
    EpigraphRepresentation (fun p : ℝ × ℝ => max p.1 p.2) where
  Auxiliary := Unit
  target p t _ := p.1 ≤ t ∧ p.2 ≤ t
  source_iff_exists p t := by
    simpa only [exists_const] using Polyhedral.max_le_iff p.1 p.2 t

/-- Exact binary-minimum hypograph on a pair of real operands. -/
noncomputable def minHypograph :
    HypographRepresentation (fun p : ℝ × ℝ => min p.1 p.2) where
  Auxiliary := Unit
  target p t _ := t ≤ p.1 ∧ t ≤ p.2
  source_iff_exists p t := by
    simpa only [exists_const] using Polyhedral.le_min_iff p.1 p.2 t

/-- Exact finite-maximum epigraph, indexed by the supplied finite support. -/
noncomputable def finsetSupEpigraph {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    EpigraphRepresentation (fun f : ι → ℝ => s.sup' hs f) where
  Auxiliary := Unit
  target f t _ := (fun j : Fin s.card => f (s.equivFin.symm j)) ≤ (fun _ => t)
  source_iff_exists f t := by
    simpa only [exists_const] using Polyhedral.sup'_le_iff s hs f t

/-- Exact finite-minimum hypograph, indexed by the supplied finite support. -/
noncomputable def finsetInfHypograph {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    HypographRepresentation (fun f : ι → ℝ => s.inf' hs f) where
  Auxiliary := Unit
  target f t _ := (fun _ : Fin s.card => t) ≤ (fun j => f (s.equivFin.symm j))
  source_iff_exists f t := by
    simpa only [exists_const] using Polyhedral.le_inf'_iff s hs f t

/-- Exact native one-norm epigraph using an auxiliary coordinatewise bound. -/
noncomputable def norm1Epigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖WithLp.toLp 1 v‖) where
  Auxiliary := Fin n → ℝ
  target v t u := v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t
  source_iff_exists v t := Polyhedral.norm_toLp_one_le_iff v t

/-- Exact infinity-norm epigraph of an ordinary finite real function. -/
noncomputable def normInfEpigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖v‖) where
  Auxiliary := Unit
  target v t _ := 0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t)
  source_iff_exists v t := by
    simpa only [exists_const] using Polyhedral.norm_le_iff v t

/-- The explicit native infinity-norm carrier has the same exact target. -/
noncomputable def normInfToLpEpigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖WithLp.toLp ∞ v‖) where
  Auxiliary := Unit
  target v t _ := 0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t)
  source_iff_exists v t := by
    simpa only [exists_const] using Polyhedral.norm_toLp_top_le_iff v t

end Morew.Rewrite
