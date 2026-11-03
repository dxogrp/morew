/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Rewrite.Polyhedral.Lemmas
import Morew.Fn.Norm

/-!
# Exact polyhedral representations

Scalar and coordinatewise representations of absolute values, extrema, and
vector norms. The norm of a finite real function is its infinity norm; the
one-norm representation introduces an auxiliary vector. Norm bounds include
dimension zero; finite extrema use a nonempty support.
-/

namespace Morew.Rewrite

open scoped ENNReal

/-- The absolute-value epigraph as two inequalities. -/
noncomputable def absEpigraph : EpigraphRepresentation (fun a : ℝ => |a|) where
  Auxiliary := Unit
  target a t _ := a ≤ t ∧ -a ≤ t
  source_iff_exists a t := by
    simpa only [exists_const] using Polyhedral.abs_le_iff a t

/-- The positive-part epigraph, including nonnegativity of the bound. -/
noncomputable def posEpigraph : EpigraphRepresentation (fun a : ℝ => a⁺) where
  Auxiliary := Unit
  target a t _ := a ≤ t ∧ 0 ≤ t
  source_iff_exists a t := by
    simpa only [exists_const] using Polyhedral.posPart_le_iff a t

/-- The epigraph of the maximum of two real values. -/
noncomputable def maxEpigraph :
    EpigraphRepresentation (fun p : ℝ × ℝ => max p.1 p.2) where
  Auxiliary := Unit
  target p t _ := p.1 ≤ t ∧ p.2 ≤ t
  source_iff_exists p t := by
    simpa only [exists_const] using Polyhedral.max_le_iff p.1 p.2 t

/-- The hypograph of the minimum of two real values. -/
noncomputable def minHypograph :
    HypographRepresentation (fun p : ℝ × ℝ => min p.1 p.2) where
  Auxiliary := Unit
  target p t _ := t ≤ p.1 ∧ t ≤ p.2
  source_iff_exists p t := by
    simpa only [exists_const] using Polyhedral.le_min_iff p.1 p.2 t

/-- The epigraph of a maximum over a nonempty finite support. -/
noncomputable def finsetSupEpigraph {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    EpigraphRepresentation (fun f : ι → ℝ => s.sup' hs f) where
  Auxiliary := Unit
  target f t _ := (fun j : Fin s.card => f (s.equivFin.symm j)) ≤ (fun _ => t)
  source_iff_exists f t := by
    simpa only [exists_const] using Polyhedral.sup'_le_iff s hs f t

/-- The hypograph of a minimum over a nonempty finite support. -/
noncomputable def finsetInfHypograph {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    HypographRepresentation (fun f : ι → ℝ => s.inf' hs f) where
  Auxiliary := Unit
  target f t _ := (fun _ : Fin s.card => t) ≤ (fun j => f (s.equivFin.symm j))
  source_iff_exists f t := by
    simpa only [exists_const] using Polyhedral.le_inf'_iff s hs f t

/-- The one-norm epigraph using an auxiliary coordinatewise bound. -/
noncomputable def norm1Epigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖WithLp.toLp 1 v‖) where
  Auxiliary := Fin n → ℝ
  target v t u := v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t
  source_iff_exists v t := Polyhedral.norm_toLp_one_le_iff v t

/-- The infinity-norm epigraph of a finite real function. -/
noncomputable def normInfEpigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖v‖) where
  Auxiliary := Unit
  target v t _ := 0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t)
  source_iff_exists v t := by
    simpa only [exists_const] using Polyhedral.norm_le_iff v t

/-- The `WithLp ∞` norm has the same epigraph inequalities. -/
noncomputable def normInfToLpEpigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖WithLp.toLp ∞ v‖) where
  Auxiliary := Unit
  target v t _ := 0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t)
  source_iff_exists v t := by
    simpa only [exists_const] using Polyhedral.norm_toLp_top_le_iff v t

/-- The named one-norm uses the same auxiliary vector as the native one-norm. -/
noncomputable def fnNorm1Epigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => Fn.norm1 v) :=
  norm1Epigraph

/-- The named infinity norm retains its scalar bound, including for empty vectors. -/
noncomputable def fnNormInfEpigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => Fn.normInf v) :=
  normInfEpigraph

end Morew.Rewrite
