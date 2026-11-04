/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Exponential
import Morew.Rewrite.Basic

/-!
# Exact exponential-cone representations

The `Fn` functions and their defining formulas have separate representations.
Input types include the domain hypotheses; log-sum-exp requires a positive dimension.
-/

namespace Morew.Conic.Exponential

/-- The global exponential epigraph. -/
noncomputable def expEpigraph : EpigraphRepresentation Real.exp where
  Auxiliary := Unit
  target a t _ := (a, 1, t) ∈ EXP
  source_iff_exists a t := by simpa only [exists_const] using exp_le_iff a t

/-- The logarithmic hypograph on positive inputs. -/
noncomputable def logHypograph :
    HypographRepresentation (fun a : {a : ℝ // 0 < a} => Real.log a.1) where
  Auxiliary := Unit
  target a t _ := (t, 1, a.1) ∈ EXP
  source_iff_exists a t := by simpa only [exists_const] using le_log_iff a.1 t a.2

/-- The epigraph of `Fn.logSumExp` in positive dimension. -/
noncomputable def logSumExpEpigraph {n : Nat} (hn : 0 < n) :
    EpigraphRepresentation (fun v : Fin n → ℝ => Fn.logSumExp v) where
  Auxiliary := Fin n → ℝ
  target v t u := (∀ i, (v i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1
  source_iff_exists v t := logSumExp_le_iff v t hn

/-- The log-sum-exp epigraph for `Real.log (∑ i, Real.exp (v i))`. -/
noncomputable def logSumExpNativeEpigraph {n : Nat} (hn : 0 < n) :
    EpigraphRepresentation (fun v : Fin n → ℝ => Real.log (∑ i, Real.exp (v i))) :=
  logSumExpEpigraph hn

/-- The epigraph of `Fn.softplus` using two auxiliary variables. -/
noncomputable def softplusEpigraph : EpigraphRepresentation Fn.softplus where
  Auxiliary := Fin 2 → ℝ
  target a t u := (∀ i : Fin 2, (![0, a] i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1
  source_iff_exists a t := softplus_le_iff a t

/-- The softplus epigraph for `Real.log (1 + Real.exp a)`. -/
noncomputable def softplusNativeEpigraph :
    EpigraphRepresentation (fun a : ℝ => Real.log (1 + Real.exp a)) :=
  softplusEpigraph

/-- The epigraph of `Fn.relativeEntropy` for `a ≥ 0` and `b > 0`. -/
noncomputable def relativeEntropyEpigraph :
    EpigraphRepresentation (fun p : {a : ℝ // 0 ≤ a} × {b : ℝ // 0 < b} =>
      Fn.relativeEntropy p.1.1 p.2.1) where
  Auxiliary := Unit
  target p t _ := (-t, p.1.1, p.2.1) ∈ EXP
  source_iff_exists p t := by
    simpa only [exists_const] using relativeEntropy_le_iff p.1.1 p.2.1 t p.1.2 p.2.2

/-- The relative-entropy epigraph for `a * Real.log (a / b)`. -/
noncomputable def relativeEntropyNativeEpigraph :
    EpigraphRepresentation (fun p : {a : ℝ // 0 ≤ a} × {b : ℝ // 0 < b} =>
      p.1.1 * Real.log (p.1.1 / p.2.1)) :=
  relativeEntropyEpigraph

end Morew.Conic.Exponential
