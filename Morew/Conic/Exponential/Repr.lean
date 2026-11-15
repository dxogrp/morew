/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Exponential
import Morew.Rewrite.Basic

/-!
# Exact exponential-cone representations

The scalar `Fn` functions and their native forms have separate representations.
Input types include the domain hypotheses. Finite entropy and KL sums allow
dimension zero; log-sum-exp requires a positive dimension.
-/

namespace Morew.Conic.Exponential

/-- The global exponential epigraph. -/
def expEpigraph : EpigraphRepr Real.exp where
  Auxiliary := Unit
  target a t _ := (a, 1, t) ∈ EXP
  source_iff_exists a t := by simpa only [exists_const] using exp_le_iff a t

/-- The logarithmic hypograph on positive inputs. -/
def logHypograph :
    HypographRepr (fun a : {a : ℝ // 0 < a} => Real.log a.1) where
  Auxiliary := Unit
  target a t _ := (t, 1, a.1) ∈ EXP
  source_iff_exists a t := by simpa only [exists_const] using le_log_iff a.1 t a.2

/-- The epigraph of `Fn.logSumExp` in positive dimension. -/
def logSumExpEpigraph {n : Nat} (hn : 0 < n) :
    EpigraphRepr (fun v : Fin n → ℝ => Fn.logSumExp v) where
  Auxiliary := Fin n → ℝ
  target v t u := (∀ i, (v i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1
  source_iff_exists v t := logSumExp_le_iff v t hn

/-- The log-sum-exp epigraph for `Real.log (∑ i, Real.exp (v i))`. -/
def logSumExpNativeEpigraph {n : Nat} (hn : 0 < n) :
    EpigraphRepr (fun v : Fin n → ℝ => Real.log (∑ i, Real.exp (v i))) :=
  logSumExpEpigraph hn

/-- The epigraph of `Fn.softplus` using two auxiliary variables. -/
def softplusEpigraph : EpigraphRepr Fn.softplus where
  Auxiliary := Fin 2 → ℝ
  target a t u := (∀ i : Fin 2, (![0, a] i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1
  source_iff_exists a t := softplus_le_iff a t

/-- The softplus epigraph for `Real.log (1 + Real.exp a)`. -/
def softplusNativeEpigraph :
    EpigraphRepr (fun a : ℝ => Real.log (1 + Real.exp a)) :=
  softplusEpigraph

/-- The epigraph of `Fn.relEntr` for `a ≥ 0` and `b > 0`. -/
def relEntrEpigraph :
    EpigraphRepr (fun p : {a : ℝ // 0 ≤ a} × {b : ℝ // 0 < b} =>
      Fn.relEntr p.1.1 p.2.1) where
  Auxiliary := Unit
  target p t _ := (-t, p.1.1, p.2.1) ∈ EXP
  source_iff_exists p t := by
    simpa only [exists_const] using relEntr_le_iff p.1.1 p.2.1 t p.1.2 p.2.2

/-- The relative-entropy epigraph for `a * Real.log (a / b)`. -/
def relEntrNativeEpigraph :
    EpigraphRepr (fun p : {a : ℝ // 0 ≤ a} × {b : ℝ // 0 < b} =>
      p.1.1 * Real.log (p.1.1 / p.2.1)) :=
  relEntrEpigraph

/-- The entropy hypograph on nonnegative inputs. -/
def negMulLogHypograph :
    HypographRepr (fun a : {a : ℝ // 0 ≤ a} => Real.negMulLog a.1) where
  Auxiliary := Unit
  target a t _ := (t, a.1, 1) ∈ EXP
  source_iff_exists a t := by
    simpa only [exists_const] using le_negMulLog_iff a.1 t a.2

/-- The entropy atom's hypograph on nonnegative inputs. -/
def entrHypograph :
    HypographRepr (fun a : {a : ℝ // 0 ≤ a} => Fn.entr a.1) :=
  negMulLogHypograph

/-- The KL-divergence epigraph for a nonnegative first and positive second argument. -/
def klDivEpigraph :
    EpigraphRepr (fun p : {a : ℝ // 0 ≤ a} × {b : ℝ // 0 < b} =>
      Fn.klDiv p.1.1 p.2.1) where
  Auxiliary := Unit
  target p t _ := (p.2.1 - p.1.1 - t, p.1.1, p.2.1) ∈ EXP
  source_iff_exists p t := by
    simpa only [exists_const] using klDiv_le_iff p.1.1 p.2.1 t p.1.2 p.2.2

/-- The finite entropy sum hypograph on coordinatewise nonnegative inputs. -/
def sumEntrHypograph {n : Nat} :
    HypographRepr (fun x : {x : Fin n → ℝ // ∀ i, 0 ≤ x i} =>
      ∑ i, Fn.entr (x.1 i)) where
  Auxiliary := Fin n → ℝ
  target x t u := (∀ i, (u i, x.1 i, 1) ∈ EXP) ∧ t ≤ ∑ i, u i
  source_iff_exists x t := le_sum_entr_iff x.1 t x.2

/-- The finite KL sum epigraph against a fixed positive vector. -/
def sumKlDivEpigraph {n : Nat} (q : Fin n → ℝ) (hq : ∀ i, 0 < q i) :
    EpigraphRepr (fun x : {x : Fin n → ℝ // ∀ i, 0 ≤ x i} =>
      ∑ i, Fn.klDiv (x.1 i) (q i)) where
  Auxiliary := Fin n → ℝ
  target x t u := (∀ i, (q i - x.1 i - u i, x.1 i, q i) ∈ EXP) ∧ (∑ i, u i) ≤ t
  source_iff_exists x t := sum_klDiv_le_iff x.1 q t x.2 hq

end Morew.Conic.Exponential
