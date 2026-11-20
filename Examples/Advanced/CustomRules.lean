/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Conic
public import Morew.Reformulation.NLP

/-!
# Representation certificates and custom rules
-/

@[expose] public section

namespace Examples.Advanced.CustomRules

open Morew
noncomputable section

/-!
## Using certificates directly

The field `source_iff_exists` proves the represented mathematical formula.
For absolute value, `Auxiliary := Unit`, so the existential can be removed.
-/

example (x t : ℝ) : |x| ≤ t ↔ x ≤ t ∧ -x ≤ t := by
  simpa only [Rewrite.absEpigraph, exists_const] using
    Rewrite.absEpigraph.source_iff_exists x t

/-!
The log-sum-exp certificate uses a vector of auxiliary values. In positive
dimension, its formula is

```math
\log\sum_{i=1}^n e^{x_i}\leq t
\iff \exists u\in\mathbf{R}^n,\quad
(x_i-t,1,u_i)\in\mathrm{EXP}\ \text{for all }i,\quad
\mathbf{1}^T u\leq1.
```
-/

example {n : Nat} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    Fn.logSumExp x ≤ t ↔ ∃ u : Fin n → ℝ,
      (∀ i, (x i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 :=
  (Conic.Exponential.logSumExpEpigraph hn).source_iff_exists x t

/-!
## Registering a representation

`@[morew_conic]` and `@[morew_nlp]` register representations for automatic
selection. A representation is a `def` and may carry both attributes.
-/

def absoluteDeviation (center x : ℝ) : ℝ := |x - center|

@[morew_conic, morew_nlp]
def absoluteDeviationEpigraph (center : ℝ) :
    EpigraphRepr (absoluteDeviation center) where
  Auxiliary := Unit -- No auxiliary optimization variable.
  target x t _ := x - center ≤ t ∧ -(x - center) ≤ t
  source_iff_exists x t := Rewrite.absEpigraph.source_iff_exists (x - center) t

-- Apply the epigraph representation to a bound on the decision space `ℝ × ℝ`.
def absoluteDeviationBound (center : ℝ) :
    ConstraintRepr (fun p : ℝ × ℝ => absoluteDeviation center p.1 ≤ p.2) :=
  (absoluteDeviationEpigraph center).toConstraintRepr Prod.fst Prod.snd

def fitting (center : ℝ) :=
  problem (x t : ℝ)
    minimize t
    subject to
      deviation : absoluteDeviation center x ≤ t

section

variable (center : ℝ)

-- `conic at` selects the registered rule and infers `center`.
reformulation conicRows : (fitting center) := by
  conic at deviation

/-! The bound is replaced by `x - center ≤ t` and `-(x - center) ≤ t`. -/
#printp conicRows
example : GlobalEquiv (fitting center) (conicRows center) :=
  conicRows.equiv center

-- `nlp` applies the registered rule and certifies smoothness.
reformulation smooth : (fitting center) := by
  nlp

#printp smooth
example : GlobalEquiv (fitting center) (smooth center) := smooth.equiv center
example : (smooth.nlpForm center).data.toProblem = smooth center :=
  (smooth.nlpForm center).represents
example : IsSmoothNLP (smooth center) := smooth.isSmoothNLP center

-- `using` selects the unregistered constraint representation and infers `center`.
reformulation selected : (fitting center) := by
  conic at deviation using absoluteDeviationBound
  conic

example : GlobalEquiv (fitting center) (selected center) :=
  selected.equiv center
example : IsConic (selected center) := selected.isConic center
example : (selected.conicForm center).data.toProblem = selected center :=
  (selected.conicForm center).represents
example (x t : ℝ) : (selected center).feasible (x, t) ↔
    x - center ≤ t ∧ -(x - center) ≤ t := by
  change (0 ≤ t - (x - center) ∧ 0 ≤ t + (x - center)) ↔ _
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

#printp selected

end

-- The equation `y = |x|` is equivalent to `0 ≤ y` and `y² = x²`.
-- Register this graph formula for smooth NLP reformulations.
@[morew_nlp]
def absoluteGraph : GraphRepr (fun x : ℝ => |x|) where
  Auxiliary := Unit
  target x y _ := 0 ≤ y ∧ y ^ 2 = x ^ 2
  source_iff_exists x y := by
    simp only [exists_const]
    constructor
    · rintro rfl
      exact ⟨abs_nonneg x, sq_abs x⟩
    · rintro ⟨hy, hsq⟩
      simpa only [abs_of_nonneg hy] using (sq_eq_sq_iff_abs_eq_abs y x).mp hsq

def signedGraph :=
  problem (x y : ℝ)
    minimize y
    subject to graph : y = -|x ^ 2 - 1|

-- Negation changes the graph equation to `-y = |x² - 1|`. The registered
-- formula expresses this equation using smooth polynomial constraints.
reformulation signedGraphNLP : signedGraph := by nlp

#printp signedGraphNLP

example : GlobalEquiv signedGraph signedGraphNLP := signedGraphNLP.equiv
example : IsSmoothNLP signedGraphNLP := signedGraphNLP.isSmoothNLP

-- A subtype states the representation's domain, proved from existing constraints.
def positiveLogEpigraph :
    EpigraphRepr (fun x : {x : ℝ // 0 < x} => Real.log x.1) where
  Auxiliary := ℝ
  target x t u := x.1 = Real.exp u ∧ u ≤ t
  source_iff_exists x t := by
    constructor
    · intro h
      exact ⟨Real.log x.1, (Real.exp_log x.2).symm, h⟩
    · rintro ⟨u, hx, hu⟩
      simpa only [hx, Real.log_exp] using hu

def logarithmicBound :=
  problem (x t : ℝ)
    minimize t
    subject to
      positive : 1 ≤ x
      bound : Real.log x ≤ t

-- `positive` supplies `0 < x`; the rewrite adds `x = exp u` and `u ≤ t`.
reformulation logarithmicNLP : logarithmicBound := by
  nlp at bound using positiveLogEpigraph
  nlp

#printp logarithmicNLP

example : GlobalEquiv logarithmicBound logarithmicNLP := logarithmicNLP.equiv
example : IsSmoothNLP logarithmicNLP := logarithmicNLP.isSmoothNLP

end
end Examples.Advanced.CustomRules
