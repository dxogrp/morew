/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Registering custom rewrite rules

`@[morew_conic]` and `@[morew_nlp]` register representations for automatic
discovery. Define representation records with `def`; a definition may carry
both attributes. The examples use an absolute-deviation epigraph, an
absolute-value graph, and a logarithm representation on positive inputs.
-/

namespace Examples.Advanced.CustomRules

open Morew
noncomputable section

def absoluteDeviation (center x : ℝ) : ℝ := |x - center|

@[morew_conic, morew_nlp]
def absoluteDeviationEpigraph (center : ℝ) :
    EpigraphRepresentation (absoluteDeviation center) where
  Auxiliary := Unit -- No auxiliary decision variable.
  target x t _ := x - center ≤ t ∧ -(x - center) ≤ t
  -- Certify the original bound iff an auxiliary satisfying the target exists.
  source_iff_exists x t := Rewrite.absEpigraph.source_iff_exists (x - center) t

def fitting (center : ℝ) :=
  problem (x t : ℝ)
    minimize t
    subject to
      deviation : absoluteDeviation center x ≤ t

section

variable (center : ℝ)

-- The attribute lets `conic at` discover the rule for this named helper and
-- infer its `center` parameter from the selected constraint.
reformulation conicRows : (fitting center) := by
  conic at deviation

/-! The bound is replaced by `x - center ≤ t` and `-(x - center) ≤ t`. -/
#printp conicRows
example : GlobalEquivalence (fitting center) (conicRows center) :=
  conicRows.equivalence center

-- Terminal commands also discover registered rules. Here `nlp` rewrites the
-- bound and certifies the complete problem, producing its NLP form.
reformulation smooth : (fitting center) := by
  nlp

#printp smooth
example : GlobalEquivalence (fitting center) (smooth center) := smooth.equivalence center
example : (smooth.nlpForm center).data.toProblem = smooth center :=
  (smooth.nlpForm center).represents
example : IsSmoothNLP (smooth center) := smooth.isSmoothNLP center

-- `using` selects a rule, including an unregistered one, and infers `center`.
-- Automatic selection requires exactly one match passing target certification.
reformulation selected : (fitting center) := by
  conic at deviation using absoluteDeviationEpigraph
  conic

example : GlobalEquivalence (fitting center) (selected center) :=
  selected.equivalence center
example : IsConic (selected center) := selected.isConic center

#printp selected

end

-- The equation y = |x| is equivalent to 0 ≤ y and y² = x².
-- Register this graph formula for smooth NLP reformulations.
@[morew_nlp]
def absoluteGraph : GraphRepresentation (fun x : ℝ => |x|) where
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

-- Negation changes the graph equation to -y = |x² - 1|. The registered
-- formula expresses this equation using smooth polynomial constraints.
reformulation signedGraphNLP : signedGraph := by nlp

#printp signedGraphNLP

example : GlobalEquivalence signedGraph signedGraphNLP := signedGraphNLP.equivalence
example : IsSmoothNLP signedGraphNLP := signedGraphNLP.isSmoothNLP

-- A subtype states the representation's domain, proved from existing constraints.
def positiveLogEpigraph :
    EpigraphRepresentation (fun x : {x : ℝ // 0 < x} => Real.log x.1) where
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

-- `positive` supplies 0 < x. The rewrite adds a real auxiliary u with
-- x = exp u and u ≤ t; the retained positivity constraint stays in place.
reformulation logarithmicNLP : logarithmicBound := by
  nlp at bound using positiveLogEpigraph
  nlp

#printp logarithmicNLP

example : GlobalEquivalence logarithmicBound logarithmicNLP := logarithmicNLP.equivalence
example : IsSmoothNLP logarithmicNLP := logarithmicNLP.isSmoothNLP

end
end Examples.Advanced.CustomRules
