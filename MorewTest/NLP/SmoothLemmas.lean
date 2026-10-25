/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP

/-!
# Smooth closure rules

The semantic rules compose on arbitrary common domains and do not require
finite-dimensional decision spaces. Index sets, dimensions, and natural powers
remain symbolic, including empty finite vectors.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.NLP.SmoothLemmas

open Morew.NLP

universe u v w

noncomputable section

section GeneralDomain

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {domain : Set X} {f g : X → ℝ}

-- Both factors may depend on the decision; all elementary functions retain
-- the same domain, without assuming that it is open or inhabited.
example (m : Nat) (hf : ContDiffOn ℝ 2 f domain) (hg : ContDiffOn ℝ 2 g domain) :
    ContDiffOn ℝ 2 (fun x => Real.tanh (f x * g x) +
      Real.exp (Real.sin (f x) - Real.cos (g x)) *
        (Real.sinh (f x) + Real.cosh (g x)) ^ m) domain :=
  Smooth.add _ _
    (Smooth.tanh _ (Smooth.mul f g hf hg))
    (Smooth.mul _ _
      (Smooth.exp _ (Smooth.sub _ _ (Smooth.sin f hf) (Smooth.cos g hg)))
      (Smooth.pow _ m (Smooth.add _ _ (Smooth.sinh f hf) (Smooth.cosh g hg))))

-- A fixed value needs no analytic hypotheses about how it was computed.
example (value : ℝ) : ContDiffOn ℝ 2 (fun _ : X => |value|) domain :=
  Smooth.const domain |value|

-- Normed codomains and index families can live in other universes.
example {ι : Type v} [Fintype ι] {F : ι → Type w}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (family : X → ∀ i, F i)
    (hf : ∀ i, ContDiffOn ℝ 2 (fun x => family x i) domain) (index : ι) :
    ContDiffOn ℝ 2 (fun x => family x index) domain :=
  Smooth.component family index (Smooth.pi family hf)

end GeneralDomain

-- A supplied finite set does not require the ambient index type to be finite.
example (indices : Finset Nat) (domain : Set ℝ) :
    ContDiffOn ℝ 2 (fun x : ℝ => ∑ i ∈ indices, x ^ (i + 1)) domain :=
  Smooth.sum indices (fun i x => x ^ (i + 1))
    (fun i => Smooth.pow _ (i + 1) (Smooth.id domain))

-- Product decisions and symbolic finite-vector coordinates compose directly.
example (n : Nat) (domain : Set ((Fin n → ℝ) × ℝ)) :
    ContDiffOn ℝ 2 (fun p => ∑ i : Fin n, (p.1 i - p.2) ^ 2) domain :=
  Smooth.sum (domain := domain) Finset.univ
    (fun (i : Fin n) (p : (Fin n → ℝ) × ℝ) => (p.1 i - p.2) ^ 2) fun i =>
    Smooth.pow _ 2 (Smooth.sub _ _
      (Smooth.apply _ i (Smooth.fst _ (Smooth.id domain)))
      (Smooth.snd _ (Smooth.id domain)))

example (domain : Set (Fin 0 → ℝ)) :
    ContDiffOn ℝ 2 (fun x => ∑ i : Fin 0, Real.tanh (x i)) domain :=
  Smooth.sum (domain := domain) Finset.univ
    (fun (i : Fin 0) (x : Fin 0 → ℝ) => Real.tanh (x i)) fun i =>
    Smooth.tanh _ (Smooth.apply _ i (Smooth.id domain))

-- A product can be built first, then projected and composed with a global map.
example (domain : Set ℝ) :
    ContDiffOn ℝ 2 (fun x : ℝ => Real.exp (-x)) domain :=
  Smooth.comp Real.exp _ Real.contDiff_exp
    (Smooth.fst _ (Smooth.pair _ _
      (Smooth.neg _ (Smooth.id domain)) (Smooth.const domain (7 : ℝ))))

end

end MorewTest.NLP.SmoothLemmas
