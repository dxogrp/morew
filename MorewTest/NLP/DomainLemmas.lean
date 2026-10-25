/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Basic
import Morew.NLP.Domain

/-!
# Semantic evaluation-domain regression examples

These examples exercise nested restricted functions, finite families, and
membership-sensitive sums without the expression certifier or command DSL.
The final representation keeps the objective and its sole closed-bound row.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.NLP.DomainLemmas

open Morew Morew.NLP

universe u v

noncomputable section

section GeneralDomain

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {domain : Set X} {f g : X → ℝ}

-- Every restricted native expression retains an arbitrary common domain.
-- No finite-dimensionality or openness assumption is needed here.
example (exponent : ℝ) (hf : ContDiffOn ℝ 2 f domain)
    (hg : ContDiffOn ℝ 2 g domain) (hpos : ∀ x ∈ domain, 0 < f x)
    (hne : ∀ x ∈ domain, g x ≠ 0) :
    ContDiffOn ℝ 2 (fun x => Real.log (f x) + Real.sqrt (f x) +
      (g x)⁻¹ + f x / g x + f x ^ exponent) domain :=
  Smooth.add _ _
    (Smooth.add _ _
      (Smooth.add _ _
        (Smooth.add _ _ (Domain.log f hf hpos) (Domain.sqrt f hf hpos))
        (Domain.inv g hg hne))
      (Domain.div f g hf hg hne))
    (Domain.rpow f exponent hf hpos)

example (s t : Set X) (hs : IsOpen s) (ht : IsOpen t)
    (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g t) :
    IsOpen (Domain.inter s t) ∧
      ContDiffOn ℝ 2 (fun x => f x + g x) (Domain.inter s t) :=
  ⟨Domain.inter_open s t hs ht,
    Smooth.add _ _
      (Domain.restrict f s _ hf (Domain.inter_left s t))
      (Domain.restrict g t _ hg (Domain.inter_right s t))⟩

example (feasible : X → Prop) (s t : Set X)
    (hs : ∀ x, feasible x → x ∈ s) (ht : ∀ x, feasible x → x ∈ t)
    (hpos : ∀ x, feasible x → 0 < f x) (hne : ∀ x, feasible x → g x ≠ 0) :
    ∀ x, feasible x →
      x ∈ Domain.inter (Domain.positive s f) (Domain.nonzero t g) :=
  Domain.inter_includes feasible _ _
    (Domain.positive_includes feasible s f hs hpos)
    (Domain.nonzero_includes feasible t g ht hne)

example (s : Set X) (hs : IsOpen s) (hf : ContDiffOn ℝ 2 f s) :
    IsOpen (Domain.nonzero s f) ∧
      ContDiffOn ℝ 2 (fun x => (f x)⁻¹) (Domain.nonzero s f) :=
  ⟨Domain.nonzero_open s f hs hf,
    Domain.inv f (Domain.restrict f s _ hf (Domain.nonzero_subset s f))
      (Domain.nonzero_holds s f)⟩

end GeneralDomain

private def logDomain : Set ℝ := Domain.positive Set.univ (fun x => x)

private theorem logDomain_open : IsOpen logDomain :=
  Domain.positive_open Set.univ (fun x => x) (Domain.univ_open ℝ)
    (Smooth.id Set.univ)

private theorem log_smooth : ContDiffOn ℝ 2 Real.log logDomain :=
  Domain.log (fun x => x) (Smooth.id logDomain)
    (Domain.positive_holds Set.univ (fun x => x))

private def nestedLogDomain : Set ℝ := Domain.positive logDomain Real.log

-- The second restriction uses continuity of log only on the first domain.
example : IsOpen nestedLogDomain :=
  Domain.positive_open logDomain Real.log logDomain_open log_smooth

example : ContDiffOn ℝ 2 (fun x => Real.log (Real.log x)) nestedLogDomain :=
  Domain.log Real.log
    (Domain.restrict Real.log logDomain _ log_smooth
      (Domain.positive_subset logDomain Real.log))
    (Domain.positive_holds logDomain Real.log)

example (feasible : ℝ → Prop) (hx : ∀ x, feasible x → 0 < x)
    (hlog : ∀ x, feasible x → 0 < Real.log x) :
    ∀ x, feasible x → x ∈ nestedLogDomain :=
  Domain.positive_includes feasible logDomain Real.log
    (Domain.positive_includes feasible Set.univ (fun x => x)
      (Domain.univ_includes feasible) hx) hlog

-- The ambient index type can be infinite. Only selected summands and selected
-- domains supply evidence, so no hypotheses about omitted indices are needed.
example (indices : Finset Nat) (sets : Nat → Set ℝ) (f : Nat → ℝ → ℝ)
    (hopen : ∀ i ∈ indices, IsOpen (sets i))
    (hsmooth : ∀ i ∈ indices, ContDiffOn ℝ 2 (f i) (sets i)) :
    IsOpen (Domain.bounded indices sets) ∧
      ContDiffOn ℝ 2 (fun x => ∑ i ∈ indices, f i x) (Domain.bounded indices sets) :=
  ⟨Domain.bounded_open indices sets hopen,
    Domain.sum indices f fun i hi =>
      Domain.restrict (f i) (sets i) _ (hsmooth i hi)
        (Domain.bounded_subset indices sets i hi)⟩

example (feasible : ℝ → Prop) (indices : Finset Nat) (sets : Nat → Set ℝ)
    (h : ∀ i ∈ indices, ∀ x, feasible x → x ∈ sets i) :
    ∀ x, feasible x → x ∈ Domain.bounded indices sets :=
  Domain.bounded_includes feasible indices sets h

example {ι : Type v} [Fintype ι] (sets : ι → Set ℝ)
    (hopen : ∀ i, IsOpen (sets i)) (f : ι → ℝ → ℝ)
    (hsmooth : ∀ i, ContDiffOn ℝ 2 (f i) (sets i)) :
    IsOpen (Domain.family sets) ∧
      ContDiffOn ℝ 2 (fun x i => f i x) (Domain.family sets) :=
  ⟨Domain.family_open sets hopen,
    Smooth.pi _ fun i => Domain.restrict (f i) (sets i) _ (hsmooth i)
      (Domain.family_subset sets i)⟩

example (feasible : ℝ → Prop) (sets : Fin 0 → Set ℝ) :
    IsOpen (Domain.family sets) ∧ (∀ x, feasible x → x ∈ Domain.family sets) :=
  ⟨Domain.family_open sets (fun i => Fin.elim0 i),
    Domain.family_includes feasible sets (fun i => Fin.elim0 i)⟩

example (sets : Fin 0 → Set ℝ) : Domain.family sets = Set.univ := by
  simp [Domain.family]

example (sets : Nat → Set ℝ) (f : Nat → ℝ → ℝ) :
    IsOpen (Domain.bounded ∅ sets) ∧
      ContDiffOn ℝ 2 (fun x => ∑ i ∈ (∅ : Finset Nat), f i x)
        (Domain.bounded ∅ sets) :=
  ⟨Domain.bounded_open ∅ sets (fun _ hi => False.elim (Finset.notMem_empty _ hi)),
    Domain.sum ∅ f (fun _ hi => False.elim (Finset.notMem_empty _ hi))⟩

private def lowerRow : Row ℝ logDomain where
  residual := fun x => x
  bounds := Bounds.lowerBound 1
  smooth := Smooth.id logDomain

private def logData : Data ℝ where
  sense := .minimize
  domain := logDomain
  domain_isOpen := logDomain_open
  objective := Real.log
  objective_smooth := log_smooth
  rowCount := 1
  rows := fun _ => lowerRow
  feasible_mem_domain x h := by
    have hx : 1 ≤ x := (Bounds.contains_lowerBound 1 x).mp (h 0)
    exact ⟨Set.mem_univ x, lt_of_lt_of_le zero_lt_one hx⟩

-- Domain inference is proof data; the closed-bound row stays exactly x ≥ 1.
example (x : ℝ) : logData.toProblem.feasible x ↔ 1 ≤ x := by
  simp [Data.toProblem, logData, lowerRow, Row.Holds]

example : logData.rowCount = 1 := rfl

-- The total native objective is preserved even outside the evaluation domain.
example (x : ℝ) : logData.toProblem.objective x = Real.log x := rfl

example : (-1 : ℝ) ∉ logData.domain := by
  simp [logData, logDomain, Domain.positive]

end

end MorewTest.NLP.DomainLemmas
