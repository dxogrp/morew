import PTran

/-!
# Targeted polyhedral reformulations

These surface tests exercise ordered row replacement, auxiliary decisions,
native operation spellings, user certificates, and composition with other
reformulation steps.
-/

namespace PTranTest.Reformulation.Polyhedral

open PTran
open scoped ENNReal

noncomputable section

def scalarSource :=
  problem (x t : ℝ)
    minimize x ^ 2
    subject to
      before : Real.exp x ≤ 100
      absolute : |x - 1| ≤ t
      positive : x⁺ ≤ t
      maximum : max x (1 - x) ≤ t
      minimum : -t ≤ min x (2 - x)
      after : x ≤ 10 ∧ 0 ≤ t

reformulation scalarTarget : scalarSource := by
  conic at absolute
  conic at positive
  conic at maximum
  conic at minimum

example : GlobalEquivalence scalarSource scalarTarget := scalarTarget.equivalence

example (x t : ℝ) : scalarTarget.objective (x, t) = x ^ 2 := rfl

example (x t : ℝ) : scalarTarget.feasible (x, t) ↔
    Real.exp x ≤ 100 ∧ x - 1 ≤ t ∧ -(x - 1) ≤ t ∧
      x ≤ t ∧ 0 ≤ t ∧ x ≤ t ∧ 1 - x ≤ t ∧
      -t ≤ x ∧ -t ≤ 2 - x ∧ (x ≤ 10 ∧ 0 ≤ t) := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize x ^ 2
  subject to
    before : Real.exp x ≤ 100
    absolute_conic_1 : x - 1 ≤ t
    absolute_conic_2 : -(x - 1) ≤ t
    positive_conic_1 : x ≤ t
    positive_conic_2 : 0 ≤ t
    maximum_conic_1 : x ≤ t
    maximum_conic_2 : 1 - x ≤ t
    minimum_conic_1 : -t ≤ x
    minimum_conic_2 : -t ≤ 2 - x
    after : x ≤ 10 ∧ 0 ≤ t
-/
#guard_msgs in
#printp scalarTarget

def absoluteObjective :=
  problem (x : ℝ)
    minimize |x|

reformulation defaultEpigraph : absoluteObjective := by
  epigraph t
  conic at epigraph_t

reformulation namedEpigraph : absoluteObjective := by
  epigraph t as magnitude
  conic at magnitude

example : GlobalEquivalence absoluteObjective defaultEpigraph := defaultEpigraph.equivalence
example : GlobalEquivalence absoluteObjective namedEpigraph := namedEpigraph.equivalence

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    magnitude_conic_1 : x ≤ t
    magnitude_conic_2 : -x ≤ t
-/
#guard_msgs in
#printp namedEpigraph

def minimumObjective :=
  problem (x : ℝ)
    maximize (min x (1 - x) : ℝ)

reformulation minimumHypograph : minimumObjective := by
  hypograph t
  conic at hypograph_t

example : GlobalEquivalence minimumObjective minimumHypograph := minimumHypograph.equivalence

/--
info: problem (x t : ℝ)
  maximize t
  subject to
    hypograph_t_conic_1 : t ≤ x
    hypograph_t_conic_2 : t ≤ 1 - x
-/
#guard_msgs in
#printp minimumHypograph

namespace FiniteExtrema

class IndexSet where
  indices : Finset ℕ
  nonempty : indices.Nonempty

variable [IndexSet]

def source :=
  problem (x : ℝ)
    minimize x
    subject to
      upper : IndexSet.indices.sup' IndexSet.nonempty (fun i => (i : ℝ) * x) ≤ 5
      lower : -5 ≤ IndexSet.indices.inf' IndexSet.nonempty (fun i => (i : ℝ) * x)

reformulation target : source := by
  conic at upper
  conic at lower

example : GlobalEquivalence source target := target.equivalence

end FiniteExtrema

namespace SectionParameters

class Parameter (a : outParam ℝ) where
  objective : ℝ

section

variable {a : ℝ} [Parameter a]

def source :=
  problem (x : ℝ)
    minimize (Parameter.objective (a := a))
    subject to
      cap : |x| ≤ a

reformulation lowered : source := by
  conic at cap

end

/- Saved presentation parameters must resolve in the new section. -/
section

variable {a : ℝ} [Parameter a]

reformulation continued : lowered := by
  epigraph t

example : GlobalEquivalence (lowered (a := a)) (continued (a := a)) :=
  continued.equivalence

example (x t : ℝ) : (continued (a := a)).feasible (x, t) ↔
    x ≤ a ∧ -x ≤ a ∧ Parameter.objective (a := a) ≤ t := Iff.rfl

end

end SectionParameters

namespace Norms

class Dimension where
  size : ℕ

variable [Dimension]

def source :=
  problem (v : Fin Dimension.size → ℝ) (t : ℝ)
    minimize t
    subject to
      infinity : ‖v‖ ≤ t
      explicitInfinity : ‖WithLp.toLp ∞ v‖ ≤ t
      one : ‖WithLp.toLp 1 v‖ ≤ t

reformulation target : source := by
  conic at infinity
  conic at explicitInfinity
  conic at one

example : GlobalEquivalence source target := target.equivalence

example (v u : Fin Dimension.size → ℝ) (t : ℝ) :
    target.objective ((v, t), u) = t := rfl

example (v u : Fin Dimension.size → ℝ) (t : ℝ) :
    target.feasible ((v, t), u) ↔
      (0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) ∧
        0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) ∧
        v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t) := Iff.rfl

def emptySource :=
  problem (v : Fin 0 → ℝ)
    minimize (0 : ℝ)
    subject to
      bound : ‖v‖ ≤ -1

reformulation emptyTarget : emptySource := by
  conic at bound

example : ¬ emptyTarget.HasFeasiblePoint := by
  rintro ⟨point⟩
  have h : (0 : ℝ) ≤ -1 := point.2.1
  norm_num at h

/--
info: problem (v : Fin 0 → ℝ)
  minimize 0
  subject to
    bound_conic_1 : 0 ≤ -1
    bound_conic_2 : v ≤ fun x => -1
    bound_conic_3 : -v ≤ fun x => -1
-/
#guard_msgs in
#printp emptyTarget

def emptyOneSource :=
  problem (v : Fin 0 → ℝ)
    minimize (0 : ℝ)
    subject to
      budget : ‖WithLp.toLp 1 v‖ ≤ -1

reformulation emptyOneTarget : emptyOneSource := by
  conic at budget

example : ¬ emptyOneTarget.HasFeasiblePoint := by
  rintro ⟨point⟩
  have h : (0 : ℝ) ≤ -1 := by simpa using point.2.2.2
  norm_num at h

def singleSource :=
  problem (v : Fin 1 → ℝ)
    minimize v 0
    subject to
      budget : ‖WithLp.toLp 1 v‖ ≤ 3

reformulation singleTarget : singleSource := by
  conic at budget

example : GlobalEquivalence singleSource singleTarget := singleTarget.equivalence

/--
info: problem (v budget_aux : Fin 1 → ℝ)
  minimize v 0
  subject to
    budget_conic_1 : v ≤ budget_aux
    budget_conic_2 : -v ≤ budget_aux
    budget_conic_3 : ∑ x, budget_aux x ≤ 3
-/
#guard_msgs in
#printp singleTarget

end Norms

namespace Composition

def Positive (x : ℝ) : Prop := 0 < x
def InDomain (x : ℝ) : Prop := Positive x

def source :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      grouped : x ≤ 10 ∧ 0 ≤ x
      magnitude : |x| ≤ 5
      positive : InDomain x

reformulation target : source := by
  conic at magnitude
  substitute x := Real.exp u
  epigraph t

example : GlobalEquivalence source target := target.equivalence

example (u t : ℝ) : target.objective (u, t) = t := rfl

example (u t : ℝ) : target.feasible (u, t) ↔
    (Real.exp u ≤ 10 ∧ 0 ≤ Real.exp u) ∧
      Real.exp u ≤ 5 ∧ -Real.exp u ≤ 5 ∧ u ≤ t := Iff.rfl

/--
info: problem (u t : ℝ)
  minimize t
  subject to
    grouped : Real.exp u ≤ 10 ∧ 0 ≤ Real.exp u
    magnitude_conic_1 : Real.exp u ≤ 5
    magnitude_conic_2 : -Real.exp u ≤ 5
    epigraph_t : u ≤ t
-/
#guard_msgs in
#printp target

def maximumSource :=
  problem (x : ℝ)
    maximize x
    subject to
      bound : |x| ≤ 5

reformulation maximumTarget : maximumSource := by
  conic at bound
  hypograph t as value

example : GlobalEquivalence maximumSource maximumTarget := maximumTarget.equivalence

example (x t : ℝ) : maximumTarget.feasible (x, t) ↔
    x ≤ 5 ∧ -x ≤ 5 ∧ t ≤ x := Iff.rfl

end Composition

namespace Names

def budget : ℕ := 17

def source :=
  problem (budget_aux : ℝ) (v : Fin 1 → ℝ)
    minimize budget_aux
    subject to
      budget_conic_1 : budget_aux ≤ 10
      budget : ‖WithLp.toLp 1 v‖ ≤ 3
      labels.cap : |budget_aux| ≤ 5
      «cap value» : budget_aux⁺ ≤ 2

reformulation target : source := by
  conic at budget
  conic at labels.cap
  conic at «cap value»

example : GlobalEquivalence source target := target.equivalence

/--
info: problem (budget_aux : ℝ) (v budget_aux_1 : Fin 1 → ℝ)
  minimize budget_aux
  subject to
    budget_conic_1 : budget_aux ≤ 10
    budget_conic_1_1 : v ≤ budget_aux_1
    budget_conic_2 : -v ≤ budget_aux_1
    budget_conic_3 : ∑ x, budget_aux_1 x ≤ 3
    cap_conic_1 : budget_aux ≤ 5
    cap_conic_2 : -budget_aux ≤ 5
    «cap value_conic_1» : budget_aux ≤ 2
    «cap value_conic_2» : 0 ≤ 2
-/
#guard_msgs in
#printp target

def macroSource :=
  problem (x : ℝ)
    minimize x
    subject to
      cap : |x| ≤ 1

macro "conicMacro " target:ident : command =>
  `(reformulation $target : macroSource := by
      conic at cap)

conicMacro macroTarget

example : GlobalEquivalence macroSource macroTarget := macroTarget.equivalence

end Names

namespace Custom

def userFunction (x : ℝ) : ℝ := x

def graph : GraphRepresentation userFunction where
  Auxiliary := Unit
  target x y _ := y = x
  source_iff_exists x y := by simp [userFunction]

def epiRule : EpigraphRepresentation userFunction where
  Auxiliary := Unit
  target x t _ := x ≤ t
  source_iff_exists x t := by simp [userFunction]

def hypoRule : HypographRepresentation userFunction where
  Auxiliary := Unit
  target x t _ := t ≤ x
  source_iff_exists x t := by simp [userFunction]

def exactLift : ExactConstraintLift
    (fun point : ℝ × ℝ => point.1 ≤ 5 ∧ point.2 ≤ 6) :=
  ExactConstraintLift.ofIff (fun point => point.1 ≤ 5 ∧ point.2 ≤ 6)
    (fun _ => Iff.rfl)

def source :=
  problem (x y : ℝ)
    minimize x
    subject to
      graph_row : y = userFunction x
      epigraph_row : userFunction x ≤ y
      hypograph_row : y ≤ userFunction x
      grouped : x ≤ 5 ∧ y ≤ 6

reformulation target : source := by
  conic at graph_row using graph
  conic at epigraph_row using epiRule
  conic at hypograph_row using hypoRule
  conic at grouped using exactLift

example : GlobalEquivalence source target := target.equivalence

example (x y : ℝ) : target.feasible (x, y) ↔
    y = x ∧ x ≤ y ∧ y ≤ x ∧ x ≤ 5 ∧ y ≤ 6 := Iff.rfl

/-- A local alias in a replacement row may depend on the auxiliary decision. -/
def auxiliaryAliasLift : ExactConstraintLift (fun x : ℝ => 0 ≤ x) where
  Auxiliary := ℝ
  target x u := u = x ∧ (let y := u; 0 ≤ y)
  source_iff_exists x := by simp

def auxiliaryAliasSource :=
  problem (x : ℝ)
    minimize x
    subject to
      before : x ≤ 3
      positive : 0 ≤ x
      after : x ≤ 5

reformulation auxiliaryAliasTarget : auxiliaryAliasSource := by
  conic at positive using auxiliaryAliasLift

example : GlobalEquivalence auxiliaryAliasSource auxiliaryAliasTarget :=
  auxiliaryAliasTarget.equivalence

example (x u : ℝ) : auxiliaryAliasTarget.feasible (x, u) ↔
    x ≤ 3 ∧ u = x ∧ 0 ≤ u ∧ x ≤ 5 := Iff.rfl

def trivialLift : ExactConstraintLift (fun x : ℝ => x = x) :=
  ExactConstraintLift.ofIff (fun _ => True) (fun _ => by simp)

def removableSource :=
  problem (x : ℝ)
    minimize x
    subject to
      removable : x = x
      bound : |x| ≤ 3

reformulation removableTarget : removableSource := by
  conic at removable using trivialLift
  conic at bound

example (x : ℝ) : removableTarget.feasible x ↔ x ≤ 3 ∧ -x ≤ 3 := Iff.rfl

end Custom

end

end PTranTest.Reformulation.Polyhedral
