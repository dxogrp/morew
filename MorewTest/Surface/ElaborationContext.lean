/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Surface elaboration contexts

Exercise ambient instances, coercions, section parameters, and macro hygiene.
-/

namespace MorewTest.Surface

open Morew
noncomputable section

/-! Generated targets retain the source's inferred elaboration choices. -/

namespace AmbientInstanceResolution

def source :=
  problem (x : Nat)
    minimize x + 1

local instance zeroHAdd : HAdd Nat Nat Nat where
  hAdd _ _ := 0

example : (2 + 3 : Nat) = 0 := rfl

reformulation target : source := by
  epigraph t

example : GlobalEquivalence source target := target.equivalence

example (x t : Nat) :
    target.feasible (x, t) ↔ Nat.add x 1 ≤ t := Iff.rfl

/--
info: problem (x t : ℕ)
  minimize t
  subject to
    epigraph_t : x + 1 ≤ t
-/
#guard_msgs in
#printp target

def identityCoverage : FeasibleSurjection source (fun u : Nat => u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation substituted : source := by
  substitute x := u using identityCoverage

example (u : Nat) : substituted.objective u = Nat.add u 1 := rfl

end AmbientInstanceResolution

namespace RetainedTrueConstraint

def source :=
  problem (x : Nat)
    minimize x
    subject to
      retained : (fun _ : Nat => True) x

def identityCoverage : FeasibleSurjection source (fun u : Nat => u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation target : source := by
  substitute x := u using identityCoverage
  epigraph t

example (u t : Nat) :
    target.feasible (u, t) ↔ True ∧ u ≤ t := Iff.rfl

/--
info: problem (u t : ℕ)
  minimize t
  subject to
    retained : (fun x => True) u
    epigraph_t : u ≤ t
-/
#guard_msgs in
#printp target

end RetainedTrueConstraint

namespace SectionParameterResolution

class Score where
  score : Nat → Nat

section

variable [Score]

def source :=
  problem (x : Nat)
    minimize Score.score x

def identityCoverage : FeasibleSurjection source (fun u : Nat => u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation target : source := by
  substitute x := u using identityCoverage

example : GlobalEquivalence source target := target.equivalence

example (u : Nat) : target.objective u = Score.score u := rfl

reformulation bounded : target := by
  epigraph t

example (u t : Nat) : bounded.feasible (u, t) ↔ Score.score u ≤ t := Iff.rfl

end
end SectionParameterResolution

namespace InstantiatedValueTypeResolution

class Choice (α : outParam Type) where
  order : LinearOrder α
  value : α

set_option warn.classDefReducibility false in
attribute [instance] Choice.order

namespace Provider

def source {α : Type} [Choice α] : Problem Unit α :=
  problem (_x : Unit)
    minimize Choice.value

end Provider

namespace Consumer

section

variable {β : Type} [Choice β]

reformulation target : Provider.source := by
  epigraph t

example (t : β) : target.objective ((), t) = t := rfl

example : GlobalEquivalence Provider.source target := target.equivalence

end
end Consumer
end InstantiatedValueTypeResolution

namespace AmbientCoercionResolution

structure Box where
  value : Nat

section Source

local instance sourceCoe : Coe Box Nat where
  coe box := box.value + 1

def source :=
  problem (box : Box)
    minimize (box : Nat)

end Source

section Target

local instance targetCoe : Coe Box Nat where
  coe _ := 0

example (box : Box) : (box : Nat) = 0 := rfl

reformulation target : source := by
  epigraph t

example : GlobalEquivalence source target := target.equivalence

example (box : Box) (t : Nat) :
    target.feasible (box, t) ↔ box.value + 1 ≤ t := Iff.rfl

/--
info: problem (box : Box) (t : ℕ)
  minimize t
  subject to
    epigraph_t : box.value + 1 ≤ t
-/
#guard_msgs in
#printp target

end Target

end AmbientCoercionResolution

namespace AmbientBinderTypeResolution

def source :=
  problem (x : Fin (1 + 1))
    minimize x.val

def identityCoverage : FeasibleSurjection source (fun u : Fin 2 => u) where
  preimage point := point.1
  rightInverse _ := rfl

local instance zeroHAdd : HAdd Nat Nat Nat where
  hAdd _ _ := 0

reformulation target : source := by
  substitute x := u using identityCoverage
  epigraph t

example (u : Fin 2) (t : Nat) :
    target.feasible (u, t) ↔ u.val ≤ t := Iff.rfl

/--
info: problem (u : Fin (1 + 1)) (t : ℕ)
  minimize t
  subject to
    epigraph_t : (↑u : ℕ) ≤ t
-/
#guard_msgs in
#printp target

reformulation chained : target := by
  epigraph s

example (u : Fin 2) (t s : Nat) :
    chained.feasible ((u, t), s) ↔ u.val ≤ t ∧ t ≤ s := Iff.rfl

end AmbientBinderTypeResolution

namespace MultiBinderSubstitution

def source :=
  problem (x y : Nat)
    minimize x + y

def renameCoverage :
    FeasibleSurjection source (fun point : Nat × Nat => point) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation target : source := by
  substitute x := u using renameCoverage
  epigraph t

example (u y t : Nat) :
    target.feasible ((u, y), t) ↔ u + y ≤ t := Iff.rfl

end MultiBinderSubstitution

/-! Macro-generated problem binders remain coherent during reformulation. -/

namespace MacroGeneratedReformulation

macro "generatedProblemForReformulation" : term =>
  `(problem (x : ℝ)
      minimize x
      subject to
        reflexive : x ≤ x)

def source := generatedProblemForReformulation

reformulation target : source := by
  epigraph t

example : GlobalEquivalence source target := target.equivalence

example (x t : ℝ) :
    target.feasible (x, t) ↔ x ≤ x ∧ x ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    reflexive : x ≤ x
    epigraph_t : x ≤ t
-/
#guard_msgs in
#printp target

end MacroGeneratedReformulation

/-! Substitution variables remain free across same-spelled nested binders. -/

namespace SubstitutionBinderHygiene

def source :=
  problem (x : Nat)
    minimize (fun u : Nat => x + u) 1

def coverage : FeasibleSurjection source (fun u : Nat => u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation target : source := by
  substitute x := u using coverage

example (u : Nat) : target.objective u = u + 1 := rfl

/--
info: problem (u : ℕ)
  minimize (fun u_1 => u + u_1) 1
-/
#guard_msgs in
#printp target

local instance zeroHAdd : HAdd Nat Nat Nat where
  hAdd _ _ := 0

reformulation chained : target := by
  epigraph t

example (u t : Nat) :
    chained.feasible (u, t) ↔ Nat.add u 1 ≤ t := Iff.rfl

end SubstitutionBinderHygiene

/-! The built-in exponential rule is selected by declaration, not spelling. -/

namespace ShadowedExpLogResolution

namespace Real

def exp (x : Nat) : Nat := x
def log (x : Nat) : Nat := x

end Real

def source :=
  problem (x : Nat)
    minimize Real.log x
    subject to
      positive : 0 < x

def coverage : FeasibleSurjection source (fun u : Nat => Real.exp u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation target : source := by
  substitute x := Real.exp u using coverage

example (u : Nat) : target.objective u = u := rfl
example (u : Nat) : target.feasible u ↔ 0 < u := Iff.rfl

/--
info: problem (u : ℕ)
  minimize Real.log (Real.exp u)
  subject to
    positive : 0 < Real.exp u
-/
#guard_msgs in
#printp target

end ShadowedExpLogResolution

end
end MorewTest.Surface
