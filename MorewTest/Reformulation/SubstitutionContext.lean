/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Substitution elaboration contexts

Substitution scripts preserve source types, arithmetic instances, and
constraints across section boundaries, instantiated parameters, and macro
expansion. Binder inference and certificate resolution respect local scopes,
and nested positivity aliases compose through successive substitutions.
Paired objective-bound steps check that substitution retains source instances.
-/

namespace MorewTest.Reformulation.SubstitutionContext

open Morew
noncomputable section

namespace ScopedConstraintInstance

structure Box where
  val : Nat

section

local instance : LE Box := ⟨fun a b => a.val ≤ b.val⟩

def source :=
  problem (x : Box)
    minimize x.val
    subject to
      bounded : x ≤ x

def automaticSource :=
  problem (box : Box) (x : ℝ)
    minimize Real.log x
    subject to
      bounded : box ≤ box
      positive : 0 < x

end

def coverage : FeasibleSurjection source (fun u : Box => u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation target : source := by
  substitute x := u using coverage
  epigraph t

example : GlobalEquivalence source target := target.equivalence

example (u : Box) (t : Nat) : target.objective (u, t) = t := rfl

example (u : Box) (t : Nat) :
    target.feasible (u, t) ↔ u.val ≤ u.val ∧ u.val ≤ t := Iff.rfl

reformulation automaticTarget : automaticSource := by
  epigraph t
  substitute x := Real.exp u

example : GlobalEquivalence automaticSource automaticTarget :=
  automaticTarget.equivalence

example (box : Box) (u t : ℝ) :
    automaticTarget.objective ((box, u), t) = t := rfl

example (box : Box) (u t : ℝ) :
    automaticTarget.feasible ((box, u), t) ↔ box.val ≤ box.val ∧ u ≤ t :=
  Iff.rfl

end ScopedConstraintInstance

namespace InstantiatedDomain

class Choice (α : outParam Type) where
  score : α → Nat

namespace Provider

def source {α : Type} [Choice α] : Problem α Nat :=
  problem (x : α)
    minimize Choice.score x

def coverage {α : Type} [Choice α] :
    FeasibleSurjection (source (α := α)) (fun u : α => u) where
  preimage point := point.1
  rightInverse _ := rfl

end Provider

section

variable {β : Type} [Choice β]

reformulation target : Provider.source := by
  substitute x := u using Provider.coverage
  epigraph t

example : GlobalEquivalence (Provider.source (α := β)) target :=
  target.equivalence

example (u : β) (t : Nat) : target.objective (u, t) = t := rfl

example (u : β) (t : Nat) :
    target.feasible (u, t) ↔ Choice.score u ≤ t := Iff.rfl

end
end InstantiatedDomain

namespace MacroGeneratedSubstitution

def source :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      positive : 0 < x

macro "contextGeneratedSubstitution " target:ident : command =>
  `(reformulation $target : source := by
      substitute x := Real.exp u)

contextGeneratedSubstitution target

example : GlobalEquivalence source target := target.equivalence

example (u : ℝ) : target.objective u = u := rfl
example (u : ℝ) : target.feasible u ↔ True := Iff.rfl

reformulation bounded : target := by
  epigraph t

example : GlobalEquivalence target bounded := bounded.equivalence

example (u t : ℝ) : bounded.objective (u, t) = t := rfl
example (u t : ℝ) : bounded.feasible (u, t) ↔ u ≤ t := Iff.rfl

end MacroGeneratedSubstitution

namespace NestedPositivityAliases

def Positive (x : ℝ) : Prop := 0 < x
def InDomain (x : ℝ) : Prop := Positive x

def source :=
  problem (x y : ℝ)
    minimize Real.log x + Real.log y
    subject to
      positive_x : InDomain x
      retained : True
      positive_y : (show Prop from InDomain y)

def coverage :
    FeasibleSurjection source
      (fun point : ℝ × ℝ => (Real.exp point.1, point.2)) where
  preimage point := (Real.log point.1.1, point.1.2)
  rightInverse point := Prod.ext (Real.exp_log point.2.1) rfl

reformulation manualTarget : source := by
  substitute x := Real.exp u using coverage
  epigraph t as sum_bound
  substitute y := Real.exp v

example : GlobalEquivalence source manualTarget := manualTarget.equivalence

example (u v t : ℝ) : manualTarget.objective ((u, v), t) = t := rfl

example (u v t : ℝ) :
    manualTarget.feasible ((u, v), t) ↔ True ∧ u + v ≤ t := Iff.rfl

reformulation automaticTarget : source := by
  substitute y := Real.exp v
  substitute x := Real.exp u
  epigraph t as sum_bound

example : GlobalEquivalence source automaticTarget :=
  automaticTarget.equivalence

example (u v t : ℝ) : automaticTarget.objective ((u, v), t) = t := rfl

example (u v t : ℝ) :
    automaticTarget.feasible ((u, v), t) ↔ True ∧ u + v ≤ t := Iff.rfl

end NestedPositivityAliases

namespace AnonymousSectionInstance

class Marker where
  marker : Nat

def Positive [Marker] (x : ℝ) : Prop := 0 < x
def InDomain [Marker] (x : ℝ) : Prop := Positive x

section

variable [Marker]

def source :=
  problem (x y : ℝ)
    minimize Real.log x + Real.log y
    subject to
      positive_x : InDomain x
      positive_y : InDomain y
      retained : True

def coverage :
    FeasibleSurjection source
      (fun point : ℝ × ℝ => (Real.exp point.1, point.2)) where
  preimage point := (Real.log point.1.1, point.1.2)
  rightInverse point := Prod.ext (Real.exp_log point.2.1) rfl

reformulation manualTarget : source := by
  substitute x := Real.exp u using coverage
  epigraph t as positive_x
  substitute y := Real.exp v

example : GlobalEquivalence source manualTarget := manualTarget.equivalence

example (u v t : ℝ) :
    manualTarget.feasible ((u, v), t) ↔ True ∧ u + v ≤ t := Iff.rfl

reformulation automaticTarget : source := by
  substitute x := Real.exp u
  epigraph t as positive_x
  substitute y := Real.exp v
  epigraph s as positive_y

example : GlobalEquivalence source automaticTarget := automaticTarget.equivalence

example (u v t s : ℝ) :
    automaticTarget.feasible (((u, v), t), s) ↔
      True ∧ u + v ≤ t ∧ t ≤ s := Iff.rfl

end
end AnonymousSectionInstance

namespace AmbientBinderType

def source :=
  problem (x : Fin (1 + 1))
    minimize x.val

def reverse (u : Fin 2) : Fin 2 := u.rev

def coverage : FeasibleSurjection source reverse where
  preimage point := point.1.rev
  rightInverse point := Fin.rev_rev point.1

local instance zeroHAdd : HAdd Nat Nat Nat where
  hAdd _ _ := 0

reformulation target : source := by
  substitute x := reverse u using coverage
  epigraph t

example : GlobalEquivalence source target := target.equivalence

example (u : Fin 2) (t : Nat) : target.objective (u, t) = t := rfl

example (u : Fin 2) (t : Nat) :
    target.feasible (u, t) ↔ (reverse u).val ≤ t := Iff.rfl

end AmbientBinderType

/-! Binder inference counts free identifiers in the elaborated replacement,
not identifiers bound inside a lambda. -/

namespace ScopedBinderInference

def source :=
  problem (x : ℝ)
    minimize x

def coverage :
    FeasibleSurjection source (fun u : ℝ => (fun z : ℝ => z) u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation target : source := by
  substitute x := (fun z : ℝ => z) u using coverage

example : GlobalEquivalence source target := target.equivalence
example (u : ℝ) : target.objective u = u := rfl

end ScopedBinderInference

/-! A checked manual witness keeps its original global resolution even when
the new target is declared under the same short name. -/

namespace CertificateNameCapture

def source :=
  problem (x : ℝ)
    minimize x

namespace Witnesses

def reused : FeasibleSurjection source (fun u : ℝ => u) where
  preimage point := point.1
  rightInverse _ := rfl

end Witnesses

open Witnesses

reformulation reused : source := by
  substitute x := u using reused

example : GlobalEquivalence source reused := reused.equivalence

end CertificateNameCapture

/-! Objective-bound construction retains source arithmetic under changed ambient instances. -/

namespace SubstitutionSourceInstances

def source :=
  problem (x : Nat)
    minimize x + 1

def identityCoverage : FeasibleSurjection source (fun u : Nat => u) where
  preimage point := point.1
  rightInverse _ := rfl

local instance zeroHAdd : HAdd Nat Nat Nat where
  hAdd _ _ := 0

example : (2 + 3 : Nat) = 0 := rfl

reformulation target : source := by
  substitute x := u using identityCoverage
  epigraph t as objective_bound

example : GlobalEquivalence source target := target.equivalence

example (u t : Nat) :
    target.feasible (u, t) ↔ Nat.add u 1 ≤ t := Iff.rfl

/--
info: problem (u t : ℕ)
  minimize t
  subject to
    objective_bound : u + 1 ≤ t
-/
#guard_msgs in
#printp target

end SubstitutionSourceInstances

namespace ObjectiveBoundSourceInstances

def source :=
  problem (x : Nat)
    minimize x + 1

local instance zeroHAdd : HAdd Nat Nat Nat where
  hAdd _ _ := 0

example : (2 + 3 : Nat) = 0 := rfl

reformulation target : source := by
  epigraph t as objective_bound

example : GlobalEquivalence source target := target.equivalence

example (x t : Nat) :
    target.feasible (x, t) ↔ Nat.add x 1 ≤ t := Iff.rfl

/--
info: problem (x t : ℕ)
  minimize t
  subject to
    objective_bound : x + 1 ≤ t
-/
#guard_msgs in
#printp target

end ObjectiveBoundSourceInstances

end
end MorewTest.Reformulation.SubstitutionContext
