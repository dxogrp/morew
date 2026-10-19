import PTran

/-!
# Substitution elaboration contexts

Public reformulation scripts preserve source types and constraints across
section boundaries, instantiated parameters, and macro expansion. Nested
positivity aliases also compose through manual and automatic substitutions.
-/

namespace PTranTest.SubstitutionContext

open PTran
noncomputable section

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

end
end PTranTest.SubstitutionContext
