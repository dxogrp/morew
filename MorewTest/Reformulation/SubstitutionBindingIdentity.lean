import Morew.Reformulation

/-!
# Substitution respects lexical binding identity

Decision substitution preserves shadowing lambdas, lets, and quantifiers in
definition values, dependent annotations, objectives, and constraints.
-/

namespace MorewTest.Reformulation.SubstitutionBindingIdentity

open Morew
noncomputable section

def lambdaSource :=
  problem (x : ℝ)
    let fn := fun (x : ℝ) => x
    let identity : ∀ x : ℝ, fn x = x := fun _ => rfl
    minimize Real.log (fn x)
    subject to
      positive : 0 < x

reformulation lambdaTarget : lambdaSource := by
  substitute x := Real.exp u

example : GlobalEquivalence lambdaSource lambdaTarget := lambdaTarget.equivalence
example (u : ℝ) : lambdaTarget.objective u = u := by simp [lambdaTarget]
example (u : ℝ) : lambdaTarget.feasible u := True.intro

def letSource :=
  problem (x : ℝ)
    let offset := let x := x + 1; x
    minimize offset
    subject to
      positive : 0 < x
      universal : ∀ x : ℝ, x ≤ x
      bounded : (let x := x + 2; x) ≤ 10

reformulation letTarget : letSource := by
  substitute x := Real.exp u

example : GlobalEquivalence letSource letTarget := letTarget.equivalence
example (u : ℝ) : letTarget.objective u = Real.exp u + 1 := rfl
example (u : ℝ) : letTarget.feasible u ↔
    (∀ x : ℝ, x ≤ x) ∧ Real.exp u + 2 ≤ 10 := Iff.rfl

-- Nested binders must also survive when the model has no shared definitions.
def inlineSource :=
  problem (x : ℝ)
    minimize (let fn := fun (x : ℝ) => x; Real.log (fn x))
    subject to
      positive : 0 < x

reformulation inlineTarget : inlineSource := by
  substitute x := Real.exp u

example : GlobalEquivalence inlineSource inlineTarget := inlineTarget.equivalence
example (u : ℝ) : inlineTarget.objective u = u := by simp [inlineTarget]

-- A preexisting inner u must not capture the newly introduced decision u.
def captureSource :=
  problem (x : ℝ)
    let fn := fun (u : ℝ) => x + u
    minimize fn 1 + (fun (u : ℝ) => x + u) 2
    subject to
      positive : 0 < x

reformulation captureTarget : captureSource := by
  substitute x := Real.exp u

example : GlobalEquivalence captureSource captureTarget := captureTarget.equivalence
example (u : ℝ) : captureTarget.objective u =
    (Real.exp u + 1) + (Real.exp u + 2) := rfl

private def x : ℝ := 3
macro "capturedX" : term => `(x)

-- The decision x and the global x captured by the macro are distinct bindings.
def globalSource :=
  problem (x : ℝ)
    let offset := capturedX
    minimize x + offset

def identityCoverage : FeasibleSurjection globalSource (fun u : ℝ => u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation globalTarget : globalSource := by
  substitute x := u using identityCoverage

example : GlobalEquivalence globalSource globalTarget := globalTarget.equivalence
example (u : ℝ) : globalTarget.objective u = u + 3 := rfl

def composedSource :=
  problem (x y : ℝ)
    let fn := fun (x : ℝ) => x + y
    let offset := let y := y + 1; y
    minimize Real.log x + Real.log y + fn 1 + offset
    subject to
      positiveX : 0 < x
      positiveY : 0 < y

reformulation composedTarget : composedSource := by
  substitute x := Real.exp u
  substitute y := Real.exp v
  epigraph t

example : GlobalEquivalence composedSource composedTarget := composedTarget.equivalence
example (u v t : ℝ) : composedTarget.objective ((u, v), t) = t := rfl
example (u v t : ℝ) : composedTarget.feasible ((u, v), t) ↔
    u + v + (1 + Real.exp v) + (Real.exp v + 1) ≤ t := Iff.rfl

end
end MorewTest.Reformulation.SubstitutionBindingIdentity
