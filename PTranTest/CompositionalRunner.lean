import PTran

/-!
# Compositional reformulation runner

These end-to-end tests exercise exact reformulation steps after the runner has
already changed the semantic problem.  They intentionally use the public DSL
and generated certificates rather than the runner's internal representation.
-/

namespace PTranTest.CompositionalRunner

open PTran
noncomputable section

/-! Automatic exponential substitution composes after an objective-bound
step, for both optimization senses. -/

namespace AutomaticAfterObjectiveBound

def minimumSource :=
  problem (x : ℝ)
    minimize (Real.log x) ^ 2
    subject to
      positive : 0 < x

reformulation minimumTarget : minimumSource := by
  epigraph t as squared_log_bound
  substitute x := Real.exp u

example : GlobalEquivalence minimumSource minimumTarget :=
  minimumTarget.equivalence

example (u t : ℝ) : minimumTarget.objective (u, t) = t := rfl

example (u t : ℝ) :
    minimumTarget.feasible (u, t) ↔ u ^ 2 ≤ t :=
  Iff.rfl

def maximumSource :=
  problem (x : ℝ)
    maximize Real.log x
    subject to
      positive : 0 < x

reformulation maximumTarget : maximumSource := by
  hypograph t as logarithm_bound
  substitute x := Real.exp u

example : GlobalEquivalence maximumSource maximumTarget :=
  maximumTarget.equivalence

example (u t : ℝ) : maximumTarget.objective (u, t) = t := rfl

example (u t : ℝ) :
    maximumTarget.feasible (u, t) ↔ t ≤ u :=
  Iff.rfl

end AutomaticAfterObjectiveBound

/-! The automatic rule can replace a selected middle coordinate.  The map
assertions also ensure that coordinates on both sides of it are retained by
the generated certificate in both directions. -/

namespace MiddleCoordinate

def source :=
  problem (a x b : ℝ)
    minimize a + (Real.log x) ^ 2 + b
    subject to
      positive : 0 < x

reformulation target : source := by
  epigraph t as objective_bound
  substitute x := Real.exp u

example : GlobalEquivalence source target := target.equivalence

example (a u b t : ℝ) :
    target.objective (((a, u), b), t) = t :=
  rfl

example (a u b t : ℝ) :
    target.feasible (((a, u), b), t) ↔
      a + u ^ 2 + b ≤ t :=
  Iff.rfl

example (point : FeasiblePoint source) :
    let mapped := target.equivalence.forward.map point
    mapped.1.1.1.1 = point.1.1.1 ∧
      mapped.1.1.1.2 = Real.log point.1.1.2 ∧
      mapped.1.1.2 = point.1.2 := by
  constructor
  · rfl
  constructor <;> rfl

example (point : FeasiblePoint target) :
    let mapped := target.equivalence.backward.map point
    mapped.1.1.1 = point.1.1.1.1 ∧
      mapped.1.1.2 = Real.exp point.1.1.1.2 ∧
      mapped.1.2 = point.1.1.2 := by
  constructor
  · rfl
  constructor <;> rfl

end MiddleCoordinate

/-! An explicit coverage certificate is checked against the semantic problem
at its actual script position rather than against the original source. -/

namespace ManualAfterObjectiveBound

def source :=
  problem (x : ℝ)
    minimize x ^ 2

def epigraphIdentityCoverage :
    FeasibleSurjection source.epigraph (fun point : ℝ × ℝ => point) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation target : source := by
  epigraph t as square_bound
  substitute x := u using epigraphIdentityCoverage

example : GlobalEquivalence source target := target.equivalence

example (u t : ℝ) : target.objective (u, t) = t := rfl

example (u t : ℝ) :
    target.feasible (u, t) ↔ u ^ 2 ≤ t :=
  Iff.rfl

end ManualAfterObjectiveBound

/-! Only a constraint made tautological by the exponential rule is removed.
An explicitly presented `True` row remains, and the removed row's label is
available to a later completed step. -/

namespace TrueRemovalAndLabelReuse

def source :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      retained : True
      retained_parenthesized : (True)
      positive : 0 < x

reformulation target : source := by
  substitute x := Real.exp u
  epigraph t as positive

example : GlobalEquivalence source target := target.equivalence

example (u t : ℝ) :
    target.feasible (u, t) ↔ True ∧ True ∧ u ≤ t :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  match PTran.Syntax.getProblemView? env
      `PTranTest.CompositionalRunner.TrueRemovalAndLabelReuse.target with
  | none =>
      Lean.throwError "the reformulation target has no presentation metadata"
  | some view =>
      let visibleNames := view.constraints.map fun constraint =>
        constraint.name.eraseMacroScopes
      unless visibleNames == #[`retained, `retained_parenthesized, `positive] do
        Lean.throwError
          "expected both explicit-True rows followed by reused `positive` label, got {visibleNames}"

end TrueRemovalAndLabelReuse

/-! Typed recognition also drives rule selection and proof-backed removal when
the source uses reducible aliases or an opened spelling of `Real.exp`. -/

namespace ElaboratedRecognition

def IsPositive (x : ℝ) : Prop := 0 < x

def source :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      positive : IsPositive x

open Real in
reformulation target : source := by
  substitute x := exp u

example (u : ℝ) : target.objective u = u := rfl
example (u : ℝ) : target.feasible u ↔ True := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  let some view := PTran.Syntax.getProblemView? env
      `PTranTest.CompositionalRunner.ElaboratedRecognition.target
    | Lean.throwError "the alias-recognition target has no metadata"
  unless view.constraints.isEmpty do
    Lean.throwError "typed-equivalent positivity was not removed"

end ElaboratedRecognition

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

end
end PTranTest.CompositionalRunner
