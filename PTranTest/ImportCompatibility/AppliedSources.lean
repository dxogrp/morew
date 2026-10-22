import PTranTest.ImportCompatibility.AppliedSources.Defined

/-!
# Imported applied-source presentations

Imported source and generated families instantiate under changed namespaces,
and their parameterized certificates and conic artifacts remain usable.
-/

namespace PTranTest.ImportCompatibility.AppliedSources

open PTran
noncomputable section

abbrev Coordinate := Nat

def score (_ : ℝ) : ℝ := 100

def within (x bound : ℝ) : Prop := bound < x

reformulation imported : (Defined.family 3) := by
  epigraph t

example : GlobalEquivalence (Defined.family 3) imported := imported.equivalence

example (x t : ℝ) : imported.feasible (x, t) ↔
    x ≤ 3 ∧ x + 1 ≤ t := Iff.rfl

namespace ChangedInstance

local instance : HAdd Nat Nat Nat where
  hAdd _ _ := 0

example : (2 + 3 : Nat) = 0 := rfl

reformulation target : (Defined.naturalFamily 4) := by
  epigraph t

example (x t : Nat) : target.feasible (x, t) ↔ Nat.add x 4 ≤ t := Iff.rfl
example : GlobalEquivalence (Defined.naturalFamily 4) target := target.equivalence

end ChangedInstance

reformulation generated : (Defined.generated 4) := by
  epigraph s as secondBound

example : GlobalEquivalence (Defined.generated 4) generated := generated.equivalence

example (x t s : ℝ) : generated.feasible ((x, t), s) ↔
    x ≤ 4 ∧ x + 1 ≤ t ∧ t ≤ s := Iff.rfl

section

variable (shift : ℝ)

reformulation importedSubstitution : (Defined.logarithmic shift) := by
  substitute x := Real.exp u
  epigraph t

example : GlobalEquivalence (Defined.logarithmic shift) (importedSubstitution shift) :=
  importedSubstitution.equivalence shift

example (u t : ℝ) : (importedSubstitution shift).feasible (u, t) ↔
    u + shift ≤ t := Iff.rfl

end

reformulation generatedSubstitution : (Defined.substituted 5) := by
  epigraph t

example : GlobalEquivalence (Defined.substituted 5) generatedSubstitution :=
  generatedSubstitution.equivalence

example (u t : ℝ) : generatedSubstitution.feasible (u, t) ↔ u + 5 ≤ t := Iff.rfl

example : Conic.Form (Defined.terminal 6) := Defined.terminal.conicForm 6
example : IsConic (Defined.terminal 6) := Defined.terminal.isConic 6
example : GlobalEquivalence (Defined.absoluteBound 6) (Defined.terminal 6) :=
  Defined.terminal.equivalence 6

reformulation terminal : (Defined.terminal 6) := by
  hypograph t
  conic

example : GlobalEquivalence (Defined.terminal 6) terminal := terminal.equivalence
example : Conic.Form terminal := terminal.conicForm
example : IsConic terminal := terminal.isConic

run_cmd do
  let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) ``terminal
    | Lean.throwError "imported applied conic source lost its presentation"
  unless view.sense == .maximize do
    Lean.throwError "imported applied source lost its objective sense"
  unless view.constraints.map (·.name.eraseMacroScopes) ==
      #[`magnitude_conic_1, `magnitude_conic_2, `hypograph_t] do
    Lean.throwError "imported applied source changed the registered row order"

end
end PTranTest.ImportCompatibility.AppliedSources
