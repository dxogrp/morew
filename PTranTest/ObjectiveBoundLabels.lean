import PTran

/-!
# Explicit epigraph and hypograph labels

These tests keep the optional presentation label separate from the semantic
epigraph and hypograph transformations.  They also exercise label hygiene,
collision handling, parser rejection, and command atomicity.
-/

namespace PTranTest.ObjectiveBoundLabels

open PTran
noncomputable section

/-! Explicit labels do not change the generated optimization problem. -/

def minimumSource :=
  problem (x : ℝ)
    minimize x ^ 2

reformulation defaultMinimum : minimumSource := by
  epigraph t

reformulation labeledMinimum : minimumSource := by
  epigraph t as objective_bound

reformulation explicitlyDefaultMinimum : minimumSource := by
  epigraph t as epigraph_t

example : GlobalEquivalence minimumSource labeledMinimum :=
  labeledMinimum.equivalence

example : defaultMinimum = labeledMinimum := rfl
example : defaultMinimum = explicitlyDefaultMinimum := rfl
example : defaultMinimum.equivalence = labeledMinimum.equivalence := rfl

example (x t : ℝ) : labeledMinimum.objective (x, t) = t := rfl

example (x t : ℝ) :
    labeledMinimum.feasible (x, t) ↔ x ^ 2 ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    objective_bound : x ^ 2 ≤ t
-/
#guard_msgs in
#printp labeledMinimum

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    epigraph_t : x ^ 2 ≤ t
-/
#guard_msgs in
#printp explicitlyDefaultMinimum

def maximumSource :=
  problem (x : ℝ)
    maximize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

reformulation defaultMaximum : maximumSource := by
  hypograph t

reformulation labeledMaximum : maximumSource := by
  hypograph t as score_bound

example : GlobalEquivalence maximumSource labeledMaximum :=
  labeledMaximum.equivalence

example : defaultMaximum = labeledMaximum := rfl
example : defaultMaximum.equivalence = labeledMaximum.equivalence := rfl

example (x t : ℝ) :
    labeledMaximum.feasible (x, t) ↔
      -1 ≤ x ∧ x ≤ 1 ∧ t ≤ x := Iff.rfl

/--
info: problem (x t : ℝ)
  maximize t
  subject to
    lower : -1 ≤ x
    upper : x ≤ 1
    score_bound : t ≤ x
-/
#guard_msgs in
#printp labeledMaximum

/-! Existing constraints and successive objective-bound labels retain order. -/

reformulation twiceBounded : minimumSource := by
  epigraph t as first_bound
  epigraph s as second_bound

example : GlobalEquivalence minimumSource twiceBounded :=
  twiceBounded.equivalence

example (x t s : ℝ) :
    twiceBounded.feasible ((x, t), s) ↔
      x ^ 2 ≤ t ∧ t ≤ s := Iff.rfl

/--
info: problem (x t s : ℝ)
  minimize s
  subject to
    first_bound : x ^ 2 ≤ t
    second_bound : t ≤ s
-/
#guard_msgs in
#printp twiceBounded

reformulation boundedAcrossDeclarations : labeledMinimum := by
  epigraph s as outer_bound

example : GlobalEquivalence labeledMinimum boundedAcrossDeclarations :=
  boundedAcrossDeclarations.equivalence

example (x t s : ℝ) :
    boundedAcrossDeclarations.feasible ((x, t), s) ↔
      x ^ 2 ≤ t ∧ t ≤ s := Iff.rfl

/--
info: problem (x t s : ℝ)
  minimize s
  subject to
    objective_bound : x ^ 2 ≤ t
    outer_bound : t ≤ s
-/
#guard_msgs in
#printp boundedAcrossDeclarations

/-! Explicit labels survive automatic and explicitly certified substitution. -/

def logarithmicSource :=
  problem (x : ℝ)
    minimize (Real.log x) ^ 2
    subject to
      positive : 0 < x

reformulation automaticSubstitution : logarithmicSource := by
  substitute x := Real.exp u
  epigraph t as logarithm_bound

example : GlobalEquivalence logarithmicSource automaticSubstitution :=
  automaticSubstitution.equivalence

example (u t : ℝ) :
    automaticSubstitution.feasible (u, t) ↔ u ^ 2 ≤ t := Iff.rfl

/--
info: problem (u t : ℝ)
  minimize t
  subject to
    logarithm_bound : u ^ 2 ≤ t
-/
#guard_msgs in
#printp automaticSubstitution

def labeledRenameCoverage :
    FeasibleSurjection labeledMinimum (fun point : ℝ × ℝ => point) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation substitutionAfterBound : labeledMinimum := by
  substitute x := u using labeledRenameCoverage

example : GlobalEquivalence labeledMinimum substitutionAfterBound :=
  substitutionAfterBound.equivalence

example (u t : ℝ) :
    substitutionAfterBound.feasible (u, t) ↔ u ^ 2 ≤ t := Iff.rfl

/--
info: problem (u t : ℝ)
  minimize t
  subject to
    objective_bound : u ^ 2 ≤ t
-/
#guard_msgs in
#printp substitutionAfterBound

namespace CanonicalSubstitutionPath

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
info: problem (u : Nat) (t : ℕ)
  minimize t
  subject to
    objective_bound : u + 1 ≤ t
-/
#guard_msgs in
#printp target

end CanonicalSubstitutionPath

namespace SemanticTargetRetry

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
info: problem (x : Nat) (t : ℕ)
  minimize t
  subject to
    objective_bound : x + 1 ≤ t
-/
#guard_msgs in
#printp target

end SemanticTargetRetry

/-! Binder names and presentation labels occupy independent namespaces. -/

reformulation sameBinderAndLabel : minimumSource := by
  epigraph t as t

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    t : x ^ 2 ≤ t
-/
#guard_msgs in
#printp sameBinderAndLabel

reformulation quotedLabel : minimumSource := by
  epigraph t as «subject»

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    «subject» : x ^ 2 ≤ t
-/
#guard_msgs in
#printp quotedLabel

namespace DeclarationNameIndependence

def objective_bound : Nat := 37

reformulation target : minimumSource := by
  epigraph t as objective_bound

example : objective_bound = 37 := rfl

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    objective_bound : x ^ 2 ≤ t
-/
#guard_msgs in
#printp target

end DeclarationNameIndependence

def qualifiedSource :=
  problem (x : ℝ)
    minimize x
    subject to
      Other.objective_bound : True

reformulation qualifiedLabel : qualifiedSource := by
  epigraph t as Bounds.objective_bound

example (x t : ℝ) :
    qualifiedLabel.feasible (x, t) ↔ True ∧ x ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    Other.objective_bound : True
    Bounds.objective_bound : x ≤ t
-/
#guard_msgs in
#printp qualifiedLabel

macro "makeLabeledMinimum " target:ident " from " source:ident : command =>
  `(reformulation $target : $source := by
      epigraph t as macro_bound)

makeLabeledMinimum macroLabeledMinimum from minimumSource

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    macro_bound : x ^ 2 ≤ t
-/
#guard_msgs in
#printp macroLabeledMinimum

/-! Explicit labels escape generated-label collisions without auto-renaming. -/

def occupiedDefaultLabel :=
  problem (x : ℝ)
    minimize x
    subject to
      epigraph_t : x ≤ x

/-- error: generated constraint name `epigraph_t` already exists; use `as <label>` to choose a different constraint label -/
#guard_msgs in
reformulation generatedCollision : occupiedDefaultLabel := by
  epigraph t

reformulation escapedGeneratedCollision : occupiedDefaultLabel := by
  epigraph t as objective_bound

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    epigraph_t : x ≤ x
    objective_bound : x ≤ t
-/
#guard_msgs in
#printp escapedGeneratedCollision

def occupiedExplicitLabel :=
  problem (x : ℝ)
    minimize x
    subject to
      objective_bound : x ≤ x

/-- error: constraint name `objective_bound` already exists -/
#guard_msgs in
reformulation explicitCollision : occupiedExplicitLabel := by
  epigraph t as objective_bound

def occupiedQualifiedLabel :=
  problem (x : ℝ)
    minimize x
    subject to
      Bounds.objective_bound : x ≤ x

/-- error: constraint name `Bounds.objective_bound` already exists -/
#guard_msgs in
reformulation qualifiedCollision : occupiedQualifiedLabel := by
  epigraph t as Bounds.objective_bound

def occupiedMacroLabel :=
  problem (x : ℝ)
    minimize x
    subject to
      macro_bound : x ≤ x

/-- error: constraint name `macro_bound` already exists -/
#guard_msgs in
makeLabeledMinimum macroCollision from occupiedMacroLabel

/-! Existing validation remains active with the optional-label syntax. -/

/-- error: decision variable `x` already exists -/
#guard_msgs in
reformulation binderCollision : minimumSource := by
  epigraph x as fresh_label

/-- error: `hypograph` is not valid for a minimization problem -/
#guard_msgs in
reformulation wrongSense : minimumSource := by
  hypograph t as fresh_label

/-! Malformed and repeated `as` clauses are parser errors, not reformulation steps. -/

run_cmd do
  let missingLabel :=
    "reformulation missingLabel : minimumSource := by\n  epigraph t as"
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command missingLabel with
  | .error _ => pure ()
  | .ok _ => Lean.throwError "an epigraph step accepted `as` without a label"

run_cmd do
  let duplicateAs :=
    "reformulation duplicateAs : minimumSource := by\n  epigraph t as first as second"
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command duplicateAs with
  | .error _ => pure ()
  | .ok _ => Lean.throwError "an epigraph step accepted a repeated `as` clause"

/-! A late label collision leaves no declarations or metadata behind. -/

/-- error: constraint name `shared` already exists -/
#guard_msgs in
reformulation atomicTarget : minimumSource certificate atomicAlias := by
  epigraph t as shared
  epigraph s as shared

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PTranTest.ObjectiveBoundLabels.atomicTarget then
    Lean.throwError "a label collision emitted the reformulation target"
  if env.contains `PTranTest.ObjectiveBoundLabels.atomicTarget.equivalence then
    Lean.throwError "a label collision emitted the canonical certificate"
  if env.contains `PTranTest.ObjectiveBoundLabels.atomicAlias then
    Lean.throwError "a label collision emitted the certificate alias"
  if (PTran.Syntax.getProblemView? env
      `PTranTest.ObjectiveBoundLabels.atomicTarget).isSome then
    Lean.throwError "a label collision emitted target presentation metadata"

reformulation atomicTarget : minimumSource certificate atomicAlias := by
  epigraph t as shared
  epigraph s as recovered

example : GlobalEquivalence minimumSource atomicTarget := atomicAlias

example (x t s : ℝ) :
    atomicTarget.feasible ((x, t), s) ↔
      x ^ 2 ≤ t ∧ t ≤ s := Iff.rfl

/--
info: problem (x t s : ℝ)
  minimize s
  subject to
    shared : x ^ 2 ≤ t
    recovered : t ≤ s
-/
#guard_msgs in
#printp atomicTarget

end
end PTranTest.ObjectiveBoundLabels
