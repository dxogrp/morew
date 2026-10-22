import PTran

/-!
# Explicitly applied reformulation sources

Applications instantiate semantic problems and their presentations together.
Generated families retain their actual parameters across section boundaries.
-/

namespace PTranTest.Surface.AppliedSources

open PTran
noncomputable section

def quadratic (a : ℝ) :=
  problem (x : ℝ)
    minimize (x - a) ^ 2
    subject to
      lower : a ≤ x

reformulation concrete : (quadratic 3) certificate concreteEquivalence := by
  epigraph t as objectiveBound

example : GlobalEquivalence (quadratic 3) concrete := concrete.equivalence
example : GlobalEquivalence (quadratic 3) concrete := concreteEquivalence

example (x t : ℝ) : concrete.feasible (x, t) ↔
    3 ≤ x ∧ (x - 3) ^ 2 ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    lower : 3 ≤ x
    objectiveBound : (x - 3) ^ 2 ≤ t
-/
#guard_msgs in
#printp concrete

reformulation named : (quadratic (a := 4)) := by
  epigraph t

example : GlobalEquivalence (quadratic 4) named := named.equivalence

reformulation explicitlyApplied : (@quadratic 5) := by
  epigraph t

example : GlobalEquivalence (quadratic 5) explicitlyApplied :=
  explicitlyApplied.equivalence

reformulation nestedParens : ((quadratic 6)) := by
  epigraph t

example : GlobalEquivalence (quadratic 6) nestedParens := nestedParens.equivalence

reformulation expressionArgument : (quadratic (2 + 1)) := by
  epigraph t

example (x t : ℝ) : expressionArgument.feasible (x, t) ↔
    2 + 1 ≤ x ∧ (x - (2 + 1)) ^ 2 ≤ t := Iff.rfl

namespace GlobalArgument

def x : ℝ := 12

reformulation target : (quadratic x) := by
  epigraph t

example (u t : ℝ) : target.feasible (u, t) ↔
    x ≤ u ∧ (u - x) ^ 2 ≤ t := Iff.rfl

end GlobalArgument

section

variable (coefficient : ℝ)

reformulation parameterized : (quadratic coefficient)
    certificate parameterizedEquivalence := by
  epigraph t as objectiveBound

example : GlobalEquivalence (quadratic coefficient) (parameterized coefficient) :=
  parameterized.equivalence coefficient

example : GlobalEquivalence (quadratic coefficient) (parameterized coefficient) :=
  parameterizedEquivalence coefficient

end

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    lower : coefficient ≤ x
    objectiveBound : (x - coefficient) ^ 2 ≤ t
-/
#guard_msgs in
#printp parameterized

reformulation chained : (parameterized 7) := by
  epigraph s as secondBound

example : GlobalEquivalence (parameterized 7) chained := chained.equivalence

example (x t s : ℝ) : chained.feasible ((x, t), s) ↔
    7 ≤ x ∧ (x - 7) ^ 2 ≤ t ∧ t ≤ s := Iff.rfl

section

variable (lower : ℝ)

-- Constraint labels do not bind expression variables.
reformulation parameterNamedLikeLabel : (quadratic lower) := by
  epigraph t

example (x t : ℝ) : (parameterNamedLikeLabel lower).feasible (x, t) ↔
    lower ≤ x ∧ (x - lower) ^ 2 ≤ t := Iff.rfl

end

section

variable (x coefficient : ℝ)

-- Only dependencies of the applied source reserve parameter names.
reformulation unusedOuterName : (quadratic coefficient) := by
  epigraph t

example : GlobalEquivalence (quadratic coefficient) (unusedOuterName coefficient) :=
  unusedOuterName.equivalence coefficient

end

def vectors {n : Nat} (bound : ℝ) :=
  problem (v w : Fin n → ℝ)
    minimize (0 : ℝ)
    subject to
      grouped : (∀ i, v i ≤ bound) ∧ (∀ i, w i ≤ bound)
      retained : True

reformulation concreteVectors : (vectors (n := 2) 3) := by
  epigraph t

example : Problem (((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ℝ) ℝ := concreteVectors

example (v w : Fin 2 → ℝ) (t : ℝ) : concreteVectors.feasible ((v, w), t) ↔
    ((∀ i, v i ≤ 3) ∧ (∀ i, w i ≤ 3)) ∧ True ∧ 0 ≤ t := Iff.rfl

run_cmd do
  let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) ``concreteVectors
    | Lean.throwError "applied vector source lost its presentation"
  unless view.binders.map (·.name.eraseMacroScopes) == #[`v, `w, `t] do
    Lean.throwError "applied vector source changed binder names or order"
  unless view.constraints.map (·.name.eraseMacroScopes) == #[`grouped, `retained, `epigraph_t] do
    Lean.throwError "applied vector source split or dropped a named row"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `copiedVectors
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (v w : Fin 2 → ℝ) (t : ℝ) : copiedVectors.feasible ((v, w), t) ↔
    ((∀ i, v i ≤ 3) ∧ (∀ i, w i ≤ 3)) ∧ True ∧ 0 ≤ t := Iff.rfl

reformulation explicitVectors : (@vectors 2 3) := by
  epigraph t

example : GlobalEquivalence (@vectors 2 3) explicitVectors := explicitVectors.equivalence

section

variable (size : Nat) (bound : ℝ)

reformulation symbolicVectors : (vectors (n := size) bound) := by
  epigraph t

end

reformulation generatedVectors : (symbolicVectors 2 4) := by
  epigraph s

example (v w : Fin 2 → ℝ) (t s : ℝ) : generatedVectors.feasible (((v, w), t), s) ↔
    ((∀ i, v i ≤ 4) ∧ (∀ i, w i ≤ 4)) ∧ True ∧ 0 ≤ t ∧ t ≤ s := Iff.rfl

namespace InstanceApplications

class Weight where
  coefficient : ℝ

abbrev originalWeight : Weight := ⟨2⟩
abbrev changedWeight : Weight := ⟨7⟩

def weighted [Weight] (offset : ℝ) :=
  problem (x : ℝ)
    minimize Weight.coefficient * x + offset

local instance : Weight := changedWeight

reformulation explicitInstance : (@weighted originalWeight 3) := by
  epigraph t

example : GlobalEquivalence (@weighted originalWeight 3) explicitInstance :=
  explicitInstance.equivalence

example (x t : ℝ) : explicitInstance.feasible (x, t) ↔ 2 * x + 3 ≤ t := Iff.rfl

reformulation implicitInstance : (weighted 3) := by
  epigraph t

example (x t : ℝ) : implicitInstance.feasible (x, t) ↔ 7 * x + 3 ≤ t := Iff.rfl

end InstanceApplications

def maximum (bound : ℝ) :=
  problem (x : ℝ)
    maximize x
    subject to
      upper : x ≤ bound

reformulation maximumBound : (maximum 8) := by
  hypograph t

example : GlobalEquivalence (maximum 8) maximumBound := maximumBound.equivalence

example (x t : ℝ) : maximumBound.feasible (x, t) ↔ x ≤ 8 ∧ t ≤ x := Iff.rfl

/--
info: problem (x t : ℝ)
  maximize t
  subject to
    upper : x ≤ 8
    hypograph_t : t ≤ x
-/
#guard_msgs in
#printp maximumBound

/-! The declared value type may itself carry order information beyond the sense. -/

namespace ObjectiveValueOrders

def minimum (a : Nat) : Problem Nat (OrderDual Nat) :=
  problem (x : Nat)
    minimize OrderDual.toDual (x + a)

reformulation minimumTarget : (minimum 3) := by
  epigraph t

example : Problem (Nat × OrderDual Nat) (OrderDual Nat) := minimumTarget
example : GlobalEquivalence (minimum 3) minimumTarget := minimumTarget.equivalence

-- These comparisons infer their order from the emitted target itself.
example : ¬ minimumTarget.objective (0, 0) ≤ minimumTarget.objective (0, 1) := by decide

def maximum (a : Nat) : Problem Nat (OrderDual (OrderDual Nat)) :=
  problem (x : Nat)
    maximize OrderDual.toDual (x + a)

reformulation maximumTarget : (maximum 3) := by
  hypograph t

example : Problem (Nat × OrderDual Nat) (OrderDual (OrderDual Nat)) := maximumTarget
example : GlobalEquivalence (maximum 3) maximumTarget := maximumTarget.equivalence

example : maximumTarget.objective (0, 0) ≤ maximumTarget.objective (0, 1) := by decide

end ObjectiveValueOrders

def logarithmic (offset : ℝ) :=
  problem (x : ℝ)
    minimize Real.log x + offset
    subject to
      positive : 0 < x

section

variable (offset : ℝ)

reformulation substituted : (logarithmic offset) := by
  substitute x := Real.exp u
  epigraph t

example : GlobalEquivalence (logarithmic offset) (substituted offset) :=
  substituted.equivalence offset

example (u t : ℝ) : (substituted offset).feasible (u, t) ↔ u + offset ≤ t := Iff.rfl

end

reformulation substitutedAgain : (substituted 2) := by
  epigraph s

example (u t s : ℝ) : substitutedAgain.feasible ((u, t), s) ↔
    u + 2 ≤ t ∧ t ≤ s := Iff.rfl

def absoluteBound (bound : ℝ) :=
  problem (x : ℝ)
    minimize x
    subject to
      magnitude : |x| ≤ bound

reformulation targeted : (absoluteBound 9) := by
  conic at magnitude

example : GlobalEquivalence (absoluteBound 9) targeted := targeted.equivalence

example (x : ℝ) : targeted.feasible x ↔ x ≤ 9 ∧ -x ≤ 9 := Iff.rfl

section

variable (bound : ℝ)

reformulation terminal : (absoluteBound bound) certificate terminalEquivalence := by
  conic

example : GlobalEquivalence (absoluteBound bound) (terminal bound) :=
  terminal.equivalence bound
example : GlobalEquivalence (absoluteBound bound) (terminal bound) :=
  terminalEquivalence bound
example : Conic.Form (terminal bound) := terminal.conicForm bound
example : IsConic (terminal bound) := terminal.isConic bound

end

reformulation terminalAgain : (terminal 10) := by
  epigraph t
  conic

example : GlobalEquivalence (terminal 10) terminalAgain := terminalAgain.equivalence
example : Conic.Form terminalAgain := terminalAgain.conicForm
example : IsConic terminalAgain := terminalAgain.isConic

/-! Applications require their own parentheses; the bare identifier form remains. -/

run_cmd do
  let unparenthesized :=
    "reformulation rejected : quadratic 3 := by\n  epigraph t"
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command unparenthesized with
  | .error _ => pure ()
  | .ok _ => Lean.throwError "unparenthesized applied source was accepted"

/-! Invalid sources and collisions leave no target, artifacts, or metadata. -/

/-- error: term does not have type `PTran.Problem _ _` -/
#guard_msgs in
reformulation bareFamily : quadratic := by
  epigraph t

def twoParameters (a b : ℝ) :=
  problem (x : ℝ)
    minimize x + a + b

/-- error: term does not have type `PTran.Problem _ _` -/
#guard_msgs in
reformulation partialApplication : (twoParameters 3) := by
  epigraph t

/-- error: reformulation source contains unresolved metavariables -/
#guard_msgs in
reformulation unresolvedArgument : (quadratic _) := by
  epigraph t

def unregistered (a : ℝ) : Problem ℝ ℝ :=
  ⟨fun x => x + a, fun _ => True⟩

/-- error: declaration `PTranTest.Surface.AppliedSources.unregistered` has no registered problem presentation -/
#guard_msgs in
reformulation unregisteredApplication : (unregistered 3) := by
  epigraph t

/-- error: declaration `Nat.succ` has no registered problem presentation -/
#guard_msgs in
reformulation nonProblemApplication : (Nat.succ 3) := by
  epigraph t

/-- error: reformulation source must be an application of a registered problem declaration -/
#guard_msgs in
reformulation lambdaSource : (fun a : ℝ => quadratic a) := by
  epigraph t

section

variable (localProblem : Problem ℝ ℝ)

/-- error: reformulation source must be an application of a registered problem declaration -/
#guard_msgs in
reformulation localSource : (localProblem) := by
  epigraph t

end

section

variable (x : ℝ)

/-- error: source parameter `x` conflicts with a decision variable; rename the outer parameter -/
#guard_msgs in
reformulation conflictingParameter : (quadratic x)
    certificate conflictingParameterAlias := by
  epigraph t

end

section

variable (t : ℝ)

/-- error: decision variable `t` conflicts with a source parameter; rename the outer parameter or choose a different decision name -/
#guard_msgs in
reformulation conflictingNewBinder : (quadratic t)
    certificate conflictingNewBinderAlias := by
  epigraph t

end

section

variable (u : ℝ)

/-- error: decision variable `u` conflicts with a source parameter; rename the outer parameter or choose a different decision name -/
#guard_msgs in
reformulation conflictingSubstitution : (logarithmic u) := by
  substitute x := Real.exp u

end

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
reformulation failedAfterTerminal : (absoluteBound 3)
    certificate failedAfterTerminalAlias := by
  conic
  epigraph t

run_cmd do
  let env ← Lean.getEnv
  for shortName in #[`bareFamily, `partialApplication, `unresolvedArgument,
      `unregisteredApplication, `nonProblemApplication, `lambdaSource, `localSource,
      `conflictingParameter, `conflictingNewBinder, `conflictingSubstitution,
      `failedAfterTerminal] do
    let name := `PTranTest.Surface.AppliedSources ++ shortName
    for artifact in #[name, name ++ `equivalence, name ++ `conicForm, name ++ `isConic] do
      if env.contains artifact then
        Lean.throwError "failed applied source emitted declaration `{artifact}`"
    if (PTran.Syntax.getProblemView? env name).isSome then
      Lean.throwError "failed applied source emitted presentation `{name}`"
  for aliasName in #[`conflictingParameterAlias, `conflictingNewBinderAlias,
      `failedAfterTerminalAlias] do
    if env.contains (`PTranTest.Surface.AppliedSources ++ aliasName) then
      Lean.throwError "failed applied source emitted its certificate alias"

namespace GeneratedNames

def family (cap : ℝ) :=
  problem (v : Fin 2 → ℝ)
    minimize (0 : ℝ)
    subject to magnitude : ‖WithLp.toLp 1 v‖ ≤ cap

section

variable (magnitude_aux : ℝ)

reformulation targeted : (family magnitude_aux) := by
  conic at magnitude

reformulation terminal : (family magnitude_aux) := by
  conic

example : GlobalEquivalence (family magnitude_aux) (targeted magnitude_aux) :=
  targeted.equivalence magnitude_aux
example : GlobalEquivalence (family magnitude_aux) (terminal magnitude_aux) :=
  terminal.equivalence magnitude_aux
example : IsConic (terminal magnitude_aux) := terminal.isConic magnitude_aux

end

run_cmd do
  for name in #[``targeted, ``terminal] do
    let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "generated auxiliary lost its presentation"
    unless view.binders.map (·.name.eraseMacroScopes) == #[`v, `magnitude_aux_1] do
      Lean.throwError "generated auxiliary captured the source parameter"

end GeneratedNames

reformulation validAfterFailures : (quadratic 11) := by
  epigraph t

example : GlobalEquivalence (quadratic 11) validAfterFailures := validAfterFailures.equivalence

end
end PTranTest.Surface.AppliedSources
