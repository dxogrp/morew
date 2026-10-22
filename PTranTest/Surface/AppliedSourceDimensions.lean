import PTran

/-!
# Applied sources with dimensions and parameter dependencies

Applied least-squares families preserve rectangular dimensions through epigraph
and conic conversion. Generic value universes and proof-only dependencies also
survive emitted target, certificate, and conic artifact declarations.
-/

namespace PTranTest.Surface.AppliedSourceDimensions

open PTran PTran.Conic
noncomputable section

namespace LeastSquares

def source {m n : Nat} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize ∑ i, ((∑ j, A i j * x j) - b i) ^ 2
    subject to
      nonnegative : 0 ≤ x

section
variable (rows columns : Nat) (design : Fin rows → Fin columns → ℝ)
  (response : Fin rows → ℝ)

reformulation symbolic : (source design response) := by
  epigraph t as residual
  conic

example : GlobalEquivalence (source design response)
    (symbolic rows columns design response) := symbolic.equivalence rows columns design response

example : IsConic (symbolic rows columns design response) :=
  symbolic.isConic rows columns design response

example : (symbolic.conicForm rows columns design response).data.toProblem =
    symbolic rows columns design response :=
  (symbolic.conicForm rows columns design response).represents

example (x : Fin columns → ℝ) (t : ℝ) :
    (symbolic rows columns design response).feasible (x, t) ↔
      0 ≤ x ∧ (t, 1 / 2, fun i => (∑ j, design i j * x j) - response i) ∈
        (Cone.rotatedSecondOrder rows).carrier := Iff.rfl

reformulation continued : (symbolic rows columns design response) := by
  epigraph value
  conic

example : GlobalEquivalence (source design response)
    (continued rows columns design response) :=
  (symbolic.equivalence rows columns design response).trans
    (continued.equivalence rows columns design response)

end

/--
info: problem (x : Fin columns → ℝ) (t : ℝ)
  minimize t
  subject to
    nonnegative : 0 ≤ x
    residual_conic_1 : (t, 1 / 2, fun i => ∑ x_1, design i x_1 * x x_1 - response i) ∈ RSOC rows
-/
#guard_msgs in
#printp symbolic

reformulation concrete : (source (m := 2) (n := 3) ![![1, 2, 3], ![4, 5, 6]] ![7, 8]) := by
  epigraph t as residual
  conic

example : Problem ((Fin 3 → ℝ) × ℝ) ℝ := concrete
example : concrete.conicForm.data.rowCount = 2 := rfl
example : GlobalEquivalence (source ![![1, 2, 3], ![4, 5, 6]] ![7, 8]) concrete :=
  concrete.equivalence
example : IsConic concrete := concrete.isConic

/--
info: problem (x : Fin 3 → ℝ) (t : ℝ)
  minimize t
  subject to
    nonnegative : 0 ≤ x
    residual_conic_1 : (t, 1 / 2, fun i => ∑ x_1, ![![1, 2, 3], ![4, 5, 6]] i x_1 * x x_1 - ![7, 8] i) ∈ RSOC 2
-/
#guard_msgs in
#printp concrete

-- An empty residual dimension still has a valid symbolic sum and cone row.
reformulation empty : (source (m := 0) (n := 3) 0 0) := by
  epigraph t
  conic

example : Problem ((Fin 3 → ℝ) × ℝ) ℝ := empty
example : GlobalEquivalence (source (m := 0) (n := 3) 0 0) empty := empty.equivalence

end LeastSquares

namespace Maximum

def source (cap : ℝ) :=
  problem (x : ℝ)
    maximize x
    subject to upper : x ≤ cap

section
variable (limit : ℝ)

reformulation target : (source limit) := by
  conic

example : GlobalEquivalence (source limit) (target limit) := target.equivalence limit
example : Problem ℝ (OrderDual ℝ) := target limit
example : (target.conicForm limit).data.sense = .maximize := rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo ``target
  Lean.Meta.forallTelescope info.type fun _ type => do
    unless type.isAppOfArity ``PTran.Problem 2 &&
        type.getAppArgs[1]!.isAppOfArity ``OrderDual 1 do
      throwError "applied maximizing target lost its explicit OrderDual annotation"

end
end Maximum

namespace Universes

universe u v

def source {α : Type u} [Preorder α] (lower : α) :=
  problem (x : α)
    minimize x
    subject to bound : lower ≤ x

section
variable (β : Type v) [Preorder β] (minimum : β)

reformulation target : (@source.{v} β _ minimum) := by
  epigraph t

example : GlobalEquivalence (source minimum) (target β minimum) :=
  target.equivalence β minimum

example (x t : β) : (target β minimum).feasible (x, t) ↔ minimum ≤ x ∧ x ≤ t :=
  Iff.rfl

end

/--
info: problem (x t : β)
  minimize t
  subject to
    bound : minimum ≤ x
    epigraph_t : x ≤ t
-/
#guard_msgs in
#printp target

namespace ResultUniverse

-- This family has no term parameters from which to recover its universe.
-- Targets and certificate aliases must retain the universe in their result type.
def source : Problem (ULift.{u} Nat) Nat :=
  problem (x : ULift.{u} Nat)
    minimize x.down

reformulation target : (source.{u}) certificate targetEquivalence := by
  epigraph t

example : Problem (ULift.{u} Nat × Nat) Nat := target.{u}
example : GlobalEquivalence source.{u} target.{u} := targetEquivalence.{u}

reformulation continued : (target.{u}) certificate continuedEquivalence := by
  epigraph upper

example : GlobalEquivalence source.{u} continued.{u} :=
  targetEquivalence.{u}.trans continuedEquivalence.{u}

end ResultUniverse

end Universes

namespace ProofDependencies

class Evidence where
  witness : True

opaque coefficient (_ : True) : ℝ := 7

def source (evidence : True) :=
  problem (x : ℝ)
    minimize coefficient evidence + x

section
variable [Evidence]

reformulation target : (source Evidence.witness) := by
  conic

example : GlobalEquivalence (source Evidence.witness) target := target.equivalence
example : Conic.Form target := target.conicForm
example : IsConic target := target.isConic

end

-- An explicit proof argument has to be recovered even though proof irrelevance
-- means matching the target expression alone need not assign its metavariable.
section
variable (evidence : True)

reformulation explicitTarget : (source evidence) := by
  conic

example : GlobalEquivalence (source evidence) (explicitTarget evidence) :=
  explicitTarget.equivalence evidence
example : Conic.Form (explicitTarget evidence) := explicitTarget.conicForm evidence
example : IsConic (explicitTarget evidence) := explicitTarget.isConic evidence

end

opaque witnessCoefficient (_ : ∃ n : Nat, n = n) : ℝ := 7

def parameterSource (a : Nat) :=
  problem (point : ℝ)
    minimize witnessCoefficient ⟨a, rfl⟩ + point

section
variable (data other : Nat)

-- Proof irrelevance may leave the target's data parameter unconstrained during
-- matching. It must retain the actual source parameter instead of choosing the
-- unrelated local parameter of the same type.
reformulation parameterTarget : (parameterSource data) certificate parameterEquivalence := by
  epigraph t

example : GlobalEquivalence (parameterSource data) (parameterTarget data) :=
  parameterTarget.equivalence data
example : GlobalEquivalence (parameterSource data) (parameterTarget data) :=
  parameterEquivalence data

reformulation parameterConic : (parameterSource data) := by
  conic

example : GlobalEquivalence (parameterSource data) (parameterConic data) :=
  parameterConic.equivalence data
example : Conic.Form (parameterConic data) := parameterConic.conicForm data
example : IsConic (parameterConic data) := parameterConic.isConic data

end

namespace ShadowedParameters

-- Proof irrelevance can make a certificate with the wrong argument typecheck.
-- Inspect the applications structurally, including the conic theorem's witness.
private def checkParameterApplication (declaration : Lean.Name) (parameter body : Lean.Expr)
    (applicationName : Lean.Name) (nested : Bool := false) : Lean.MetaM Unit := do
  let some application := body.find? (·.isAppOfArity applicationName 1)
    | throwError "`{declaration}` lost its application of `{applicationName}`"
  let argument := application.getArg! 0
  unless argument == parameter || (nested && (argument.find? (· == parameter)).isSome) do
    throwError "`{declaration}` applied `{applicationName}` to a different parameter"

private def checkParameterIdentity (declaration : Lean.Name)
    (typeApplications : Array Lean.Name := #[])
    (valueApplications : Array Lean.Name := #[])
    (parameterType : Lean.Expr := Lean.mkConst ``Nat)
    (nestedTypeApplications : Array Lean.Name := #[]) : Lean.MetaM Unit := do
  let info ← Lean.getConstInfo declaration
  Lean.Meta.forallTelescope info.type fun parameters type => do
    unless parameters.size == 1 &&
        (← Lean.Meta.inferType parameters[0]!) == parameterType do
      throwError "`{declaration}` generalized an unrelated shadowed parameter"
    for applicationName in typeApplications do
      checkParameterApplication declaration parameters[0]! type applicationName
    for applicationName in nestedTypeApplications do
      checkParameterApplication declaration parameters[0]! type applicationName true
  unless valueApplications.isEmpty do
    let some value := info.value? (allowOpaque := true)
      | throwError "`{declaration}` has no value"
    Lean.Meta.lambdaTelescope value fun parameters body => do
      unless parameters.size == 1 do
        throwError "`{declaration}` retained an unrelated shadowed parameter"
      for applicationName in valueApplications do
        checkParameterApplication declaration parameters[0]! body applicationName

private def checkGeneratedParameters (target aliasName terminal terminalAlias : Lean.Name)
    (parameterType : Lean.Expr := Lean.mkConst ``Nat)
    (sourceName : Lean.Name := ``parameterSource) (nestedSource : Bool := false) :
    Lean.MetaM Unit := do
  let directSources := if nestedSource then #[] else #[sourceName]
  let nestedSources := if nestedSource then #[sourceName] else #[]
  for name in #[target, terminal] do
    checkParameterIdentity name (parameterType := parameterType)
    checkParameterIdentity (name ++ `equivalence) (directSources.push name) #[]
      parameterType nestedSources
  checkParameterIdentity aliasName (directSources.push target) #[target ++ `equivalence]
    parameterType nestedSources
  checkParameterIdentity terminalAlias (directSources.push terminal)
    #[terminal ++ `equivalence] parameterType nestedSources
  checkParameterIdentity (terminal ++ `conicForm) #[terminal] #[] parameterType
  checkParameterIdentity (terminal ++ `isConic) #[terminal] #[terminal ++ `conicForm]
    parameterType

namespace DifferentTypes

variable (data : Bool)
section
variable (data : Nat)

reformulation target : (parameterSource data) certificate targetEquivalence := by
  epigraph t

reformulation terminal : (parameterSource data) certificate terminalEquivalence := by
  conic

example : GlobalEquivalence (parameterSource data) (target data) := targetEquivalence data
example : GlobalEquivalence (parameterSource data) (terminal data) := terminalEquivalence data
example : Conic.Form (terminal data) := terminal.conicForm data
example : IsConic (terminal data) := terminal.isConic data

end

run_cmd Lean.Elab.Command.liftTermElabM do
  checkGeneratedParameters ``target ``targetEquivalence ``terminal ``terminalEquivalence

end DifferentTypes

namespace InnerParameter

variable (data : Nat)
section
variable (data : Nat)

reformulation target : (parameterSource data) certificate targetEquivalence := by
  epigraph t

reformulation terminal : (parameterSource data) certificate terminalEquivalence := by
  conic

example : GlobalEquivalence (parameterSource data) (target data) := targetEquivalence data
example : GlobalEquivalence (parameterSource data) (terminal data) := terminalEquivalence data
example : Conic.Form (terminal data) := terminal.conicForm data
example : IsConic (terminal data) := terminal.isConic data

end

run_cmd Lean.Elab.Command.liftTermElabM do
  checkGeneratedParameters ``target ``targetEquivalence ``terminal ``terminalEquivalence

end InnerParameter

namespace OuterParameter

variable (data : Nat)
local notation "outerData" => data
section
variable (data : Nat)

reformulation target : (parameterSource outerData) certificate targetEquivalence := by
  epigraph t

reformulation terminal : (parameterSource outerData) certificate terminalEquivalence := by
  conic

example : GlobalEquivalence (parameterSource outerData) (target outerData) :=
  targetEquivalence outerData
example : GlobalEquivalence (parameterSource outerData) (terminal outerData) :=
  terminalEquivalence outerData
example : Conic.Form (terminal outerData) := terminal.conicForm outerData
example : IsConic (terminal outerData) := terminal.isConic outerData

end

run_cmd Lean.Elab.Command.liftTermElabM do
  checkGeneratedParameters ``target ``targetEquivalence ``terminal ``terminalEquivalence

end OuterParameter

-- Passing proofs directly creates generated proof declarations. Their original
-- parameters must remain attached to every emitted target and certificate.
def proofSource (evidence : ∃ n : Nat, n = n) :=
  problem (point : ℝ)
    minimize witnessCoefficient evidence + point

namespace InlineProof

variable (data : Bool)
section
variable (data : Nat)

reformulation target : (proofSource ⟨data, rfl⟩) certificate targetEquivalence := by
  epigraph t

reformulation terminal : (proofSource ⟨data, rfl⟩) certificate terminalEquivalence := by
  conic

example : GlobalEquivalence (proofSource ⟨data, rfl⟩) (target data) := targetEquivalence data
example : IsConic (terminal data) := terminal.isConic data

end

run_cmd Lean.Elab.Command.liftTermElabM do
  checkGeneratedParameters ``target ``targetEquivalence ``terminal ``terminalEquivalence
    (sourceName := ``proofSource) (nestedSource := true)

end InlineProof

namespace FunctionParameter

variable (data : Nat → Nat)
section
variable (data : Nat → Nat)

-- A retained parameter may occur in function position rather than as a leaf.
reformulation target : (parameterSource (data 0)) certificate targetEquivalence := by
  epigraph t

reformulation terminal : (parameterSource (data 0)) certificate terminalEquivalence := by
  conic

example : GlobalEquivalence (parameterSource (data 0)) (target data) := targetEquivalence data
example : IsConic (terminal data) := terminal.isConic data

end

run_cmd Lean.Elab.Command.liftTermElabM do
  checkGeneratedParameters ``target ``targetEquivalence ``terminal ``terminalEquivalence
    (Lean.mkForall `_ .default (Lean.mkConst ``Nat) (Lean.mkConst ``Nat))
    (nestedSource := true)

end FunctionParameter

namespace OuterInstance

set_option linter.overlappingInstances false

class Config where
  value : Nat

variable [cfg : Config]
local notation "outerConfig" => cfg
section
variable [cfg : Config]

-- Instance search would choose the inner instance, but the proof deliberately
-- uses the outer one. Count and inspect parameters instead of using proof irrelevance.
reformulation target : (proofSource ⟨(outerConfig).value, rfl⟩)
    certificate targetEquivalence := by
  epigraph t

reformulation terminal : (proofSource ⟨(outerConfig).value, rfl⟩)
    certificate terminalEquivalence := by
  conic

example : GlobalEquivalence (proofSource ⟨(outerConfig).value, rfl⟩) (@target outerConfig) :=
  @targetEquivalence outerConfig
example : IsConic (@terminal outerConfig) := @terminal.isConic outerConfig

end

run_cmd Lean.Elab.Command.liftTermElabM do
  checkGeneratedParameters ``target ``targetEquivalence ``terminal ``terminalEquivalence
    (Lean.mkConst ``Config) ``proofSource true

end OuterInstance
end ShadowedParameters
end ProofDependencies

end
end PTranTest.Surface.AppliedSourceDimensions
