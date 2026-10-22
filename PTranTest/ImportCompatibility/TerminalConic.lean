import PTranTest.ImportCompatibility.TerminalConic.Defined

/-!
# Imported terminal forms and continuation

Named forms certify the imported target itself. Both objective senses, proof-only
section parameters, and presentation metadata survive subsequent reformulation.
-/

namespace PTranTest.ImportCompatibility.TerminalConic

open PTran PTran.Conic
noncomputable section

variable [Parameter] (hn : 0 < Parameter.size) (hε : 0 < Parameter.epsilon)

def importedMinimumForm : Conic.Form minimumTarget := minimumTarget.conicForm
def importedMaximumForm : Conic.Form maximumTarget := maximumTarget.conicForm

example : importedMinimumForm.data.toProblem = minimumTarget := importedMinimumForm.represents
example : importedMaximumForm.data.toProblem = maximumTarget := importedMaximumForm.represents
example : IsConic minimumTarget := minimumTarget.isConic
example : IsConic maximumTarget := maximumTarget.isConic
example : importedMinimumForm.data.sense = .minimize := rfl
example : importedMaximumForm.data.sense = .maximize := rfl
example : importedMinimumForm.data.rowCount = 4 := rfl
example : importedMaximumForm.data.rowCount = 2 := rfl
example : GlobalEquivalence minimumSource minimumTarget := minimumEquivalence hn hε
example : GlobalEquivalence maximumSource maximumTarget := maximumEquivalence hε

reformulation continuedMinimum : minimumTarget := by
  epigraph value as objectiveBound
  conic

reformulation continuedMaximum : maximumTarget := by
  hypograph value as objectiveBound
  conic

example : GlobalEquivalence minimumTarget continuedMinimum := continuedMinimum.equivalence
example : GlobalEquivalence maximumTarget continuedMaximum := continuedMaximum.equivalence
example : GlobalEquivalence minimumSource continuedMinimum :=
  (minimumTarget.equivalence hn hε).trans continuedMinimum.equivalence
example : GlobalEquivalence maximumSource continuedMaximum :=
  (maximumTarget.equivalence hε).trans continuedMaximum.equivalence
example : IsConic continuedMinimum := continuedMinimum.isConic
example : IsConic continuedMaximum := continuedMaximum.isConic
example : continuedMinimum.conicForm.data.sense = .minimize := rfl
example : continuedMaximum.conicForm.data.sense = .maximize := rfl
example : continuedMinimum.conicForm.data.rowCount = 5 := rfl
example : continuedMaximum.conicForm.data.rowCount = 3 := rfl

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ)
    (value : ℝ) : continuedMinimum.objective ((((v, y), t), u), value) = value := rfl

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ)
    (value : ℝ) : continuedMinimum.feasible ((((v, y), t), u), value) ↔
      (∀ i, (v i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 ∧
        Parameter.epsilon ≤ y ∧ (t, 1, y) ∈ EXP ∧ t ≤ value := Iff.rfl

example (y t value : ℝ) : continuedMaximum.objective ((y, t), value) = value := rfl
example (y t value : ℝ) : continuedMaximum.feasible ((y, t), value) ↔
    Parameter.epsilon ≤ y ∧ (t, 1, y) ∈ EXP ∧ value ≤ t := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  for (name, sense, labels) in #[
      (``minimumTarget, ObjectiveSense.minimize,
        #[`lse_conic_1, `lse_conic_2, `margin, `logarithm_conic_1]),
      (``maximumTarget, ObjectiveSense.maximize, #[`margin, `logarithm_conic_1]),
      (``continuedMinimum, ObjectiveSense.minimize,
        #[`lse_conic_1, `lse_conic_2, `margin, `logarithm_conic_1, `objectiveBound]),
      (``continuedMaximum, ObjectiveSense.maximize,
        #[`margin, `logarithm_conic_1, `objectiveBound])] do
    let some view := Syntax.getProblemView? env name
      | Lean.throwError m!"import or continuation lost terminal presentation {name}"
    unless view.sense == sense do Lean.throwError "terminal objective sense changed after import"
    unless view.constraints.map (·.name.eraseMacroScopes) == labels do
      Lean.throwError "import or continuation changed terminal row labels"
  for name in #[``minimumTarget, ``maximumTarget] do
    for suffix in #[`equivalence, `conicForm, `isConic] do
      unless env.contains (name ++ suffix) do
        Lean.throwError m!"import lost terminal public artifact {name ++ suffix}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let declaration ← Lean.getConstInfo ``maximumTarget
  Lean.Meta.forallTelescope declaration.type fun _ body => do
    unless body.isAppOfArity ``Problem 2 &&
        body.getAppArgs[1]!.isAppOfArity ``OrderDual 1 do
      Lean.throwError "imported maximizing target lost its explicit OrderDual annotation"

namespace Shadow

def Parameter.size : Nat := 37
def Parameter.epsilon : ℝ := 100

run_cmd do
  for (source, copied) in #[(``minimumTarget, `copiedMinimum),
      (``maximumTarget, `copiedMaximum)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) source
      | Lean.throwError m!"import lost terminal presentation {source}"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copied
    Lean.Elab.Command.elabCommand (← `(def $name := $term))

end Shadow

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ) :
    Shadow.copiedMinimum.objective (((v, y), t), u) =
      minimumTarget.objective (((v, y), t), u) := rfl
example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ) :
    Shadow.copiedMinimum.feasible (((v, y), t), u) ↔
      minimumTarget.feasible (((v, y), t), u) := Iff.rfl
example (y t : ℝ) : Shadow.copiedMaximum.feasible (y, t) ↔
    maximumTarget.feasible (y, t) := Iff.rfl

end
end PTranTest.ImportCompatibility.TerminalConic
