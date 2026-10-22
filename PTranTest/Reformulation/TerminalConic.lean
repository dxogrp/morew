import PTran.Reformulation

/-!
# Complete conic reformulations

Terminal validation preserves conic groups, lowers nonlinear leaves in place,
and retains exact structural data independently of the printed presentation.
-/

namespace PTranTest.Reformulation.TerminalConic

open PTran PTran.Conic
noncomputable section

def linear :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      bounds : 0 ≤ x ∧ True ∧ y ≤ 5
      equal : x = y

reformulation linearTarget : linear := by
  conic

example : GlobalEquivalence linear linearTarget := linearTarget.equivalence
example : Conic.Form linearTarget := linearTarget.conicForm
example : IsConic linearTarget := linearTarget.isConic
example : linearTarget.conicForm.data.toProblem = linearTarget :=
  linearTarget.conicForm.represents
example : linearTarget.conicForm.data.sense = .minimize := rfl
example : linearTarget.conicForm.data.rowCount = 3 := rfl
example (x y : ℝ) :
    (linearTarget.conicForm.data.constraints ⟨0, by decide⟩).Holds (x, y) ↔ 0 ≤ x := by
  change 0 ≤ x - 0 ↔ 0 ≤ x
  rw [sub_zero]
example (x y : ℝ) :
    (linearTarget.conicForm.data.constraints ⟨2, by decide⟩).Holds (x, y) ↔ x = y := by
  change x - y = 0 ↔ x = y
  exact sub_eq_zero

/--
info: problem (x y : ℝ)
  minimize x + y
  subject to
    bounds : 0 ≤ x ∧ True ∧ y ≤ 5
    equal : x = y
-/
#guard_msgs in
#printp linearTarget

def unconstrained := problem (x : ℝ) minimize x
reformulation unconstrainedTarget : unconstrained := by
  conic
example : unconstrainedTarget.conicForm.data.rowCount = 0 := rfl
example : unconstrainedTarget.conicForm.data.toProblem = unconstrainedTarget :=
  unconstrainedTarget.conicForm.represents

def allTrue := problem (_x : Fin 0 → ℝ) minimize (0 : ℝ) subject to trivial : True ∧ True
reformulation allTrueTarget : allTrue := by
  conic
example : allTrueTarget.conicForm.data.rowCount = 0 := rfl

def maximum :=
  problem (x t : ℝ)
    maximize t
    subject to
      quadratic : x ^ 2 ≤ t
      upper : t ≤ 10

reformulation maximumTarget : maximum := by
  conic
example : Problem (ℝ × ℝ) (OrderDual ℝ) := maximumTarget
example : maximumTarget.conicForm.data.sense = .maximize := rfl
example : maximumTarget.conicForm.data.toProblem = maximumTarget := maximumTarget.conicForm.represents

run_cmd Lean.Elab.Command.liftTermElabM do
  let type := (← Lean.getConstInfo ``maximumTarget).type
  unless type.isAppOfArity ``PTran.Problem 2 &&
      type.getAppArgs[1]!.isAppOfArity ``OrderDual 1 do
    throwError "maximizing target lost its explicit OrderDual annotation"
  let info ← Lean.getConstInfo ``linearTarget.isConic
  let some value := info.value? (allowOpaque := true) | throwError "missing property definition"
  unless (value.find? (·.isConstOf ``linearTarget.conicForm)).isSome do
    throwError "the property did not reference the named form"

def grouped :=
  problem (x y t : ℝ)
    minimize t
    subject to
      first : x = y
      bounds : |x| ≤ t ∧ y ≤ 1
      domainLog : 1 ≤ x ∧ t ≤ Real.log x
      last : t ≤ 10

reformulation groupedTarget : grouped := by
  conic

/--
info: problem (x y t : ℝ)
  minimize t
  subject to
    first : x = y
    bounds_conic_1 : x ≤ t
    bounds_conic_2 : -x ≤ t
    bounds_conic_3 : y ≤ 1
    domainLog_conic_1 : 1 ≤ x
    domainLog_conic_2 : (t, 1, x) ∈ EXP
    last : t ≤ 10
-/
#guard_msgs in
#printp groupedTarget

example : groupedTarget.conicForm.data.rowCount = 7 := rfl

def deferredMargin :=
  problem (x y t : ℝ)
    minimize t
    subject to
      logarithm : t ≤ Real.log x
      domain : 1 ≤ min x y

reformulation deferredTarget : deferredMargin := by
  conic
example : IsConic deferredTarget := deferredTarget.isConic

def mixed :=
  problem (x : ℝ) (v : Fin 2 → ℝ) (z : EuclideanSpace ℝ (Fin 1)) (t : ℝ)
    minimize t
    subject to
      polyhedral : |x| ≤ t
      euclidean : ‖z‖ ≤ t
      quadratic : (∑ i, v i ^ 2) ≤ t
      exponential : Real.exp x ≤ t

reformulation mixedTarget : mixed := by
  conic at polyhedral
  conic
example : mixedTarget.conicForm.data.rowCount = 5 := rfl
example : IsConic mixedTarget := mixedTarget.isConic

def collisions :=
  problem (x t loss_aux : ℝ)
    minimize t
    subject to
      loss_conic_1 : 0 ≤ loss_aux
      loss : Fn.softplus x ≤ t ∧ Fn.softplus (-x) ≤ t
      last : t ≤ 10

reformulation collisionsTarget : collisions := by
  conic
example : collisionsTarget.conicForm.data.rowCount = 6 := rfl

/--
info: problem (x t loss_aux : ℝ) (loss_aux_1 loss_aux_2 : Fin 2 → ℝ)
  minimize t
  subject to
    loss_conic_1 : 0 ≤ loss_aux
    loss_conic_1_1 : ∀ (i : Fin 2), (![0, x] i - t, 1, loss_aux_1 i) ∈ EXP
    loss_conic_2 : ∑ x, loss_aux_1 x ≤ 1
    loss_conic_3 : ∀ (i : Fin 2), (![0, -x] i - t, 1, loss_aux_2 i) ∈ EXP
    loss_conic_4 : ∑ x, loss_aux_2 x ≤ 1
    last : t ≤ 10
-/
#guard_msgs in
#printp collisionsTarget

def logSquared :=
  problem (x : ℝ)
    minimize (Real.log x) ^ 2
    subject to positive : 0 < x

reformulation logSquaredTarget : logSquared := by
  substitute x := Real.exp u
  epigraph t
  conic
example : IsConic logSquaredTarget := logSquaredTarget.isConic

reformulation continued : logSquaredTarget := by
  epigraph value as objectiveBound
  conic
example : GlobalEquivalence logSquared continued :=
  logSquaredTarget.equivalence.trans continued.equivalence

def logMaximum :=
  problem (x : ℝ)
    maximize Real.log x
    subject to margin : 1 ≤ x

reformulation logMaximumTarget : logMaximum := by
  hypograph t
  conic
example : logMaximumTarget.conicForm.data.sense = .maximize := rfl

-- Both sides have rule heads, but are constants, so the affine row is retained.
def constants :=
  problem (x : ℝ)
    minimize x
    subject to
      overlap : Real.exp 0 ≤ Real.log 2
      fallback : |2| ≤ min x (x + 1)
reformulation constantsTarget : constants := by
  conic
example : constantsTarget.conicForm.data.rowCount = 3 := rfl

def named :=
  problem (x t : ℝ)
    minimize t
    subject to
      Bounds.loss : |x| ≤ t
      «loss bound» : x ^ 2 ≤ t
      final : t ≤ 5

-- Declaration names and presentation labels belong to separate namespaces.
def loss_conic_1 : Nat := 17
reformulation namedTarget : named := by
  conic
run_cmd do
  let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) ``namedTarget
    | Lean.throwError "missing terminal presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) ==
      #[`loss_conic_1, `loss_conic_2, Lean.Name.mkSimple "loss bound_conic_1", `final] do
    Lean.throwError "terminal generated names lost qualified or escaped label stems"

-- Macro scopes are ignored for allocation while decoded labels stay readable.
macro "terminal_named_source%" : term =>
  `(problem (x t : ℝ) minimize t subject to generated : |x| ≤ t)
def macroSource := terminal_named_source%
reformulation macroTarget : macroSource := by
  conic
run_cmd do
  let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) ``macroTarget
    | Lean.throwError "missing macro-generated terminal presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) ==
      #[`generated_conic_1, `generated_conic_2] do
    Lean.throwError "terminal names retained macro scopes"

end
end PTranTest.Reformulation.TerminalConic
