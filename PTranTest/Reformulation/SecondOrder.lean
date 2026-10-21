import PTran

/-!
# Targeted second-order reformulations

These examples check exact membership predicates, unchanged domains and row
ordering, retained denominator margins, and composition of generated certificates.
-/

namespace PTranTest.Reformulation.SecondOrder

open PTran PTran.Conic

noncomputable section

def scalarSource :=
  problem (x t : ℝ)
    minimize x ^ 2
    subject to
      first : (x - 1) ^ 2 ≤ t
      untouched : Real.exp x ≤ 100
      last : t ≥ (2 * x + 1) ^ 2

reformulation scalarTarget : scalarSource := by
  conic at first
  conic at last

example : GlobalEquivalence scalarSource scalarTarget := scalarTarget.equivalence

example (x t : ℝ) : scalarTarget.objective (x, t) = x ^ 2 := rfl

example (x t : ℝ) : scalarTarget.feasible (x, t) ↔
    (t, 1 / 2, ![x - 1]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
      Real.exp x ≤ 100 ∧
      (t, 1 / 2, ![2 * x + 1]) ∈ (Cone.rotatedSecondOrder 1).carrier := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize x ^ 2
  subject to
    first_conic_1 : (t, 1 / 2, ![x - 1]) ∈ RSOC 1
    untouched : Real.exp x ≤ 100
    last_conic_1 : (t, 1 / 2, ![2 * x + 1]) ∈ RSOC 1
-/
#guard_msgs in
#printp scalarTarget

-- Re-elaborate the stored notation, rather than just checking its rendered text.
run_cmd do
  let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) ``scalarTarget
    | Lean.throwError "missing scalar cone presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `scalarCopy
  Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : scalarCopy = scalarTarget := rfl

namespace Vectors

class Dimension where
  size : Nat

variable [Dimension]

def source :=
  problem (v : Fin Dimension.size → ℝ) (t : ℝ)
    minimize t
    subject to
      before : (∑ i, Real.exp (v i)) ≤ 100
      euclidean : ‖WithLp.toLp 2 (fun i => v i - 1)‖ ≤ t
      squares : (∑ i, (2 * v i + 1) ^ 2) ≤ t
      squaredNorm : ‖WithLp.toLp 2 v‖ ^ 2 ≤ t
      infinity : ‖v‖ ≤ t

reformulation target : source := by
  conic at euclidean
  conic at squares
  conic at squaredNorm
  conic at infinity

example : GlobalEquivalence source target := target.equivalence

example (v : Fin Dimension.size → ℝ) (t : ℝ) : target.feasible (v, t) ↔
    (∑ i, Real.exp (v i)) ≤ 100 ∧
      (t, fun i => v i - 1) ∈ (Cone.secondOrder Dimension.size).carrier ∧
      (t, 1 / 2, fun i => 2 * v i + 1) ∈ (Cone.rotatedSecondOrder Dimension.size).carrier ∧
      (t, 1 / 2, v) ∈ (Cone.rotatedSecondOrder Dimension.size).carrier ∧
      0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) := Iff.rfl

def nativeSource :=
  problem (z : EuclideanSpace ℝ (Fin Dimension.size)) (t : ℝ)
    maximize t
    subject to
      norm : t ≥ ‖z‖
      squared : ‖(2 : ℝ) • z‖ ^ 2 ≤ t

reformulation nativeTarget : nativeSource := by
  conic at norm
  conic at squared
  hypograph value

example : GlobalEquivalence nativeSource nativeTarget := nativeTarget.equivalence

example (z : EuclideanSpace ℝ (Fin Dimension.size)) (t value : ℝ) :
    nativeTarget.feasible ((z, t), value) ↔
      (t, WithLp.ofLp z) ∈ (Cone.secondOrder Dimension.size).carrier ∧
      (t, 1 / 2, WithLp.ofLp ((2 : ℝ) • z)) ∈ (Cone.rotatedSecondOrder Dimension.size).carrier ∧
      value ≤ t := Iff.rfl

run_cmd do
  let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) ``nativeTarget
    | Lean.throwError "missing maximizing cone presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `nativeCopy
  Lean.Elab.Command.elabCommand (← `(def $name := $term))

-- The displayed numeral in `2 • z` re-elaborates as natural scaling, which
-- agrees with the original real scaling by the module laws.
example : nativeCopy = nativeTarget := by
  simp only [nativeCopy, nativeTarget, ofNat_smul_eq_nsmul]

end Vectors

namespace Matrix

class Parameter where
  rows : Nat
  columns : Nat
  matrix : Fin rows → Fin columns → ℝ
  offset : Fin rows → ℝ

variable [Parameter]

def source :=
  problem (x : Fin Parameter.columns → ℝ) (t : ℝ)
    minimize t
    subject to
      residual : ‖WithLp.toLp 2
        (fun i => (∑ j, Parameter.matrix i j * x j) - Parameter.offset i)‖ ≤ t

reformulation target : source := by
  conic at residual

example : GlobalEquivalence source target := target.equivalence

example (x : Fin Parameter.columns → ℝ) (t : ℝ) : target.feasible (x, t) ↔
    (t, fun i => (∑ j, Parameter.matrix i j * x j) - Parameter.offset i) ∈
      (Cone.secondOrder Parameter.rows).carrier := Iff.rfl

end Matrix

namespace Margins

def source :=
  problem (x y t : ℝ) (v : Fin 2 → ℝ) (z : EuclideanSpace ℝ (Fin 2))
    minimize t
    subject to
      before : y ≥ 1 / 2
      scalar : (x - 1) ^ 2 / y ≤ t
      sum : (∑ i, v i ^ 2) / y ≤ t
      wrapped : ‖WithLp.toLp 2 v‖ ^ 2 / y ≤ t
      native : ‖z‖ ^ 2 / y ≤ t
      after : 1 ≤ y

reformulation target : source := by
  conic at scalar
  conic at sum
  conic at wrapped
  conic at native

example : GlobalEquivalence source target := target.equivalence

example (x y t : ℝ) (v : Fin 2 → ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    target.feasible ((((x, y), t), v), z) ↔
      y ≥ 1 / 2 ∧
      (t, y / 2, ![x - 1]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
      (t, y / 2, v) ∈ (Cone.rotatedSecondOrder 2).carrier ∧
      (t, y / 2, v) ∈ (Cone.rotatedSecondOrder 2).carrier ∧
      (t, y / 2, WithLp.ofLp z) ∈ (Cone.rotatedSecondOrder 2).carrier ∧
      1 ≤ y := Iff.rfl

def nestedSource :=
  problem (x y t : ℝ)
    minimize t
    subject to
      unusable : -1 ≤ y
      quotient : x ^ 2 / y ≤ t
      nested : Real.exp x ≤ 100 ∧ (0 ≤ y ∧ (1 / 3 ≤ y ∧ x ≤ 10))

-- Search continues past unusable margins and projects the positive margin from
-- a retained conjunction without splitting or duplicating its presentation row.
reformulation nestedTarget : nestedSource := by
  conic at quotient

example : GlobalEquivalence nestedSource nestedTarget := nestedTarget.equivalence

example (x y t : ℝ) : nestedTarget.feasible ((x, y), t) ↔
    -1 ≤ y ∧ (t, y / 2, ![x]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
      (Real.exp x ≤ 100 ∧ (0 ≤ y ∧ (1 / 3 ≤ y ∧ x ≤ 10))) := Iff.rfl

/--
info: problem (x y t : ℝ)
  minimize t
  subject to
    unusable : -1 ≤ y
    quotient_conic_1 : (t, y / 2, ![x]) ∈ RSOC 1
    nested : Real.exp x ≤ 100 ∧ 0 ≤ y ∧ 1 / 3 ≤ y ∧ x ≤ 10
-/
#guard_msgs in
#printp nestedTarget

def constantSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      quotient : x ^ 2 / (3 / 2) ≤ t

reformulation constantTarget : constantSource := by
  conic at quotient

example : GlobalEquivalence constantSource constantTarget := constantTarget.equivalence

class Parameter where
  epsilon : ℝ

section

variable [Parameter] (hε : 0 < Parameter.epsilon)

def symbolicSource :=
  problem (x y t : ℝ)
    minimize t
    subject to
      margin : Parameter.epsilon ≤ y
      quotient : x ^ 2 / y ≤ t

include hε in
reformulation symbolicTarget : symbolicSource := by
  conic at quotient

example : GlobalEquivalence symbolicSource symbolicTarget :=
  symbolicTarget.equivalence hε

end

end Margins

namespace Dimensions

def emptySource :=
  problem (v : Fin 0 → ℝ) (y : ℝ)
    minimize (0 : ℝ)
    subject to
      norm : ‖WithLp.toLp 2 v‖ ≤ -1
      square : (∑ i, v i ^ 2) ≤ -1
      quotient : (∑ i, v i ^ 2) / y ≤ -1
      margin : 1 ≤ y

reformulation emptyTarget : emptySource := by
  conic at norm
  conic at square
  conic at quotient

example : GlobalEquivalence emptySource emptyTarget := emptyTarget.equivalence

example : ¬ emptyTarget.HasFeasiblePoint := by
  rintro ⟨⟨v, y⟩, h⟩
  have hn : ‖WithLp.toLp 2 v‖ ≤ -1 := h.1
  have := (norm_nonneg (WithLp.toLp 2 v)).trans hn
  norm_num at this

/--
info: problem (v : Fin 0 → ℝ) (y : ℝ)
  minimize 0
  subject to
    norm_conic_1 : (-1, v) ∈ SOC 0
    square_conic_1 : (-1, 1 / 2, fun i => v i) ∈ RSOC 0
    quotient_conic_1 : (-1, y / 2, fun i => v i) ∈ RSOC 0
    margin : 1 ≤ y
-/
#guard_msgs in
#printp emptyTarget

def singleSource :=
  problem (v : Fin 1 → ℝ)
    minimize v 0
    subject to
      norm : ‖WithLp.toLp 2 v‖ ≤ 3
      square : (∑ i, v i ^ 2) ≤ 9

reformulation singleTarget : singleSource := by
  conic at norm
  conic at square

example : GlobalEquivalence singleSource singleTarget := singleTarget.equivalence

/--
info: problem (v : Fin 1 → ℝ)
  minimize v 0
  subject to
    norm_conic_1 : (3, v) ∈ SOC 1
    square_conic_1 : (9, 1 / 2, fun i => v i) ∈ RSOC 1
-/
#guard_msgs in
#printp singleTarget

end Dimensions

namespace CarrierPresentation

-- Compact notation must leave other cone carriers valid when stored syntax is
-- re-elaborated, including the field notation used for their carriers.
def source :=
  problem (v : Fin 1 → ℝ) (t : ℝ)
    minimize t
    subject to
      norm : ‖WithLp.toLp 2 v‖ ≤ t
      other : v ∈ (Cone.nonnegative 1).carrier

reformulation target : source := by
  conic at norm

run_cmd do
  let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing mixed cone presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `copied
  Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : copied = target := rfl

-- The presentation hook must not alter exact semantic serialization.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← Lean.Elab.Term.elabTerm (← `(
    fun (v : Fin 2 → ℝ) (t : ℝ) => (t, v) ∈ SOC 2 ∧ (t, 1 / 2, v) ∈ RSOC 2)) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let original ← Lean.instantiateMVars original
  let exact ← PTran.Reformulation.Internal.exactExpressionSyntax original
  if (exact.raw.findStack? (fun _ => true) (fun stx =>
      stx.isOfKind ``PTran.Conic.socCarrier || stx.isOfKind ``PTran.Conic.rsocCarrier)).isSome then
    Lean.throwError "cone presentation notation leaked into exact semantic syntax"
  let restored ← Lean.Elab.Term.elabTerm exact none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  unless ← Lean.Meta.isDefEq original (← Lean.instantiateMVars restored) do
    Lean.throwError "exact cone syntax changed its meaning"

end CarrierPresentation

namespace Auxiliary

def source :=
  problem (v : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      one : ‖WithLp.toLp 1 v‖ ≤ t
      two : ‖WithLp.toLp 2 v‖ ≤ t

-- Either order preserves the same rows when the one-norm adds its auxiliary.
reformulation oneFirst : source := by
  conic at one
  conic at two

reformulation twoFirst : source := by
  conic at two
  conic at one

example : GlobalEquivalence source oneFirst := oneFirst.equivalence
example : GlobalEquivalence source twoFirst := twoFirst.equivalence

example (v u : Fin 2 → ℝ) (t : ℝ) : oneFirst.feasible ((v, t), u) ↔
    v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t ∧
      (t, v) ∈ (Cone.secondOrder 2).carrier := Iff.rfl

example (v u : Fin 2 → ℝ) (t : ℝ) :
    oneFirst.feasible ((v, t), u) ↔ twoFirst.feasible ((v, t), u) := Iff.rfl

end Auxiliary

namespace Composition

def Positive (x : ℝ) : Prop := 0 < x

def source :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      square : x ^ 2 ≤ 25
      absolute : |x| ≤ 5
      positive : Positive x

reformulation target : source := by
  conic at square
  conic at absolute
  substitute x := Real.exp u
  epigraph t as value

example : GlobalEquivalence source target := target.equivalence

example (u t : ℝ) : target.feasible (u, t) ↔
    (25, 1 / 2, ![Real.exp u]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
      Real.exp u ≤ 5 ∧ -Real.exp u ≤ 5 ∧ u ≤ t := Iff.rfl

def quadraticObjective :=
  problem (x : ℝ)
    minimize (x - 2) ^ 2

reformulation epigraphTarget : quadraticObjective := by
  epigraph t
  conic at epigraph_t

reformulation continued : epigraphTarget := by
  epigraph value as objectiveBound

example : GlobalEquivalence quadraticObjective continued :=
  epigraphTarget.equivalence.trans continued.equivalence

example (x t value : ℝ) : continued.feasible ((x, t), value) ↔
    (t, 1 / 2, ![x - 2]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
      t ≤ value := Iff.rfl

end Composition

namespace Names

def budget : Nat := 17

def source :=
  problem (x : ℝ)
    minimize x
    subject to
      budget_conic_1 : x ≤ 10
      budget : x ^ 2 ≤ 25
      labels.cap : (x - 1) ^ 2 ≤ 16
      «cap value» : (x + 1) ^ 2 ≤ 36

reformulation target : source := by
  conic at budget
  conic at labels.cap
  conic at «cap value»

example : GlobalEquivalence source target := target.equivalence

/--
info: problem (x : ℝ)
  minimize x
  subject to
    budget_conic_1 : x ≤ 10
    budget_conic_1_1 : (25, 1 / 2, ![x]) ∈ RSOC 1
    cap_conic_1 : (16, 1 / 2, ![x - 1]) ∈ RSOC 1
    «cap value_conic_1» : (36, 1 / 2, ![x + 1]) ∈ RSOC 1
-/
#guard_msgs in
#printp target

end Names

end
end PTranTest.Reformulation.SecondOrder
