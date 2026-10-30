/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.MatrixFraction
import MorewTest.Reformulation.Spectral

/-!
# Imported spectral and matrix-fraction certificates

An imported positive-definite domain lift remains evidence for a subsequent
matrix-fraction rewrite. Spectral witnesses and the source operator-norm
instance survive continued transformations and presentation replay.
-/

namespace MorewTest.ImportCompatibility.Spectral

open Morew Morew.Conic

noncomputable section

variable (m n : Nat)

reformulation continuedFraction :
    (MorewTest.Reformulation.MatrixFraction.domainIntermediate n) := by
  conic at bound
  conic

example : GlobalEquivalence (MorewTest.Reformulation.MatrixFraction.source n)
    (continuedFraction n) :=
  (MorewTest.Reformulation.MatrixFraction.domainIntermediate.equivalence n).trans
    (continuedFraction.equivalence n)

example : (continuedFraction.conicForm n).data.rowCount = 2 := rfl
example : (continuedFraction.conicForm n).data.toProblem = continuedFraction n :=
  (continuedFraction.conicForm n).represents

reformulation continuedNuclear :
    (MorewTest.Reformulation.Spectral.nuclearIntermediate (m := m) (n := n)) := by conic

example : GlobalEquivalence (MorewTest.Reformulation.Spectral.nuclearSource m n)
    (continuedNuclear (m := m) (n := n)) :=
  (MorewTest.Reformulation.Spectral.nuclearIntermediate.equivalence (m := m) (n := n)).trans
    (continuedNuclear.equivalence (m := m) (n := n))

example : (continuedNuclear.conicForm (m := m) (n := n)).data.rowCount = 2 := rfl
example : (continuedNuclear.conicForm (m := m) (n := n)).data.toProblem =
    continuedNuclear (m := m) (n := n) :=
  (continuedNuclear.conicForm (m := m) (n := n)).represents

namespace Shadow

def Fn.matrixFrac (x : ℝ) : ℝ := x + 100
def Fn.nuclearNorm (x : ℝ) : ℝ := x + 200
def SymmetricMatrix.fromBlocks (x : ℝ) : ℝ := x + 300

run_cmd do
  for (original, copied) in #[
      (``MorewTest.Reformulation.MatrixFraction.domainIntermediate, `domainCopy),
      (``continuedFraction, `fractionCopy),
      (``MorewTest.Reformulation.Spectral.nuclearIntermediate, `nuclearCopy),
      (``continuedNuclear, `continuedNuclearCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported spectral declaration lost replay metadata: {original}"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "spectral replay contains incomplete evidence"

example : domainCopy n = MorewTest.Reformulation.MatrixFraction.domainIntermediate n := rfl
example : fractionCopy n = continuedFraction n := rfl
example : nuclearCopy (m := m) (n := n) =
    MorewTest.Reformulation.Spectral.nuclearIntermediate (m := m) (n := n) := rfl
example : continuedNuclearCopy (m := m) (n := n) =
    continuedNuclear (m := m) (n := n) := rfl

end Shadow

open scoped Matrix.Norms.L2Operator in
def nestedNormSource :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (row t : ℝ)
    let original := A
    let magnitude := ‖Matrix.of (fun row column => original row column)‖
    minimize row + magnitude
    subject to
      bound : ‖Matrix.of (fun row column => original row column)‖ ≤ t

def selectedNormSource (selected : Norm (Matrix (Fin 2) (Fin 3) ℝ)) :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize (letI : Norm (Matrix (Fin 2) (Fin 3) ℝ) := selected; ‖A‖)
    subject to
      bound : (letI : Norm (Matrix (Fin 2) (Fin 3) ℝ) := selected; ‖A‖) ≤ t

syntax "heldNorm% " term:max : term

macro_rules
  | `(heldNorm% $value) => `(let held := $value; ‖held‖)

syntax "twiceNorm% " term:max : term

macro_rules
  | `(twiceNorm% $body) =>
      `((letI : Norm (Matrix (Fin 1) (Fin 1) ℝ) := ⟨fun _ => 1⟩; $body) +
        (letI : Norm (Matrix (Fin 1) (Fin 1) ℝ) := ⟨fun _ => 2⟩; $body))

open scoped Matrix.Norms.L2Operator in
def macroNormSource :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    let magnitude := heldNorm% A
    minimize heldNorm% A + magnitude
    subject to
      bound : heldNorm% A ≤ t

-- Whole-problem macros scope the decision binders and model-local definitions,
-- as well as the references in norm-containing fields.
macro "wholeNormProblem%" : term =>
  `(problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
      let original := A
      let magnitude := ‖original‖
      minimize magnitude + ‖A‖
      subject to bound : ‖original‖ ≤ t)

open scoped Matrix.Norms.L2Operator in
def wholeMacroNormSource := wholeNormProblem%

open scoped Matrix.Norms.L2Operator in
noncomputable def normSized (A : Matrix (Fin 2) (Fin 3) ℝ) : Fin (Nat.floor ‖A‖ + 1) :=
  ⟨0, Nat.zero_lt_succ _⟩

def normDependentTypeSource :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    let index := normSized A
    minimize (index.val : ℝ)

-- The macro splices identical norm syntax into two different local instances.
-- Replacing only norm subterms would accidentally retain the first instance twice.
def splicedNormSource :=
  problem (A : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ)
    minimize twiceNorm% ‖A‖
    subject to
      bound : twiceNorm% ‖A‖ ≤ t

example : splicedNormSource.objective (0, 0) = 3 := by norm_num [splicedNormSource]

-- Source elaboration must still permit inference from an enclosing application.
def keepProblem {X : Type} (source : Problem X ℝ) (_ : X) := source

def delayedNormSource := keepProblem (problem (x : _) minimize ‖x‖) (0 : ℝ)

def keepTypedProblem {X V : Type} (source : Problem X V) (_ : X) (_ : V) := source

def delayedAddSource :=
  keepTypedProblem (problem (x : _) minimize x + x) (0 : ℝ) (0 : ℝ)

def delayedNumeralSource :=
  keepTypedProblem (problem (_x : ℝ) minimize 1) (0 : ℝ) (0 : ℝ)

namespace ChangedNorm

-- Replaying an imported source must keep its original L2 operator norm even
-- when a different matrix norm is in scope at the replay site.
local instance (m n : Nat) : Norm (Matrix (Fin m) (Fin n) ℝ) := ⟨fun _ => 37⟩

variable (selected : Norm (Matrix (Fin 2) (Fin 3) ℝ))

run_cmd do
  for (original, copied) in #[(``MorewTest.Reformulation.Spectral.normSource, `normCopy),
      (``MorewTest.Reformulation.Spectral.normObjective, `objectiveCopy),
      (``nestedNormSource, `nestedCopy), (``selectedNormSource, `selectedCopy),
      (``macroNormSource, `macroCopy), (``splicedNormSource, `splicedCopy),
      (``wholeMacroNormSource, `wholeMacroCopy),
      (``normDependentTypeSource, `dependentTypeCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported spectral source lost its norm metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))

example : normCopy m n = MorewTest.Reformulation.Spectral.normSource m n := rfl
example : objectiveCopy = MorewTest.Reformulation.Spectral.normObjective := rfl
example : nestedCopy = nestedNormSource := rfl
example (selected : Norm (Matrix (Fin 2) (Fin 3) ℝ)) :
    selectedCopy selected = selectedNormSource selected := rfl
example : macroCopy = macroNormSource := rfl
example : wholeMacroCopy = wholeMacroNormSource := rfl
example : splicedCopy = splicedNormSource := rfl
example : splicedCopy.objective (0, 0) = 3 := by norm_num [splicedCopy]
example : dependentTypeCopy = normDependentTypeSource := rfl

end ChangedNorm

namespace ParameterNorm

def source (E : Type) [Norm E] :=
  problem (x : E) (t : ℝ)
    minimize t
    subject to
      bound : ‖x‖ ≤ t

variable (E : Type) [Norm E]

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``source
    | Lean.throwError "missing parameterized norm source"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent `copied) := $term))

example : copied E = source E := rfl

end ParameterNorm

namespace UniverseSource

universe u

def source (E : Type u) [Norm E] := problem (x : E) minimize ‖x‖

end UniverseSource

namespace UniverseReplay

universe v

variable (E : Type v) [Norm E]

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``UniverseSource.source
    | Lean.throwError "missing universe-polymorphic norm source"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent `copied) := $term))

example : copied E = UniverseSource.source E := rfl

end UniverseReplay

namespace ExplicitUniverseSource

universe u v

open scoped Classical

-- The universe occurs only in the value, so omitting it leaves an unsolved
-- level metavariable even though the value's type is already known.
def levelValue.{w} : ℝ := if Nonempty (Type w) then 1 else 0

def mixedValue.{a, b} (_E : Type a) : ℝ := if Nonempty (Type b) then 1 else 0

opaque levelType.{w} : Type w := PUnit

def bodyOnly :=
  problem (x : ℝ) minimize ‖x‖ + levelValue.{u} + levelValue.{u + 1}

def mixed (E : Type v) [Norm E] :=
  problem (x : E) minimize ‖x‖ + mixedValue.{_, u} E

-- A universe appearing in a constant's type can still be unconstrained by
-- the enclosing term: Nonempty discards the sort level from its result.
def hidden :=
  problem (x : ℝ) minimize ‖x‖ + if Nonempty levelType.{u} then 1 else 0

macro "explicitLevelValue% " name:ident : term => do
  let level : Lean.TSyntax `level := ⟨name.raw⟩
  `(levelValue.{$level})

def expanded := problem (x : ℝ) minimize ‖x‖ + explicitLevelValue% u

noncomputable def universeSized (x : ℝ) : Fin (Nat.floor (‖x‖ + |levelValue.{u}|) + 1) :=
  ⟨0, Nat.zero_lt_succ _⟩

def finSize {n : Nat} (_ : Fin n) := n

-- The inferred annotation contains a universe-sensitive norm expression;
-- the explicitly specialized value must still constrain its omitted level.
def inferred :=
  problem (x : ℝ)
    let index := universeSized.{u} x
    minimize (finSize index : ℝ)

end ExplicitUniverseSource

namespace ExplicitUniverseReplay

universe u w

variable (E : Type w) [Norm E]

run_cmd do
  for (original, copied) in #[(``ExplicitUniverseSource.bodyOnly, `bodyOnlyCopy),
      (``ExplicitUniverseSource.mixed, `mixedCopy),
      (``ExplicitUniverseSource.hidden, `hiddenCopy),
      (``ExplicitUniverseSource.expanded, `expandedCopy),
      (``ExplicitUniverseSource.inferred, `inferredCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "missing explicit-universe norm source"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))

example : bodyOnlyCopy.{u} = ExplicitUniverseSource.bodyOnly.{u} := rfl
example : mixedCopy.{u, w} E = ExplicitUniverseSource.mixed.{u, w} E := rfl
example : hiddenCopy.{u} = ExplicitUniverseSource.hidden.{u} := rfl
example : expandedCopy.{u} = ExplicitUniverseSource.expanded.{u} := rfl
example : inferredCopy.{u} = ExplicitUniverseSource.inferred.{u} := rfl

end ExplicitUniverseReplay

namespace OuterInstanceSource

universe u w

def real :=
  letI : Norm ℝ := ⟨fun _ => ExplicitUniverseSource.levelValue.{w}⟩
  problem (x : ℝ) minimize ‖x‖

-- The instance's value refers to the universe of E even though the reference
-- itself has type ℝ. Replaying under another universe name must preserve that link.
def anchored (E : Type u) :=
  letI : Norm E := ⟨fun _ => ExplicitUniverseSource.levelValue.{u}⟩
  problem (x : E) minimize ‖x‖

def independent (E : Type u) :=
  letI : Norm E := ⟨fun _ => ExplicitUniverseSource.levelValue.{w}⟩
  problem (x : E) minimize ‖x‖

def transitive (E : Type u) :=
  let original := ExplicitUniverseSource.levelValue.{u}
  let shifted := original + ExplicitUniverseSource.levelValue.{w}
  letI : Norm E := ⟨fun _ => shifted⟩
  problem (x : E) minimize ‖x‖

def inherited (E : Type u) [Norm E] :=
  let original := (inferInstance : Norm E)
  letI : Norm E := original
  problem (x : E) minimize ‖x‖

end OuterInstanceSource

namespace OuterInstanceReplay

universe v w

variable (E : Type v) [Norm E]

run_cmd do
  for (original, copied) in #[(``OuterInstanceSource.real, `realCopy),
      (``OuterInstanceSource.anchored, `anchoredCopy),
      (``OuterInstanceSource.independent, `independentCopy),
      (``OuterInstanceSource.transitive, `transitiveCopy),
      (``OuterInstanceSource.inherited, `inheritedCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "missing enclosing-instance norm source"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))

example : realCopy.{w} = OuterInstanceSource.real.{w} := rfl
example : anchoredCopy E = OuterInstanceSource.anchored E := rfl
example : independentCopy.{v, w} E = OuterInstanceSource.independent.{v, w} E := rfl
example : transitiveCopy.{v, w} E = OuterInstanceSource.transitive.{v, w} E := rfl
example : inheritedCopy E = OuterInstanceSource.inherited E := rfl

end OuterInstanceReplay

namespace AmbiguousInstanceUniverses

universe u v

-- The argument's universe does not determine the two source levels separately.
set_option linter.checkUnivs false in
def source (E : Type (max u v)) :=
  letI : Norm E := ⟨fun _ => ExplicitUniverseSource.levelValue.{u}⟩
  problem (x : E) minimize ‖x‖

variable (E : Type (max u v))

set_option linter.checkUnivs false in
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``source
    | Lean.throwError "missing enclosing-instance source with ambiguous universes"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent `copied) := $term))

example : copied.{u, v} E = source.{u, v} E := rfl

end AmbiguousInstanceUniverses

-- Checking a term without registering a declaration must not create replay helpers.
run_cmd Lean.Elab.Command.liftTermElabM do
  let before ← Lean.getEnv
  let term ← `(letI : Norm ℝ := ⟨fun _ => 1⟩
    problem (x : ℝ)
      let witness := (⟨x, rfl⟩ : { y : ℝ // ‖y‖ = ‖y‖ })
      minimize witness.val)
  discard <| Lean.Elab.Term.elabTerm term none
  for (name, _) in (← Lean.getEnv).constants.toList do
    if !before.contains name && name.toString.contains "_normReplay" then
      Lean.throwError "checking an unregistered problem created a replay helper"

end
end MorewTest.ImportCompatibility.Spectral
