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

end
end MorewTest.ImportCompatibility.Spectral
