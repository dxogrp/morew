/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.ImportCompatibility.PowerFamilies.Defined

/-!
# Imported finite power families

Imported prefix chains retain their row order and exact exponents. Further
reformulation and presentation replay preserve the source, auxiliary coordinates,
and named mathematical operations under consumer-side shadowing declarations.
-/

namespace MorewTest.ImportCompatibility.PowerFamilies

open Morew Morew.Conic
noncomputable section

reformulation imported : (Defined.lowered 3 (by decide)) := by
  conic at remaining

/--
info: problem (x : Fin 3 → ℝ) (t : ℝ) (reciprocal_aux : Fin 3 → ℝ)
  minimize t
  subject to
    domain : (fun x => 1) ≤ x
    mean : 0 ≤ Fn.geoMean x
    reciprocal_conic_1 : reciprocal_aux ⟨0, ⋯⟩ = x ⟨0, ⋯⟩
    reciprocal_conic_2 : ∀ (j : Fin (3 - 1)),
      (reciprocal_aux ⟨(↑j : ℕ), ⋯⟩, x ⟨(↑j : ℕ) + 1, ⋯⟩, reciprocal_aux ⟨(↑j : ℕ) + 1, ⋯⟩) ∈
        POW (((↑(↑j : ℕ) : ℝ) + 1) / ((↑(↑j : ℕ) : ℝ) + 2))
    reciprocal_conic_3 : (t, reciprocal_aux ⟨3 - 1, ⋯⟩, 1) ∈ POW (1 / ((↑3 : ℝ) + 1))
    remaining_conic_1 : t ≤ 5
    remaining_conic_2 : -t ≤ 5
-/
#guard_msgs in
#printp imported

reformulation ready : imported := by
  conic at mean
  conic

example : GlobalEquivalence (Defined.lowered 3 (by decide)) imported := imported.equivalence
example : GlobalEquivalence (Defined.source 3) ready :=
  (Defined.lowered.equivalence 3 (by decide)).trans
    (imported.equivalence.trans ready.equivalence)
example : Conic.Form ready := ready.conicForm
example : ready.conicForm.data.toProblem = ready := ready.conicForm.represents
example : IsConic ready := ready.isConic
example : ready.conicForm.data.rowCount = 10 := rfl

example (x u : Fin 3 → ℝ) (t : ℝ) : imported.objective ((x, t), u) = t := rfl

example (x u : Fin 3 → ℝ) (t : ℝ) : imported.feasible ((x, t), u) ↔
    (fun _ => (1 : ℝ)) ≤ x ∧ 0 ≤ Fn.geoMean x ∧
      u 0 = x 0 ∧
      (∀ j : Fin 2, (u ⟨j.val, by omega⟩, x ⟨j.val + 1, by omega⟩,
        u ⟨j.val + 1, by omega⟩) ∈ POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) ∧
      (t, u 2, 1) ∈ POW (1 / ((3 : ℝ) + 1)) ∧ t ≤ 5 ∧ -t ≤ 5 := Iff.rfl

run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``imported
    | Lean.throwError "import lost the finite power-family presentation"
  let names := view.constraints.map (·.name.eraseMacroScopes)
  unless names == #[`domain, `mean, `reciprocal_conic_1, `reciprocal_conic_2,
      `reciprocal_conic_3, `remaining_conic_1, `remaining_conic_2] do
    Lean.throwError "import changed finite power-family labels or row order: {names}"
  unless view.binders.size == 3 &&
      view.binders[2]!.name.eraseMacroScopes == `reciprocal_aux do
    Lean.throwError "import changed the auxiliary-vector presentation"

namespace Shadow

def Fn.geoMean {n : ℕ} (_ : Fin n → ℝ) : ℝ := 100

def Fn.invProd {n : ℕ} (_ : Fin n → ℝ) : ℝ := 200

def Cone.powerSet (_ : ℝ) : Set (ℝ × ℝ × ℝ) := Set.univ

def source : Nat := 37

-- The source is replayed with a locally supplied parameter of the same name.
variable (n : ℕ)

run_cmd do
  for (original, copied) in #[(``Defined.source, `copiedSource),
      (``imported, `copiedImported), (``ready, `copiedReady)] do
    let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "missing imported power-family presentation: {original}"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copied
    Lean.Elab.Command.elabCommand (← `(def $name := $term))

end Shadow

example (n : ℕ) : Shadow.copiedSource n = Defined.source n := rfl
example : Shadow.copiedImported = imported := rfl
example : Shadow.copiedReady = ready := rfl

end
end MorewTest.ImportCompatibility.PowerFamilies
