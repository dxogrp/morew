/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Readable finite power-cone chains

Concrete chain indices have ordinary finite-index notation, and both their exact
and readable presentations replay under conflicting consumer-side declarations.
Symbolic targets retain exact replay; their readable views retain the dimensions
and necessary embeddings, with omitted proofs.
-/

namespace MorewTest.Reformulation.PowerPrinting

open Morew Morew.Conic
noncomputable section

namespace GeometricMean

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    maximize t
    subject to
      domain : 0 ≤ x
      mean : t ≤ Fn.geoMean x

reformulation triple : (source 3) := by conic at mean
reformulation singleton : (source 1) := by conic at mean

/--
info: problem (x : Fin 3 → ℝ) (t : ℝ) (mean_aux : Fin 3 → ℝ)
  maximize t
  subject to
    domain : 0 ≤ x
    mean_conic_1 : mean_aux 0 = x 0
    mean_conic_2 : ∀ (j : Fin 2),
      (mean_aux (Fin.castSucc j), x (Fin.succ j), mean_aux (Fin.succ j)) ∈ POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
    mean_conic_3 : 0 ≤ mean_aux 2
    mean_conic_4 : t ≤ mean_aux 2
-/
#guard_msgs in
#printp triple

/--
info: problem (x : Fin 1 → ℝ) (t : ℝ) (mean_aux : Fin 1 → ℝ)
  maximize t
  subject to
    domain : 0 ≤ x
    mean_conic_1 : mean_aux 0 = x 0
    mean_conic_2 : ∀ (j : Fin 0),
      (mean_aux (Fin.castSucc j), x (Fin.succ j), mean_aux (Fin.succ j)) ∈ POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
    mean_conic_3 : 0 ≤ mean_aux 0
    mean_conic_4 : t ≤ mean_aux 0
-/
#guard_msgs in
#printp singleton

variable (n : ℕ) (hn : 0 < n)

include hn in
reformulation targeted : (source n) := by conic at mean

reformulation ready : (targeted n hn) := by conic

/--
info: problem (x : Fin n → ℝ) (t : ℝ) (mean_aux : Fin n → ℝ)
  maximize t
  subject to
    domain : 0 ≤ x
    mean_conic_1 : mean_aux ⟨0, hn⟩ = x ⟨0, hn⟩
    mean_conic_2 : ∀ (j : Fin (n - 1)),
      (mean_aux ⟨(↑j : ℕ), ⋯⟩, x ⟨(↑j : ℕ) + 1, ⋯⟩, mean_aux ⟨(↑j : ℕ) + 1, ⋯⟩) ∈
        POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
    mean_conic_3 : 0 ≤ mean_aux ⟨n - 1, ⋯⟩
    mean_conic_4 : t ≤ mean_aux ⟨n - 1, ⋯⟩
-/
#guard_msgs in
#printp targeted

example : GlobalEquivalence (source n) (targeted n hn) := targeted.equivalence n hn
example : GlobalEquivalence (source n) (ready n hn) :=
  (targeted.equivalence n hn).trans (ready.equivalence n hn)
example : Conic.Form (ready n hn) := ready.conicForm n hn
example : (ready.conicForm n hn).data.toProblem = ready n hn :=
  (ready.conicForm n hn).represents
example : IsConic (ready n hn) := ready.isConic n hn

example (x u : Fin n → ℝ) (t : ℝ) : (targeted n hn).feasible ((x, t), u) ↔
    0 ≤ x ∧ u ⟨0, hn⟩ = x ⟨0, hn⟩ ∧
      (∀ j : Fin (n - 1),
        (u ⟨j.val, by omega⟩, x ⟨j.val + 1, by omega⟩,
          u ⟨j.val + 1, by omega⟩) ∈
          POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) ∧
      0 ≤ u ⟨n - 1, by omega⟩ ∧ t ≤ u ⟨n - 1, by omega⟩ := Iff.rfl

end GeometricMean

namespace InverseProduct

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : (fun _ => (1 : ℝ)) ≤ x
      inverse : Fn.invProd x ≤ t

reformulation triple : (source 3) := by conic at inverse
reformulation singleton : (source 1) := by conic at inverse

/--
info: problem (x : Fin 3 → ℝ) (t : ℝ) (inverse_aux : Fin 3 → ℝ)
  minimize t
  subject to
    domain : (fun x => 1) ≤ x
    inverse_conic_1 : inverse_aux 0 = x 0
    inverse_conic_2 : ∀ (j : Fin 2),
      (inverse_aux (Fin.castSucc j), x (Fin.succ j), inverse_aux (Fin.succ j)) ∈
        POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
    inverse_conic_3 : (t, inverse_aux 2, 1) ∈ POW (1 / 4)
-/
#guard_msgs in
#printp triple

/--
info: problem (x : Fin 1 → ℝ) (t : ℝ) (inverse_aux : Fin 1 → ℝ)
  minimize t
  subject to
    domain : (fun x => 1) ≤ x
    inverse_conic_1 : inverse_aux 0 = x 0
    inverse_conic_2 : ∀ (j : Fin 0),
      (inverse_aux (Fin.castSucc j), x (Fin.succ j), inverse_aux (Fin.succ j)) ∈
        POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
    inverse_conic_3 : (t, inverse_aux 0, 1) ∈ POW (1 / 2)
-/
#guard_msgs in
#printp singleton

variable (n : ℕ) (hn : 0 < n)

include hn in
reformulation targeted : (source n) := by conic at inverse

reformulation ready : (targeted n hn) := by conic

/--
info: problem (x : Fin n → ℝ) (t : ℝ) (inverse_aux : Fin n → ℝ)
  minimize t
  subject to
    domain : (fun x => 1) ≤ x
    inverse_conic_1 : inverse_aux ⟨0, hn⟩ = x ⟨0, hn⟩
    inverse_conic_2 : ∀ (j : Fin (n - 1)),
      (inverse_aux ⟨(↑j : ℕ), ⋯⟩, x ⟨(↑j : ℕ) + 1, ⋯⟩, inverse_aux ⟨(↑j : ℕ) + 1, ⋯⟩) ∈
        POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
    inverse_conic_3 : (t, inverse_aux ⟨n - 1, ⋯⟩, 1) ∈ POW (1 / ((↑n : ℝ) + 1))
-/
#guard_msgs in
#printp targeted

example : GlobalEquivalence (source n) (targeted n hn) := targeted.equivalence n hn
example : GlobalEquivalence (source n) (ready n hn) :=
  (targeted.equivalence n hn).trans (ready.equivalence n hn)
example : Conic.Form (ready n hn) := ready.conicForm n hn
example : (ready.conicForm n hn).data.toProblem = ready n hn :=
  (ready.conicForm n hn).represents
example : IsConic (ready n hn) := ready.isConic n hn

example (x u : Fin n → ℝ) (t : ℝ) : (targeted n hn).feasible ((x, t), u) ↔
    (fun _ => (1 : ℝ)) ≤ x ∧ u ⟨0, hn⟩ = x ⟨0, hn⟩ ∧
      (∀ j : Fin (n - 1),
        (u ⟨j.val, by omega⟩, x ⟨j.val + 1, by omega⟩,
          u ⟨j.val + 1, by omega⟩) ∈
          POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) ∧
      (t, u ⟨n - 1, by omega⟩, 1) ∈ POW (1 / ((n : ℝ) + 1)) := Iff.rfl

end InverseProduct

namespace Shadow

def Fn.geoMean {n : ℕ} (_ : Fin n → ℝ) : ℝ := 100
def Fn.invProd {n : ℕ} (_ : Fin n → ℝ) : ℝ := 200
def Cone.powerSet (_ : ℝ) : Set (ℝ × ℝ × ℝ) := Set.univ
def Fin.castSucc {n : ℕ} (_ : _root_.Fin n) : _root_.Fin (n + 1) := 0
def Fin.succ {n : ℕ} (_ : _root_.Fin n) : _root_.Fin (n + 1) := 0

variable (n : ℕ) (hn : 0 < n)

-- Captured references, original proofs, and the readable indices must survive
-- re-elaboration. Checking the declaration also rules out unresolved proofs.
run_cmd do
  let symbolic := #[``GeometricMean.targeted, ``GeometricMean.ready,
    ``InverseProduct.targeted, ``InverseProduct.ready]
  for replay in [true, false] do
    for (original, stem) in #[(``GeometricMean.source, `geoSource),
        (``InverseProduct.source, `invSource),
        (``GeometricMean.triple, `geoTriple), (``GeometricMean.singleton, `geoSingleton),
        (``InverseProduct.triple, `invTriple), (``InverseProduct.singleton, `invSingleton),
        (``GeometricMean.targeted, `geoTargeted), (``GeometricMean.ready, `geoReady),
        (``InverseProduct.targeted, `invTargeted), (``InverseProduct.ready, `invReady)] do
      -- Symbolic readable views intentionally omit necessary Fin.mk proofs.
      if !replay && symbolic.contains original then continue
      let environment ← Lean.getEnv
      let view? := if replay then Morew.Syntax.getProblemView? environment original
        else Morew.Syntax.getProblemDisplayView? environment original
      let some view := view? | Lean.throwError m!"missing finite-chain presentation: {original}"
      let term ← Lean.Elab.liftMacroM view.toTermSyntax
      let copied := stem.appendAfter (if replay then "Exact" else "Display")
      let name := Lean.mkIdent copied
      Lean.Elab.Command.elabCommand (← `(def $name := $term))
      let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
      if declaration.type.hasMVar || declaration.type.hasSorry ||
          declaration.value!.hasMVar || declaration.value!.hasSorry then
        Lean.throwError m!"finite-chain replay contains unresolved terms or placeholders: {copied}"

example : geoSourceExact n = GeometricMean.source n := rfl
example : geoSourceDisplay n = GeometricMean.source n := rfl
example : invSourceExact n = InverseProduct.source n := rfl
example : invSourceDisplay n = InverseProduct.source n := rfl
example : geoTripleExact = GeometricMean.triple := rfl
example : geoTripleDisplay = GeometricMean.triple := rfl
example : geoSingletonExact = GeometricMean.singleton := rfl
example : geoSingletonDisplay = GeometricMean.singleton := rfl
example : invTripleExact = InverseProduct.triple := rfl
example : invTripleDisplay = InverseProduct.triple := rfl
example : invSingletonExact = InverseProduct.singleton := rfl
example : invSingletonDisplay = InverseProduct.singleton := rfl
example : geoTargetedExact n hn = GeometricMean.targeted n hn := rfl
example : geoReadyExact n hn = GeometricMean.ready n hn := rfl
example : invTargetedExact n hn = InverseProduct.targeted n hn := rfl
example : invReadyExact n hn = InverseProduct.ready n hn := rfl

end Shadow

end
end MorewTest.Reformulation.PowerPrinting
