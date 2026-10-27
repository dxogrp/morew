/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.Support

/-!
# Registered conic records and retained-domain boundaries

Built-in removal affects automatic selection, while explicit selection remains
available. User subtype-domain records exercise the same checked retained-margin
policy as native logarithm and quotient rules.
-/

namespace MorewTest.Conic.Registry

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Elab.Conic MorewTest.Affine

private def check (term : TSyntax `term) (rows : Nat) (retained : Array Expr := #[])
    (name? : Option Name := none) : TermElabM Unit := do
  let source ← elaborate term
  let result ← match name? with
    | some name => Morew.Elab.Conic.Rewrite.planDeclaration source name retained
    | none => Morew.Elab.Conic.Rewrite.planUnique source retained
  let .ok result := result
    | match result with
      | .error error => throwError "registered conic rule failed: {error.reason}"
      | .ok _ => throwError "unreachable"
  let (predicates, certificates, proof) := match result with
    | .inl result => (result.rowPredicates, result.certifiedRows, result.lift)
    | .inr result => (result.rowPredicates, result.certifiedRows, result.conditionalIff)
  unless predicates.size == rows && certificates.size == rows do
    throwError "wrong number of certified registered rows"
  checkWithKernel proof
  for row in certificates do
    checkWithKernel row.constraint
    checkWithKernel row.pointwiseIff

private def reject (term : TSyntax `term) (fragment : String)
    (retained : Array Expr := #[]) (name? : Option Name := none) : TermElabM Unit := do
  let source ← elaborate term
  let before ← getMCtx
  let environment ← getEnv
  let result ← match name? with
    | some name => Morew.Elab.Conic.Rewrite.planDeclaration source name retained
    | none => Morew.Elab.Conic.Rewrite.planUnique source retained
  let .error error := result | throwError "unsupported registered conic rule was accepted"
  unless (← error.reason.toString).contains fragment do
    throwError "unexpected registered conic failure: {error.reason}"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "failed registration use leaked scratch metavariables"
  for (name, _) in (← getEnv).constants.toList do
    unless environment.contains name do throwError "failed registration use leaked {name}"

section
attribute [-morew_conic] Morew.Conic.Exponential.expEpigraph

run_cmd liftTermElabM do
  reject (← `(fun p : ℝ × ℝ => Real.exp p.1 ≤ p.2)) "no supported registered"
  check (← `(fun p : ℝ × ℝ => Real.exp p.1 ≤ p.2)) 1 #[]
    (some ``Morew.Conic.Exponential.expEpigraph)
end

run_cmd liftTermElabM do
  check (← `(fun p : ℝ × ℝ => Real.exp p.1 ≤ p.2)) 1

-- Source matching preserves the structural forms accepted by the conic
-- consumer, while certificates still refer to the unreduced predicate.
run_cmd liftTermElabM do
  check (← `(fun p : ℝ × ℝ => let (x, t) := p; Real.exp x ≤ t)) 1
  check (← `((Morew.Problem.mk (fun p : ℝ × ℝ => p.2)
    (fun p : ℝ × ℝ => Real.exp p.1 ≤ p.2)).feasible)) 1

noncomputable def positiveLog (x : ℝ) : ℝ := Real.log x

/-- Domain restriction is checked through a subtype, with no trusted metadata. -/
noncomputable def positiveLogRule :
    HypographRepresentation (fun x : {x : ℝ // 0 < x} => positiveLog x.1) :=
  Conic.Exponential.logHypograph

run_cmd liftTermElabM do
  reject (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1)) "no supported registered"

attribute [morew_conic] positiveLogRule

run_cmd liftTermElabM do
  let margin ← elaborate (← `(fun p : ℝ × ℝ => 1 ≤ p.1))
  check (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1)) 1 #[margin]
  reject (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1)) "positive constant margin"
  check (← `(fun t : ℝ => t ≤ positiveLog 2)) 1

/-- The record is exact on its subtype, but using retained evidence together
with a nontrivial auxiliary is intentionally beyond this registry consumer. -/
noncomputable def positiveLogWithAuxiliary :
    HypographRepresentation (fun x : {x : ℝ // 0 < x} => positiveLog x.1) where
  Auxiliary := ℝ
  target x t u := (t, 1, x.1) ∈ EXP ∧ u = 0
  source_iff_exists x t := by
    change t ≤ Real.log x.1 ↔ _
    rw [Conic.Exponential.le_log_iff x.1 t x.2]
    exact ⟨fun h => ⟨0, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

run_cmd liftTermElabM do
  let margin ← elaborate (← `(fun p : ℝ × ℝ => 1 ≤ p.1))
  reject (← `(fun p : ℝ × ℝ => p.2 ≤ positiveLog p.1))
    "retained-context exact replacements with auxiliary variables" #[margin]
    (some ``positiveLogWithAuxiliary)
  check (← `(fun t : ℝ => t ≤ positiveLog 2)) 2 #[]
    (some ``positiveLogWithAuxiliary)

/-- Target-local proof lets must remain available to the affine consumer. -/
noncomputable def quotientWithProofLet (c : ℝ) (h : c = 1) :
    EpigraphRepresentation (fun x : ℝ => x / c) where
  Auxiliary := Unit
  target x t _ :=
    let _nonzero : c ≠ 0 := by simpa only [h] using (one_ne_zero : (1 : ℝ) ≠ 0)
    x / c ≤ t
  source_iff_exists _ _ := by simp only [exists_const]

run_cmd liftTermElabM do
  let term ← elaborate (← `(fun (c : ℝ) (_ : c = 1) => fun x : ℝ => x / c ≤ 1))
  lambdaBoundedTelescope term 2 fun _ source => do
    match ← Morew.Elab.Conic.Rewrite.planDeclaration source ``quotientWithProofLet with
    | .error error => throwError "target-local nonzero evidence was lost: {error.reason}"
    | .ok (.inl result) =>
      checkWithKernel result.lift
      for row in result.certifiedRows do checkWithKernel row.pointwiseIff
    | .ok (.inr _) => throwError "independent target proof unexpectedly used retained rows"

noncomputable def positiveShift (c x : ℝ) : ℝ := Real.log c + x

/-- Scalar proof parameters use the same retained-margin policy as subtype inputs. -/
@[morew_conic]
noncomputable def positiveShiftRule (c : ℝ) (hc : 0 < c) :
    HypographRepresentation (positiveShift c) where
  Auxiliary := Unit
  target x t _ := (t - x, 1, c) ∈ EXP
  source_iff_exists x t := by
    simpa only [exists_const, positiveShift, sub_le_iff_le_add] using
      Conic.Exponential.le_log_iff c (t - x) hc

/-- Conditional auxiliary restrictions also apply to declaration proof parameters. -/
noncomputable def positiveShiftAuxiliary (c : ℝ) (hc : 0 < c) :
    HypographRepresentation (positiveShift c) where
  Auxiliary := ℝ
  target x t u := (t - x, 1, c) ∈ EXP ∧ u = 0
  source_iff_exists x t := by
    change t ≤ Real.log c + x ↔ _
    rw [← sub_le_iff_le_add, Conic.Exponential.le_log_iff c (t - x) hc]
    exact ⟨fun h => ⟨0, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

run_cmd liftTermElabM do
  let margin ← elaborate (← `(fun p : ℝ × ℝ × ℝ => 1 ≤ p.1))
  check (← `(fun p : ℝ × ℝ × ℝ => p.2.2 ≤ positiveShift p.1 p.2.1)) 1 #[margin]
  reject (← `(fun p : ℝ × ℝ × ℝ => p.2.2 ≤ positiveShift p.1 p.2.1))
    "positive constant margin"
  reject (← `(fun p : ℝ × ℝ × ℝ => p.2.2 ≤ positiveShift p.1 p.2.1))
    "retained-context exact replacements with auxiliary variables" #[margin]
    (some ``positiveShiftAuxiliary)
  check (← `(fun p : ℝ × ℝ => p.2 ≤ positiveShift 2 p.1)) 2 #[]
    (some ``positiveShiftAuxiliary)

end MorewTest.Conic.Registry
