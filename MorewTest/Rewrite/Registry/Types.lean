/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Rewrite.Match
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Typed operation discovery

An overloaded head does not make natural and real powers interchangeable. Fixed
type arguments prune incompatible candidates, while polymorphic rules remain
available. Graph alternatives keep each side's head and type arguments together.
-/

namespace MorewTest.Rewrite.Registry.Types

open Lean Lean.Meta Lean.Elab.Term
open Morew Morew.Elab.Rewrite

noncomputable def realPowerGraph (p : ℝ) : GraphRepresentation (fun x : ℝ => x ^ p) where
  Auxiliary := Unit
  target x t _ := t = x ^ p
  source_iff_exists _ _ := by simp only [exists_const]

noncomputable def natPowerGraph (n : ℕ) : GraphRepresentation (fun x : ℝ => x ^ n) where
  Auxiliary := Unit
  target x t _ := t = x ^ n
  source_iff_exists _ _ := by simp only [exists_const]

def genericPowerGraph {X Y Z : Type*} [HPow X Y Z] (p : Y) :
    GraphRepresentation (fun x : X => x ^ p) where
  Auxiliary := Unit
  target x t _ := t = x ^ p
  source_iff_exists _ _ := by simp only [exists_const]

noncomputable def realPowerEpigraph (p : ℝ) : EpigraphRepresentation (fun x : ℝ => x ^ p) where
  Auxiliary := Unit
  target x t _ := x ^ p ≤ t
  source_iff_exists _ _ := by simp only [exists_const]

noncomputable def natPowerHypograph (n : ℕ) : HypographRepresentation (fun x : ℝ => x ^ n) where
  Auxiliary := Unit
  target x t _ := t ≤ x ^ n
  source_iff_exists _ _ := by simp only [exists_const]

def otherPower {X Y Z : Type*} [HPow X Y Z] (x : X) (p : Y) : Z := x ^ p

def computedInput : Bool → Type
  | true => ℝ
  | false => ℕ

def familyOperation (flag : Bool) {X : Type} (_ : X) : ℝ := if flag then 0 else 1

noncomputable def familyGraph (flag : Bool) :
    GraphRepresentation (fun x : computedInput flag => familyOperation flag x) where
  Auxiliary := Unit
  target x t _ := t = familyOperation flag x
  source_iff_exists _ _ := by simp only [exists_const]

def familyOutputOperation (flag : Bool) (x : computedInput flag) : computedInput flag := x

def familyOutputGraph (flag : Bool) : GraphRepresentation (familyOutputOperation flag) where
  Auxiliary := Unit
  target x t _ := t = familyOutputOperation flag x
  source_iff_exists _ _ := by simp only [exists_const]

private def selected (term : TSyntax `term) (expected : Array Name)
    (parameters : Nat := 0) (checkedRule? : Option Name := none) : TermElabM Unit := do
  let source ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  lambdaBoundedTelescope source parameters fun _ source => do
    let actual ← Registry.candidates .conic source
    let expected := expected.qsort fun a b => a.toString < b.toString
    unless actual == expected do throwError "unexpected typed rule candidates: {actual}"
    if let some name := checkedRule? then
      let domain ← Plan.predicateDomain source
      withLocalDeclD `point domain fun point => do
        let matched ← Match.declaration point (mkApp source point) name pure
        checkWithKernel matched.sourceIff
        let target ← mkAppM ``Exists #[matched.target]
        unless ← isDefEq (← inferType matched.sourceIff)
            (mkApp2 (mkConst ``Iff) (mkApp source point) target) do
          throwError "typed family matching changed the original predicate"

section

attribute [local morew_conic] realPowerGraph natPowerGraph genericPowerGraph
  realPowerEpigraph natPowerHypograph familyGraph familyOutputGraph

run_elab do
  selected (← `(fun x : ℝ × ℝ => x.2 = x.1 ^ (2 : ℕ)))
    #[``genericPowerGraph, ``natPowerGraph]
  selected (← `(fun x : ℝ × ℝ => x.1 ^ (2 : ℕ) = x.2))
    #[``genericPowerGraph, ``natPowerGraph]
  selected (← `(fun x : ℝ × ℝ => x.2 = x.1 ^ (1 / 2 : ℝ)))
    #[``genericPowerGraph, ``realPowerGraph]
  selected (← `(fun x : ℝ × ℝ => x.1 ^ (1 / 2 : ℝ) = x.2))
    #[``genericPowerGraph, ``realPowerGraph]
  selected (← `(fun x : ℝ × ℝ => x.1 ^ (2 : ℕ) = x.2 ^ (1 / 2 : ℝ)))
    #[``genericPowerGraph, ``natPowerGraph, ``realPowerGraph]
  -- The real-typed left head cannot lend its type arguments to the natural
  -- power on the right: the named helper remains an unrelated operation.
  selected (← `(fun x : ℝ × ℝ => otherPower x.1 (1 / 2 : ℝ) = x.2 ^ (2 : ℕ)))
    #[``genericPowerGraph, ``natPowerGraph]
  selected (← `(fun x : ℝ × ℝ => x.1 ^ (2 : ℕ) = otherPower x.2 (1 / 2 : ℝ)))
    #[``genericPowerGraph, ``natPowerGraph]
  selected (← `(fun x : ℝ × ℝ => x.1 ^ (1 / 2 : ℝ) ≤ x.2)) #[``realPowerEpigraph]
  selected (← `(fun x : ℝ × ℝ => x.1 ^ (2 : ℕ) ≤ x.2)) #[]
  selected (← `(fun x : ℝ × ℝ => x.2 ≤ x.1 ^ (2 : ℕ))) #[``natPowerHypograph]
  selected (← `(fun x : ℝ × ℝ => x.2 ≤ x.1 ^ (1 / 2 : ℝ))) #[]
  -- Generic output and operation type arguments are not excluded by indexing.
  selected (← `(fun (X Y Z : Type) [HPow X Y Z] (p : Y) =>
    fun x : X × Z => x.2 = x.1 ^ p))
    #[``genericPowerGraph, ``natPowerGraph, ``realPowerGraph] 5
  -- Declaration matching can infer the flag before reducing the input type.
  -- A stuck family head at registration must not prune either specialization.
  selected (← `(fun x : ℝ × ℝ => x.2 = familyOperation true x.1)) #[``familyGraph]
    (checkedRule? := some ``familyGraph)
  selected (← `(fun x : ℕ × ℝ => x.2 = familyOperation false x.1)) #[``familyGraph]
    (checkedRule? := some ``familyGraph)
  -- The result type is subject to the same conservative discovery policy.
  selected (← `(fun x : ℝ × ℝ => x.2 = familyOutputOperation true x.1)) #[``familyOutputGraph]
  selected (← `(fun x : ℕ × ℕ => x.2 = familyOutputOperation false x.1)) #[``familyOutputGraph]

end

end MorewTest.Rewrite.Registry.Types
