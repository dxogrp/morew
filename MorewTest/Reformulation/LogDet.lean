/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Reformulation.PrintDetails

/-! Exact log-determinant bounds retain domains through both rewrite orders. -/

namespace MorewTest.Reformulation.LogDet

open Morew Morew.Conic

noncomputable section

def source (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosDef
      bound : t ≤ Fn.logDet X.toMatrix

variable (n : Nat) (hn : 0 < n)

reformulation terminal : (source n) := by conic

reformulation domainIntermediate : (source n) := by conic at domain

reformulation domainFirst : (source n) := by
  conic at domain
  conic at bound
  conic

reformulation logDetFirst : (source n) := by
  conic at bound
  conic at domain
  conic

reformulation namedRule : (source n) := by
  conic at bound using Morew.Conic.LogDet.hypograph
  conic

reformulation appliedRule : (source n) := by
  conic at bound using (Morew.Conic.LogDet.hypograph hn)
  conic

example : GlobalEquivalence (source n) (terminal n) := terminal.equivalence n hn
example : IsConic (terminal n) := terminal.isConic n
example : (terminal.conicForm n).data.rowCount = 4 := rfl
example : (terminal.conicForm n).data.toProblem = terminal n :=
  (terminal.conicForm n).represents
example : GlobalEquivalence (source n) (domainFirst n) := domainFirst.equivalence n hn
example : GlobalEquivalence (source n) (logDetFirst n) := logDetFirst.equivalence n hn
example : GlobalEquivalence (source n) (namedRule n) := namedRule.equivalence n hn
example : GlobalEquivalence (source n) (appliedRule n) := appliedRule.equivalence n hn

def reverseSource (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    minimize -t
    subject to
      bound : Real.log X.toMatrix.det ≥ t
      domain : X.toMatrix.PosDef

reformulation nativeDomainIntermediate : (reverseSource n) := by conic at domain

reformulation reverseTarget : (reverseSource n) := by conic
example : GlobalEquivalence (reverseSource n) (reverseTarget n) :=
  reverseTarget.equivalence n hn

def groupedSource (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      group : (let matrix := X.toMatrix; matrix.PosDef ∧ t ≤ Fn.logDet matrix)
      another : 2 * t - 1 ≤ Fn.logDet X.toMatrix

reformulation groupedTarget : (groupedSource n) := by conic
example : (groupedTarget.conicForm n).data.rowCount = 7 := rfl
example : GlobalEquivalence (groupedSource n) (groupedTarget n) :=
  groupedTarget.equivalence n hn

def marginSource (n : Nat) (epsilon : ℝ) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      margin : (X.toMatrix - epsilon • 1).PosSemidef
      bound : t ≤ Fn.logDet X.toMatrix

variable (epsilon : ℝ) (hε : 0 < epsilon)

reformulation marginTarget : (marginSource n epsilon) := by conic
example : GlobalEquivalence (marginSource n epsilon) (marginTarget n epsilon) :=
  marginTarget.equivalence n hn epsilon hε

def bundledMarginSource (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      margin : X - (2 : ℝ) • SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one ∈ PSD n
      bound : t ≤ Fn.logDet X.toMatrix

reformulation bundledMarginTarget : (bundledMarginSource n) := by conic
example : GlobalEquivalence (bundledMarginSource n) (bundledMarginTarget n) :=
  bundledMarginTarget.equivalence n hn

def witnessedSource (n : Nat) :=
  problem (X W : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      witness : SymmetricMatrix.fromBlocks X 1 W ∈ PSD (n + n)
      bound : t ≤ Fn.logDet X.toMatrix

reformulation witnessedTarget : (witnessedSource n) := by conic
example : (witnessedTarget.conicForm n).data.rowCount = 4 := rfl

def nativeWitnessedSource (n : Nat) :=
  problem (X W : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      group : (let matrix := X.toMatrix;
        (fromBlocksFin matrix 1 1 W.toMatrix).PosSemidef ∧ t ≤ Fn.logDet matrix)

reformulation nativeWitnessedTarget : (nativeWitnessedSource n) := by conic
example : GlobalEquivalence (nativeWitnessedSource n) (nativeWitnessedTarget n) :=
  nativeWitnessedTarget.equivalence n hn

def fixedSource (n : Nat) (X : Matrix (Fin n) (Fin n) ℝ) :=
  problem (t : ℝ)
    maximize t
    subject to bound : t ≤ Fn.logDet X

variable (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosDef)

reformulation fixedTarget : (fixedSource n X) := by
  conic at bound
  conic
example : GlobalEquivalence (fixedSource n X) (fixedTarget n X hX) :=
  fixedTarget.equivalence n hn X hX
example : (fixedTarget.conicForm n X hX).data.rowCount = 3 := rfl

section ConjoinedDomain

variable (family : Fin 2 → Matrix (Fin n) (Fin n) ℝ)
  (hFamily : True ∧ (∀ i, (family i).PosDef ∧ True))

reformulation fixedConjoinedTarget : (fixedSource n (family 0)) := by
  conic at bound
  conic
example : GlobalEquivalence (fixedSource n (family 0))
    (fixedConjoinedTarget n family hFamily) :=
  fixedConjoinedTarget.equivalence n hn family hFamily

end ConjoinedDomain

def affineSource (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      domain : ((2 : ℝ) • X.toMatrix + 1).PosDef
      bound : t + 1 ≤ Fn.logDet ((2 : ℝ) • X.toMatrix + 1)

reformulation affineTarget : (affineSource n) := by conic
example : GlobalEquivalence (affineSource n) (affineTarget n) :=
  affineTarget.equivalence n hn

def maximum :=
  problem (X : SymmetricMatrix 2)
    maximize Fn.logDet X.toMatrix
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

reformulation maximumTarget : maximum := by
  hypograph t as logDet_bound
  conic

def negativeMinimum :=
  problem (X : SymmetricMatrix 2)
    minimize -Fn.logDet X.toMatrix
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

reformulation negativeMinimumTarget : negativeMinimum := by
  epigraph t as logDet_bound
  conic

example : GlobalEquivalence maximum maximumTarget := maximumTarget.equivalence
example : IsConic maximumTarget := maximumTarget.isConic
example : GlobalEquivalence negativeMinimum negativeMinimumTarget :=
  negativeMinimumTarget.equivalence
example : IsConic negativeMinimumTarget := negativeMinimumTarget.isConic

set_option morew.affine.maxExpansionDepth 0 in
set_option morew.affine.maxExpansionSteps 0 in
set_option morew.affine.maxExpansionNodes 0 in
reformulation helpersDisabled : (source 2) := by conic

example : GlobalEquivalence (source 2) helpersDisabled := helpersDisabled.equivalence
example : IsConic helpersDisabled := helpersDisabled.isConic

def collisionSource :=
  problem (X : SymmetricMatrix 2) (bound_aux t : ℝ)
    maximize bound_aux
    subject to
      domain : X.toMatrix.PosDef
      bound : t ≤ Fn.logDet X.toMatrix

reformulation collisionTarget : collisionSource := by conic

run_cmd do
  let compact ← PrintDetails.printed ``collisionTarget false
  let detailed ← PrintDetails.printed ``collisionTarget true
  let again ← PrintDetails.printed ``collisionTarget false
  unless compact == again do
    Lean.throwError "log-det printing is not deterministic"
  for fragment in #["bound_aux_1", "LowerTriangularEntries 2", "Fin 2 → ℝ", "PSD (2 + 2)",
      "EXP", "domain_conic_1", "bound_conic_3"] do
    unless compact.contains fragment && detailed.contains fragment do
      Lean.throwError "log-det presentation lost {fragment}: {compact}"

end
end MorewTest.Reformulation.LogDet
