/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD
import Morew.Elab.Conic.Evidence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Checked global matrix symmetry

PSD coordinates need symmetry at every decision point. This bounded checker
uses structural matrix identities and independent hypotheses, including explicit
universal witnesses. Feasibility hypotheses mentioning the decision point are
never evidence. Every successful result is checked before it leaves isolation.
-/

namespace Morew.Elab.Conic.Symmetry

open Lean Lean.Meta

private theorem congruence {m n : Type*} [Fintype m]
    (A : Matrix m m ℝ) (C : Matrix m n ℝ) (h : A.IsSymm) :
    (C.transpose * A * C).IsSymm := by
  simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose,
    h.eq, Matrix.mul_assoc]

private theorem congruenceRight {m n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (C : Matrix m n ℝ) (h : A.IsSymm) :
    (C * A * C.transpose).IsSymm := by
  simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose,
    h.eq, Matrix.mul_assoc]

private theorem sumSymmetric {ι n : Type*} (s : Finset ι)
    (f : ι → Matrix n n ℝ) (h : ∀ i, (f i).IsSymm) :
    (∑ i ∈ s, f i).IsSymm := by
  simp only [Matrix.IsSymm, Matrix.transpose_sum, fun i => (h i).eq]

private theorem positiveDefiniteSymmetric {n : Type*} (M : Matrix n n ℝ)
    (h : M.PosDef) : M.IsSymm := Matrix.isHermitian_iff_isSymm.mp h.isHermitian

private theorem positiveSemidefiniteSymmetric {n : Type*} (M : Matrix n n ℝ)
    (h : M.PosSemidef) : M.IsSymm := Matrix.isHermitian_iff_isSymm.mp h.isHermitian

private def structuralRules (matrix : Expr) : Array Name := Id.run do
  let head := matrix.getAppFn.constName?
  if head == some ``HAdd.hAdd then
    return #[``Matrix.isSymm_add_transpose_self, ``Matrix.isSymm_transpose_add_self,
      ``Matrix.IsSymm.add]
  if head == some ``HSub.hSub then return #[``Matrix.IsSymm.sub]
  if head == some ``Neg.neg then return #[``Matrix.IsSymm.neg]
  if head == some ``HSMul.hSMul then return #[``Matrix.IsSymm.smul]
  if head == some ``HMul.hMul then return #[``congruence, ``congruenceRight]
  if head == some ``Matrix.transpose then return #[``Matrix.IsSymm.transpose]
  if head == some ``Matrix.diagonal then return #[``Matrix.isSymm_diagonal]
  if head == some ``Finset.sum then return #[``sumSymmetric]
  if head == some ``Matrix.fromBlocks then return #[``Matrix.IsSymm.fromBlocks]
  if head == some ``Morew.Conic.fromBlocksFin then
    return #[``Morew.Conic.isSymm_fromBlocksFin]
  if head == some ``Matrix.reindex then return #[``Matrix.IsSymm.reindex]
  if head == some ``DFunLike.coe && matrix.getAppNumArgs == 6 then
    let operation := matrix.getAppArgs[4]!
    if operation.isAppOf ``Matrix.reindex then return #[``Matrix.IsSymm.reindex]
  if head == some ``Matrix.submatrix then return #[``Matrix.IsSymm.submatrix]
  if head == some ``Morew.Conic.SymmetricMatrix.toMatrix then
    return #[``Morew.Conic.SymmetricMatrix.toMatrix_isSymm]
  if head == some ``OfNat.ofNat then return #[``Matrix.isSymm_zero, ``Matrix.isSymm_one]
  if head == some ``Zero.zero then return #[``Matrix.isSymm_zero]
  return #[]

-- Concrete literals use a bounded number of coordinate goals. Symbolic sizes
-- remain symbolic and are handled by structural lemmas or explicit witnesses.
private def literalProof (goal : MVarId) (matrix : Expr) : MetaM Unit := do
  let .forallE _ index _ _ ← whnf (← inferType matrix) | failure
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 do failure
  let some n ← getNatValue? index.getAppArgs[0]! | failure
  unless n ≤ 16 do failure
  let (goals, _) ← Elab.Term.TermElabM.run <| Elab.Tactic.run goal do
    Elab.Tactic.evalTactic (← `(tactic|
      (apply Matrix.IsSymm.ext
       intro i j
       fin_cases i <;> fin_cases j <;> norm_num [Matrix.of_apply] <;> ring)))
  unless goals.isEmpty do failure

private partial def solve (goal : MVarId) (hypotheses : Array Expr) (fuel : Nat) :
    MetaM Unit := goal.withContext do
  if fuel == 0 then failure
  let saved ← saveState
  try
    goal.refl
    return
  catch _ => saved.restore
  for hypothesis in hypotheses do
    try
      let goals ← goal.apply hypothesis
      for subgoal in goals do solve subgoal hypotheses (fuel - 1)
      return
    catch _ => saved.restore
  let target ← instantiateMVars (← goal.getType)
  if target.isForall then
    let (_, next) ← goal.intro1
    solve next hypotheses (fuel - 1)
    return
  if target.isAppOf ``Matrix.IsSymm then
    let matrix ← Expr.reduceStructure target.getAppArgs.back!
    for name in structuralRules matrix do
      try
        let goals ← goal.apply (← mkConstWithFreshMVarLevels name)
        for subgoal in goals do solve subgoal hypotheses (fuel - 1)
        return
      catch _ => saved.restore
    for name in #[``positiveDefiniteSymmetric, ``positiveSemidefiniteSymmetric] do
      try
        let goals ← goal.apply (← mkConstWithFreshMVarLevels name)
        for subgoal in goals do solve subgoal hypotheses (fuel - 1)
        return
      catch _ => saved.restore
    try
      literalProof goal matrix
      return
    catch _ => saved.restore
    -- Entrywise universal witnesses need not be phrased with IsSymm.
    try
      let goals ← goal.apply (← mkConstWithFreshMVarLevels ``Matrix.IsSymm.ext)
      for subgoal in goals do solve subgoal hypotheses (fuel - 1)
      return
    catch _ => saved.restore
  failure

/-- Prove symmetry of the supplied matrix for every decision point, using only
independent hypotheses and bounded structural or literal proofs. -/
def prove? (point matrix : Expr) : MetaM (Option Expr) := do
  let result ← State.withIsolatedMVars do
    try
      if (← Expr.hasUnresolved matrix) || (← Evidence.hasPlaceholders matrix) then
        return .error ()
      let mut hypotheses := #[]
      for declaration in ← getLCtx do
        if declaration.isImplementationDetail then continue
        let hypothesis := declaration.toExpr
        if (← isProp declaration.type) && !(← Expr.depends point hypothesis) &&
            !(← Expr.hasUnresolved hypothesis) && !(← Evidence.hasPlaceholders hypothesis) then
          hypotheses := hypotheses.push hypothesis
      let proposition ← mkAppM ``Matrix.IsSymm #[matrix]
      let proof ← mkFreshExprMVar proposition
      let context ← readThe Core.Context
      let limit := (← IO.getNumHeartbeats) - context.initHeartbeats + 2_000_000
      withTheReader Core.Context
          (fun ctx => { ctx with maxHeartbeats :=
            if ctx.maxHeartbeats == 0 then limit else min ctx.maxHeartbeats limit }) do
        solve proof.mvarId! hypotheses 32
      let proof ← instantiateMVars proof
      if proof.hasMVar || (← Evidence.hasPlaceholders proof) then return .error ()
      let proof ← mkLambdaFVars #[point] proof
      checkWithKernel proof
      return .ok proof
    catch _ => return .error ()
  return result.toOption

end Morew.Elab.Conic.Symmetry
