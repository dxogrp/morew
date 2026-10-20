import PTranTest.Affine
import PTran.Elab.Conic

/-!
# Affine domain and row-instance regressions

Finite-only indexing evidence suffices to validate affine spaces. Row assembly
uses canonical structures even when unrelated ambient instances are available.
Every successful result and its exact source proposition are kernel checked.
-/

namespace PTranTest.AffineReviewRegressions

open Lean Lean.Meta Lean.Elab.Term
open PTran.Elab.Affine PTranTest.Affine Matrix
open scoped BigOperators

private noncomputable abbrev canonicalScalarLE : LE ℝ := inferInstance
private noncomputable abbrev canonicalVectorLE (n : ℕ) : LE (Fin n → ℝ) := inferInstance
private abbrev GroupedAlias := (Matrix (Fin 2) (Fin 3) ℝ × ℝ) × ℝ
private abbrev IndexInstance (ι : Type) := Fintype ι

private def assertRow (term : TSyntax `term) (parameterCount : Nat := 0) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let result ← match ← PTran.Elab.Conic.normalizeRow source with
      | .ok result => pure result
      | .error error => throwError "expected affine row {source}\n{error.reason}"
    for expression in #[result.constraint, result.pointwiseIff] do
      if expression.hasMVar || expression.hasSorry then
        throwError "row normalization returned an incomplete certificate"
      checkWithKernel expression
    let constraintType ← whnf (← inferType result.constraint)
    unless constraintType.isAppOfArity ``PTran.Conic.Constraint 3 do
      throwError "normalization did not produce a semantic constraint"
    let .forallE _ domain _ _ ← whnf (← inferType source)
      | throwError "row test source is not a function"
    let expected ← withLocalDeclD `x domain fun x => do
      -- Reuse the row's explicit structures, so the test does not accidentally
      -- synthesize the unrelated ambient normed-space instances it is testing.
      let holds := mkAppN
        (mkConst ``PTran.Conic.Constraint.Holds constraintType.getAppFn.constLevels!)
        (constraintType.getAppArgs ++ #[result.constraint, x])
      mkForallFVars #[x] (← mkAppM ``Iff #[holds, source.beta #[x]])
    checkWithKernel expected
    unless ← isDefEq (← inferType result.pointwiseIff) expected do
      throwError "row certificate proves the wrong statement"

private def assertRejected (term : TSyntax `term) (row : Bool := false)
    (parameterCount : Nat := 0) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let error ← if row then
        match ← PTran.Elab.Conic.normalizeRow source with
        | .ok _ => throwError "unsupported row was accepted"
        | .error error => pure error
      else
        match ← reifyAffine source with
        | .ok _ => throwError "unsupported affine function was accepted"
        | .error error => pure error
    if (← error.reason.toString).isEmpty then
      throwError "unsupported expression was rejected without a reason"

/-! No ambient `Fintype` is present when the decision domain is validated. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun (ι : Type) [Finite ι] => fun x : ι → ℝ => x)) 2
  assertAffine (← `(fun (ι : Type) [Finite ι] (i : ι) => fun x : ι → ℝ => x i)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (i : ι) =>
    fun x : (ι → ℝ) × ℝ => x.1 i + 2 * x.2)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] =>
    fun x : ι → ℝ => fun i => 2 * x i + 1)) 2
  assertAffine (← `(fun (ι : Type) [Finite ι] => fun x : ι → ℝ =>
    ∑ i ∈ @Finset.univ ι (Fintype.ofFinite ι), x i)) 2
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ι → ℝ =>
    @dotProduct ι ℝ (Fintype.ofFinite ι) _ _ a x)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ι → ℝ =>
    @dotProduct ι ℝ (Fintype.ofFinite ι) _ _ x a)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ι → ℝ =>
    letI := Fintype.ofFinite ι
    a ⬝ᵥ x)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) =>
    letI := Fintype.ofFinite ι
    fun x : ι → ℝ => x ⬝ᵥ a)) 3
  assertAffine (← `(fun (ι κ : Type) [Finite ι] [Finite κ] (A : Matrix κ ι ℝ) =>
    fun x : ι → ℝ => @Matrix.mulVec κ ι ℝ _ (Fintype.ofFinite ι) A x)) 5
  assertAffine (← `(fun (ι κ : Type) [Finite ι] [Finite κ] (A : Matrix ι κ ℝ) =>
    fun x : ι → ℝ => @Matrix.vecMul ι κ ℝ _ (Fintype.ofFinite ι) x A)) 5
  assertAffine (← `(fun (ι : Type) [Finite ι] (A : Matrix (Fin 2) ι ℝ) =>
    fun x : ι → ℝ => letI := Fintype.ofFinite ι; A *ᵥ x)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (A : Matrix ι (Fin 2) ℝ) =>
    letI := Fintype.ofFinite ι
    fun x : ι → ℝ => x ᵥ* A)) 3
  assertRow (← `(fun (ι : Type) [Finite ι] (i : ι) =>
    fun x : ι → ℝ => x i ≤ 3)) 3
  assertRow (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ι → ℝ =>
    @dotProduct ι ℝ (Fintype.ofFinite ι) _ _ a x ≥ 3)) 3

/-! Finiteness may be supplied only by an operation in the source. Its proof
must cover composed expressions and both row operands without changing the
enumeration used by the operation. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) =>
    letI := Fintype.ofEquiv (Fin 2) e
    fun x : ι → ℝ => a ⬝ᵥ x + 1)) 3
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) =>
    fun x : ι → ℝ =>
      letI := Fintype.ofEquiv (Fin 2) e
      1 + x ⬝ᵥ a)) 3
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (i : ι)
    (A : Matrix ι ι ℝ) => fun x : ι → ℝ =>
      (@Matrix.mulVec ι ι ℝ _ (Fintype.ofEquiv (Fin 2) e) A x) i + x i)) 4
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (A : Matrix ι ι ℝ) =>
    fun x : ℝ => @Matrix.vecMul ι ι ℝ _ (Fintype.ofEquiv (Fin 2) e)
      (fun _ => x) A + (fun _ => 1))) 3
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) => fun x : ι → ℝ =>
    ∑ i ∈ @Finset.univ ι (Fintype.ofEquiv (Fin 2) e), x i)) 2
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) => fun x : ι → ℝ =>
    let ft : IndexInstance ι := Fintype.ofEquiv (Fin 2) e
    x + fun _ => (@Fintype.card ι ft : ℝ))) 2
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) => fun x : ι → ℝ =>
    letI := Fintype.ofEquiv (Fin 2) e
    x + fun _ => (Fintype.card ι : ℝ))) 2
  assertRow (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (a : ι → ℝ) (i : ι) =>
    fun x : ι → ℝ => x i ≤
      @dotProduct ι ℝ (Fintype.ofEquiv (Fin 2) e) _ _ a x)) 4

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℕ → ℝ => x 0))
  assertRejected (← `(fun x : ℝ => fun _ : ℕ => x))
  assertRejected (← `(fun x : Fin 2 → ℝ =>
    @dotProduct (Fin 2) ℝ
      (if x 0 ≤ 0 then Fintype.ofFinite (Fin 2) else Fin.fintype 2) _ _ ![1, 2] x))
  assertRejected (← `(fun x : ℕ → ℝ => fun i : Empty =>
    letI : Fintype ℕ := Empty.elim i
    @dotProduct ℕ ℝ inferInstance _ _ (fun _ => 0) x))

/-! All relation orientations use the same fixed normed-space structures. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRow (← `(fun [NormedAddCommGroup ℝ] => fun x : ℝ => x = 3)) 1
  assertRow (← `(fun [NormedAddCommGroup ℝ] => fun x : ℝ => x ≤ 3)) 1
  assertRow (← `(fun [NormedAddCommGroup ℝ] => fun x : ℝ => x ≥ 3)) 1
  assertRow (← `(fun [NormedSpace ℝ ℝ] => fun x : ℝ => x = 3)) 1
  assertRow (← `(fun [NormedSpace ℝ ℝ] => fun x : ℝ => x ≤ 3)) 1
  assertRow (← `(fun [NormedSpace ℝ ℝ] => fun x : ℝ => x ≥ 3)) 1
  assertRow (← `(fun [NormedAddCommGroup (ℝ × ℝ)] [NormedSpace ℝ (ℝ × ℝ)] =>
    fun x : ℝ × ℝ => x.1 ≤ x.2)) 2
  assertRow (← `(fun [NormedAddCommGroup (Matrix (Fin 2) (Fin 3) ℝ)]
    [NormedSpace ℝ (Matrix (Fin 2) (Fin 3) ℝ)] =>
    fun x : Matrix (Fin 2) (Fin 3) ℝ => x 0 1 ≤ 3)) 2
  assertRow (← `(fun [NormedAddCommGroup GroupedAlias] [NormedSpace ℝ GroupedAlias] =>
    fun x : GroupedAlias => x.1.1 0 1 + x.1.2 ≤ x.2)) 2
  assertRow (← `(fun (ι : Type) [Finite ι]
    [NormedAddCommGroup ((ι → ℝ) × ℝ)] [NormedSpace ℝ ((ι → ℝ) × ℝ)] (i : ι) =>
    fun x : (ι → ℝ) × ℝ => x.1 i ≤ x.2)) 5

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRow (← `(fun [PartialOrder ℝ] => fun x : ℝ => x = 3)) 1
  assertRow (← `(fun [PartialOrder ℝ] => fun x : ℝ =>
    @LE.le ℝ canonicalScalarLE x 3)) 1
  assertRow (← `(fun [PartialOrder ℝ] => fun x : ℝ =>
    @GE.ge ℝ canonicalScalarLE x 3)) 1
  assertRow (← `(fun [LinearOrder ℝ] => fun x : ℝ => x = 3)) 1
  assertRow (← `(fun [LinearOrder ℝ] => fun x : ℝ =>
    @LE.le ℝ canonicalScalarLE x 3)) 1
  assertRow (← `(fun [LinearOrder ℝ] => fun x : ℝ =>
    @GE.ge ℝ canonicalScalarLE x 3)) 1

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRow (← `(fun [NormedAddCommGroup (Fin 2 → ℝ)]
    [NormedSpace ℝ (Fin 2 → ℝ)] [PartialOrder (Fin 2 → ℝ)] [PartialOrder ℝ] =>
    fun x : Fin 2 → ℝ => x = fun _ => (3 : ℝ))) 4
  assertRow (← `(fun [NormedAddCommGroup (Fin 2 → ℝ)]
    [NormedSpace ℝ (Fin 2 → ℝ)] [PartialOrder (Fin 2 → ℝ)] [PartialOrder ℝ] =>
    fun x : Fin 2 → ℝ => @LE.le (Fin 2 → ℝ) (canonicalVectorLE 2) x (fun _ => 3))) 4
  assertRow (← `(fun [NormedAddCommGroup (Fin 2 → ℝ)]
    [NormedSpace ℝ (Fin 2 → ℝ)] [PartialOrder (Fin 2 → ℝ)] [PartialOrder ℝ] =>
    fun x : Fin 2 → ℝ => @GE.ge (Fin 2 → ℝ) (canonicalVectorLE 2) x (fun _ => 3))) 4
  assertRow (← `(fun [LinearOrder ℝ] [LinearOrder (Fin 2 → ℝ)] =>
    fun x : Fin 2 → ℝ => x = fun _ => (3 : ℝ))) 2
  assertRow (← `(fun [LinearOrder ℝ] [LinearOrder (Fin 2 → ℝ)] =>
    fun x : Fin 2 → ℝ => @LE.le (Fin 2 → ℝ) (canonicalVectorLE 2) x (fun _ => 3))) 2
  assertRow (← `(fun [LinearOrder ℝ] [LinearOrder (Fin 2 → ℝ)] =>
    fun x : Fin 2 → ℝ => @GE.ge (Fin 2 → ℝ) (canonicalVectorLE 2) x (fun _ => 3))) 2

/-! Instances that actually change the source operations remain unsupported. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => @LE.le ℝ ⟨fun a b => a + 1 ≤ b⟩ x 3)) true
  assertRejected (← `(fun x : Fin 2 → ℝ =>
    @LE.le (Fin 2 → ℝ) ⟨fun a b => a 0 ≤ b 1⟩ x (fun _ => 3))) true
  assertRejected (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a * b⟩ x x ≤ 3)) true

end PTranTest.AffineReviewRegressions
