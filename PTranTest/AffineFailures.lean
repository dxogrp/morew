import PTranTest.Affine
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Affine reification boundaries

Unsupported expressions fail without claiming a certificate or changing the
caller's metavariables. Custom functions remain ordinary valid Lean terms.
-/

namespace PTranTest.AffineFailures

open Lean Lean.Meta Lean.Elab.Term
open PTran.Elab.Affine PTranTest.Affine Matrix
open scoped BigOperators

private def assertUnsupported (term : TSyntax `term) (parameterCount : Nat := 0)
    (expectedHead? : Option Name := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    match ← reifyAffine source with
    | .ok _ => throwError "unexpected affine recognition of {source}"
    | .error error =>
      if (← error.reason.toString).isEmpty then
        throwError "unsupported expression has no failure reason"
      if let some expectedHead := expectedHead? then
        unless error.expression.consumeMData.getAppFn.isConstOf expectedHead do
          throwError "failure did not identify the unsupported subexpression"

noncomputable def customAffine (x : ℝ) : ℝ := 2 * x + 1
noncomputable abbrev customAlias (x : ℝ) : ℝ := 2 * x
noncomputable abbrev customCoercion : Coe ℝ ℝ := ⟨fun x => x * x⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => x * x)) 0 (some ``HMul.hMul)
  assertUnsupported (← `(fun x : ℝ => x * x - x * x))
  assertUnsupported (← `(fun x : ℝ => 0 * Real.exp x))
  assertUnsupported (← `(fun x : ℝ × ℝ => x.1 * x.2))
  assertUnsupported (← `(fun x : ℝ => x / x))
  assertUnsupported (← `(fun x : ℝ => 1 / x))
  assertUnsupported (← `(fun x : ℝ => x / 0))
  assertUnsupported (← `(fun c : ℝ => fun x : ℝ => x / c)) 1
  assertUnsupported (← `(fun x : ℝ => x ^ (2 : ℕ)))
  assertUnsupported (← `(fun x : ℝ => Real.exp x))
  assertUnsupported (← `(fun x : ℝ => x + Real.exp x)) 0 (some ``Real.exp)
  assertUnsupported (← `(fun x : ℝ => Real.log x))
  assertUnsupported (← `(fun x : ℝ => Real.sqrt x))
  assertUnsupported (← `(fun x : ℝ => |x|))
  assertUnsupported (← `(fun x : ℝ => max x 0))
  assertUnsupported (← `(fun x : ℝ => customAffine x))
  assertUnsupported (← `(fun x : ℝ => customAlias x))
  assertUnsupported (← `(fun x : ℝ => @Coe.coe ℝ ℝ customCoercion x))
  assertUnsupported (← `(fun x : ℝ => let a := x + 1; a * x))
  assertUnsupported (← `(fun x : ℝ => let a := x; let b := a + 1; b * x))
  assertUnsupported (← `(fun x : ℝ => let a := x + 1; x / a))
  assertUnsupported (← `(fun x : ℝ => ![x, x * x]))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => x ⬝ᵥ x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => !![x 0, 1; 0, 1] *ᵥ x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => x ᵥ* !![x 0, 1; 0, 1]))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => x (if x 0 ≤ 0 then 0 else 1)))
  assertUnsupported (← `(fun x : ℝ =>
    ∑ _i ∈ ({0, 1} : Finset ℕ).filter (fun _ => x ≤ 0), x))
  assertUnsupported (← `(fun x : ℝ => ∑' _i : ℕ, x))
  assertUnsupported (← `(fun x : ℝ => if x ≤ 0 then x else 2 * x))
  assertUnsupported (← `(fun x : ℕ => (x : ℝ)))
  assertUnsupported (← `(fun x : ℕ → ℝ => x 0))

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate (← `(fun c : ℝ => fun x : ℝ => x / c))
  lambdaBoundedTelescope expression 1 fun _ source => do
    let config : PTran.Elab.Affine.Config :=
      { nonzeroEvidence? := some fun _ => return some (mkConst ``True.intro) }
    if (← reifyAffine source config).isOk then
      throwError "accepted evidence that does not establish divisor nonzeroness"

/-! Matching the operation spelling alone is not a semantic guarantee. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun [HAdd ℝ ℝ ℝ] => fun x : ℝ => x + 1)) 1
  assertUnsupported (← `(fun [HMul ℝ ℝ ℝ] => fun x : ℝ => 2 * x)) 1
  assertUnsupported (← `(fun [HDiv ℝ ℝ ℝ] => fun x : ℝ => x / 2)) 1
  assertUnsupported (← `(fun [Neg ℝ] => fun x : ℝ => -x)) 1
  assertUnsupported (← `(fun [AddCommGroup ℝ] => fun x : ℝ => x + x)) 1
  assertUnsupported (← `(fun [Module ℝ (Fin 2 → ℝ)] =>
    fun x : Fin 2 → ℝ => (2 : ℝ) • x)) 1
  assertUnsupported (← `(fun [AddCommMonoid ℝ] =>
    fun x : Fin 2 → ℝ => ∑ i, x i)) 1
  assertUnsupported (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a * b⟩ x x))
  assertUnsupported (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a _ => a + a⟩ x x))
  assertUnsupported (← `(fun x : ℝ =>
    @HMul.hMul ℝ ℝ ℝ ⟨fun a b => a * b * b⟩ 2 x))
  assertUnsupported (← `(fun x : ℝ =>
    @HSMul.hSMul ℝ ℝ ℝ ⟨fun a b => a * b * b⟩ 2 x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ =>
    @dotProduct (Fin 2) ℝ
      (if x 0 ≤ 0 then Fintype.ofFinite (Fin 2) else Fin.fintype 2) _ _ ![1, 2] x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ =>
    @Matrix.mulVec (Fin 2) (Fin 2) ℝ _
      (if x 0 ≤ 0 then Fintype.ofFinite (Fin 2) else Fin.fintype 2) !![1, 2; 3, 4] x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ =>
    @Matrix.vecMul (Fin 2) (Fin 2) ℝ _
      (if x 0 ≤ 0 then Fintype.ofFinite (Fin 2) else Fin.fintype 2) x !![1, 2; 3, 4]))

/-! An unresolved operation instance cannot be assigned to force recognition. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let instanceType ← elaborate (← `(HMul ℝ ℝ ℝ))
  let unresolvedInstance ← mkFreshExprMVar instanceType
  withLocalDeclD `x real fun x => do
    let body := mkAppN (mkConst ``HMul.hMul [.zero, .zero, .zero])
      #[real, real, real, unresolvedInstance, ← mkNumeral real 2, x]
    let source ← mkLambdaFVars #[x] body
    if (← reifyAffine source).isOk then
      throwError "recognized an unresolved multiplication instance"
    if ← unresolvedInstance.mvarId!.isAssigned then
      throwError "reification assigned an instance metavariable"
    withLetDecl `hidden instanceType unresolvedInstance fun hidden => do
      let body := mkAppN (mkConst ``HMul.hMul [.zero, .zero, .zero])
        #[real, real, real, hidden, ← mkNumeral real 2, x]
      let source ← mkLambdaFVars #[x] body
      if source.hasMVar then
        throwError "hidden-instance regression no longer hides its metavariable"
      if (← reifyAffine source).isOk then
        throwError "recognized an unresolved instance hidden behind a local let"
      if ← unresolvedInstance.mvarId!.isAssigned then
        throwError "reification assigned a hidden instance metavariable"

/-! A locally available nonzero proof must itself be fully elaborated. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  withLocalDeclD `c real fun c => do
    let obligation ← mkAppM ``Ne #[c, ← mkNumeral real 0]
    let unresolvedProof ← mkFreshExprMVar obligation
    withLetDecl `hiddenNonzero obligation unresolvedProof fun _ =>
      withLocalDeclD `x real fun x => do
        let body ← mkAppM ``HDiv.hDiv #[x, c]
        let source ← mkLambdaFVars #[x] body
        if source.hasMVar then
          throwError "hidden-evidence regression no longer hides its metavariable"
        if (← reifyAffine source).isOk then
          throwError "accepted unresolved nonzero evidence hidden behind a local let"
        if ← unresolvedProof.mvarId!.isAssigned then
          throwError "reification assigned the hidden nonzero evidence metavariable"

/-! Matrix dimensions remain enforced by ordinary Lean elaboration. -/

/--
error: Application type mismatch: The argument
  x
has type
  Fin 2 → ℝ
but is expected to have type
  Fin 3 → ℝ
in the application
  A *ᵥ x
-/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 3) ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := A *ᵥ x

end PTranTest.AffineFailures
