import PTranTest.Affine.Support
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite domains and indexing evidence

Source-provided finite indexing must scope composed affine expressions and
both row operands, without promoting evidence that depends on a source binder.
-/

namespace PTranTest.Affine.FiniteIndexing

open Lean Lean.Meta Lean.Elab.Term
open PTran.Elab.Affine PTranTest.Affine Matrix
open scoped BigOperators

private abbrev IndexInstance (ι : Type) := Fintype ι

/-! Finite indexing instances belong to the source expression's semantics. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 2 → ℝ =>
    @dotProduct (Fin 2) ℝ (Fintype.ofFinite (Fin 2)) _ _ ![1, 2] x))
  assertAffine (← `(fun x : Fin 2 → ℝ =>
    @dotProduct (Fin 2) ℝ (Fintype.ofFinite (Fin 2)) _ _ x ![1, 2]))
  assertAffine (← `(fun x : Fin 2 → ℝ =>
    @Matrix.mulVec (Fin 2) (Fin 2) ℝ _ (Fintype.ofFinite (Fin 2)) !![1, 2; 3, 4] x))
  assertAffine (← `(fun x : Fin 2 → ℝ =>
    @Matrix.vecMul (Fin 2) (Fin 2) ℝ _ (Fintype.ofFinite (Fin 2)) x !![1, 2; 3, 4]))


run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 2 → ℝ =>
    ∑ i ∈ @Finset.univ (Fin 2) (Fintype.ofFinite (Fin 2)), x i))

/-! Explicit finite-index evidence scopes the vector operands too. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ℝ =>
    @dotProduct ι ℝ (Fintype.ofFinite ι) _ _ a (fun _ => x))) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ℝ =>
    @dotProduct ι ℝ (Fintype.ofFinite ι) _ _ (fun _ => x) a)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) => fun x : ℝ =>
    letI := Fintype.ofFinite ι
    a ⬝ᵥ (fun _ => x))) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (a : ι → ℝ) =>
    letI := Fintype.ofFinite ι
    fun x : ℝ => (fun _ => x) ⬝ᵥ a)) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (A : Matrix (Fin 2) ι ℝ) =>
    fun x : ℝ => @Matrix.mulVec (Fin 2) ι ℝ _ (Fintype.ofFinite ι)
      A (fun _ => x + 1))) 3
  assertAffine (← `(fun (ι : Type) [Finite ι] (A : Matrix ι (Fin 2) ℝ) =>
    fun x : ℝ => @Matrix.vecMul ι (Fin 2) ℝ _ (Fintype.ofFinite ι)
      (fun _ => x - 1) A)) 3


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

/-! An independent `Finite` proof let supplies the domain evidence directly,
without an ambient instance or an operation carrying a `Fintype`. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun (ι : Type) (evidence : Finite ι ∧ True) (i : ι) =>
    fun x : ι → ℝ =>
      let finiteEvidence : Finite ι := evidence.1
      x i + 1)) 3

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℕ → ℝ => x 0))
  assertUnsupported (← `(fun x : ℝ => fun _ : ℕ => x))
  let boundEvidence ← `(fun x : ℕ → ℝ => fun i : Empty =>
    let finiteEvidence : Finite ℕ := Empty.elim i
    x 0)
  unless (← sourceFiniteInstances (← elaborate boundEvidence)).isEmpty do
    throwError "binder-dependent finiteness evidence escaped its scope"
  assertUnsupported boundEvidence
  assertUnsupported (← `(fun x : ℕ → ℝ => fun i : Empty =>
    letI : Fintype ℕ := Empty.elim i
    @dotProduct ℕ ℝ inferInstance _ _ (fun _ => 0) x))


/-! Index instances that depend on the decision point remain unsupported. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : Fin 2 → ℝ =>
    @dotProduct (Fin 2) ℝ
      (if x 0 ≤ 0 then Fintype.ofFinite (Fin 2) else Fin.fintype 2) _ _ ![1, 2] x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ =>
    @Matrix.mulVec (Fin 2) (Fin 2) ℝ _
      (if x 0 ≤ 0 then Fintype.ofFinite (Fin 2) else Fin.fintype 2) !![1, 2; 3, 4] x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ =>
    @Matrix.vecMul (Fin 2) (Fin 2) ℝ _
      (if x 0 ≤ 0 then Fintype.ofFinite (Fin 2) else Fin.fintype 2) x !![1, 2; 3, 4]))

end PTranTest.Affine.FiniteIndexing
