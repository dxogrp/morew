import PTranTest.Affine.Support
import PTran.Elab.Conic.Space

/-!
# Affine coordinates of Euclidean decision spaces

The L2 type wrapper preserves affine structure while its ordinary coordinates
remain distinct from the existing L∞ function space. Certificates retain the
canonical operations even when unrelated local instances are available.
-/

namespace PTranTest.Conic.EuclideanAffine

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open PTranTest.Affine
open scoped ENNReal

private abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Nested (n : ℕ) := (Fin 2 → Vector n) × ℝ

run_cmd liftTermElabM do
  assertAffine (← `(fun n : ℕ => fun x : Vector n => x)) 1
  assertAffine (← `(fun n : ℕ => fun x : Fin n → ℝ => WithLp.toLp 2 x)) 1
  assertAffine (← `(fun n : ℕ => fun x : Vector n => WithLp.ofLp x)) 1
  assertAffine (← `(fun (n : ℕ) (i : Fin n) => fun x : Vector n => x i)) 2
  assertAffine (← `(fun (n : ℕ) (i : Fin n) (c : Vector n) =>
    fun x : Vector n => (2 : ℝ) • x - c + x)) 3
  assertAffine (← `(fun (n : ℕ) (i : Fin n) =>
    fun x : Nested n => ((x.1 0) i + x.2, WithLp.ofLp (x.1 1)))) 2
  assertAffine (← `(fun (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
      (b : Fin m → ℝ) => fun x : Vector n =>
    WithLp.toLp 2 (A.mulVec (WithLp.ofLp x) + b))) 4
  assertAffine (← `(fun x : Vector 0 => WithLp.ofLp x))
  assertAffine (← `(fun x : Vector 1 => ![x 0, (2 : ℝ) * x 0 + 1]))
  assertAffine (← `(fun x : ℝ => WithLp.toLp 2 ![x, x + 1]))
  assertAffine (← `(fun x : Vector 2 =>
    let coords := WithLp.ofLp x
    WithLp.toLp 2 (fun i => coords i + 1)))

/-! Existing affine rows accept Euclidean decision domains without changing
which norm is attached to ordinary function spaces. -/

run_cmd liftTermElabM do
  assertRow (← `(fun (n : ℕ) (i : Fin n) => fun x : Vector n => x i ≤ 3)) 2
  assertRow (← `(fun n : ℕ => fun x : Vector n =>
    WithLp.ofLp x ≤ fun _ => (1 : ℝ))) 1
  assertRow (← `(fun (n : ℕ) (i : Fin n) =>
    fun x : Nested n => (x.1 0) i = x.2)) 2

/-! Local unrelated algebraic or normed structures must not leak into proofs. -/

run_cmd liftTermElabM do
  assertAffine (← `(fun [AddCommGroup (Vector 2)] => fun x : Vector 2 => x)) 1
  assertAffine (← `(fun [Module ℝ (Vector 2)] => fun x : Vector 2 => WithLp.ofLp x)) 1
  assertAffine (← `(fun [AddCommGroup (Vector 2)] [Module ℝ (Vector 2)] =>
    fun x : Vector 2 => x 0)) 2
  assertRow (← `(fun [NormedAddCommGroup (Vector 2)] [NormedSpace ℝ (Vector 2)] =>
    fun x : Vector 2 => x 0 ≤ 3)) 2
  assertRow (← `(fun [NormedAddCommGroup (Nested 2)] [NormedSpace ℝ (Nested 2)] =>
    fun x : Nested 2 => (x.1 0) 0 ≤ x.2)) 2

/-! A changed operation, nonlinear coordinate, or unsupported Lp wrapper must
be rejected instead of being silently interpreted with Euclidean operations. -/

run_cmd liftTermElabM do
  assertUnsupported (← `(fun x : Vector 2 =>
    @HAdd.hAdd (Vector 2) (Vector 2) (Vector 2) ⟨fun a _ => (a 0) • a⟩ x x))
  assertUnsupported (← `(fun x : Vector 2 =>
    @HSMul.hSMul ℝ (Vector 2) (Vector 2) ⟨fun _ a => (a 0) • a⟩ 2 x))
  assertUnsupported (← `(fun x : Vector 2 => WithLp.toLp 2 ![(x 0)^2]))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => WithLp.toLp 1 x))
  assertUnsupported (← `(fun x : Fin 2 → ℝ => WithLp.toLp ∞ x))
  assertUnsupported (← `(fun x : EuclideanSpace ℝ Bool => WithLp.ofLp x))

/-! Cone-coordinate certification supplies canonical structures for tuples,
including all nested target components, and leaves no temporary free variables. -/

run_cmd liftTermElabM do
  let domain ← elaborate (← `(Vector 2))
  let target ← elaborate (← `(ℝ × ℝ × (Fin 2 → ℝ)))
  let (finite, reflexive) ← PTran.Elab.Conic.Space.withCanonicalConeSpaces domain target do
    let obligation ← mkAppOptM ``FiniteDimensional
      #[some (mkConst ``Real), some target, none, none, none]
    return (← synthInstance obligation, ← mkEqRefl target)
  for proof in #[finite, reflexive] do
    checkWithKernel proof
    if proof.hasFVar || proof.hasMVar then
      throwError "a temporary cone-space instance escaped its scope"

end PTranTest.Conic.EuclideanAffine
