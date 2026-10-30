/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Affine.Support
import Morew.Affine.SymmetricMatrix
import Morew.Elab.Affine.Space

/-! Ordinary matrix notation, affine matrix operations, and exact symmetric restriction. -/

namespace MorewTest.Affine.MatrixReification

open Lean Lean.Meta Lean.Elab.Term
open MorewTest.Affine Morew.Conic
open scoped Matrix BigOperators

private abbrev SymmetricAlias (n : Nat) := SymmetricMatrix n
private def matrixHelper (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x, x + 1; x + 1, 2 * x]
private def scalarHelper (x : ℝ) : ℝ := 2 * x + 1

/-! Native matrix operations remain available without helper expansion. -/

set_option morew.affine.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => !![x, 2 * x; -x, x + 1]))
  assertAffine (← `(fun x : ℝ => (!![x] : Matrix (Fin 1) (Fin 1) ℝ)))
  assertAffine (← `(fun (m n : Nat) => fun x : ℝ =>
    Matrix.of (fun (i : Fin m) (j : Fin n) => x + (i.val : ℝ) - (j.val : ℝ)))) 2
  assertAffine (← `(fun (m n : Nat) (C : Matrix (Fin m) (Fin n) ℝ) =>
    fun A : Matrix (Fin m) (Fin n) ℝ => -(2 : ℝ) • A + C - A)) 3
  assertAffine (← `(fun (m n : Nat) (C : Matrix (Fin m) (Fin n) ℝ) =>
    fun x : ℝ => (x + 1) • C)) 3
  assertAffine (← `(fun n : Nat => fun x : Fin n → ℝ => Matrix.diagonal x)) 1
  assertAffine (← `(fun (m n : Nat) => fun A : Matrix (Fin m) (Fin n) ℝ => Aᵀ)) 2
  assertAffine (← `(fun A : Matrix (Fin 0) (Fin 2) ℝ => Aᵀ))
  assertAffine (← `(fun (m n : Nat) (C : Matrix (Fin m) (Fin n) ℝ) =>
    fun A : Matrix (Fin m) (Fin n) ℝ => A.submatrix id id)) 3
  assertAffine (← `(fun A : Matrix (Fin 2) (Fin 2) ℝ =>
    Matrix.reindex (Equiv.refl _) (Equiv.refl _) A))
  assertAffine (← `(fun (m n : Nat) =>
    fun p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin n) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ =>
    Matrix.fromBlocks p.1 p.2.1 p.2.2.1 p.2.2.2)) 2
  assertAffine (← `(fun (m n : Nat) =>
    fun p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin n) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ =>
    fromBlocksFin p.1 p.2.1 p.2.2.1 p.2.2.2)) 2
  assertAffine (← `(fun (l m n : Nat) (C : Matrix (Fin l) (Fin m) ℝ) =>
    fun A : Matrix (Fin m) (Fin n) ℝ => C * A)) 4
  assertAffine (← `(fun (l m n : Nat) (C : Matrix (Fin m) (Fin n) ℝ) =>
    fun A : Matrix (Fin l) (Fin m) ℝ => A * C)) 4
  assertAffine (← `(fun C : Matrix (Fin 2) (Fin 0) ℝ =>
    fun A : Matrix (Fin 0) (Fin 3) ℝ => C * A)) 1
  assertAffine (← `(fun (m n : Nat) (C : Fin m → Matrix (Fin n) (Fin n) ℝ) =>
    fun x : Fin m → ℝ => ∑ i, x i • C i)) 3

/-! Source enumerations and fixed reindexing are retained exactly. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun C : Matrix (Fin 2) (Fin 3) ℝ =>
    fun A : Matrix (Fin 4) (Fin 2) ℝ =>
    letI := Fintype.ofFinite (Fin 2)
    A * C)) 1
  assertAffine (← `(fun C : Matrix (Fin 3) (Fin 2) ℝ =>
    fun A : Matrix (Fin 2) (Fin 4) ℝ =>
    letI := Fintype.ofFinite (Fin 2)
    C * A)) 1
  assertAffine (← `(fun (ι : Type) (e : Fin 2 ≃ ι) (C : Matrix ι (Fin 3) ℝ) =>
    fun A : Matrix (Fin 4) ι ℝ =>
    letI := Fintype.ofEquiv (Fin 2) e
    A * C)) 3
  assertAffine (← `(fun (r : Fin 3 → Fin 2) (c : Fin 4 → Fin 5) =>
    fun A : Matrix (Fin 2) (Fin 5) ℝ => A.submatrix r c)) 2
  assertAffine (← `(fun A : Matrix (Fin 2) (Fin 2) ℝ =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A A A A)))

/-! Symmetric values retain their entries and support the same canonical algebra. -/

set_option morew.affine.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun n : Nat => fun A : SymmetricMatrix n => A)) 1
  assertAffine (← `(fun n : Nat => fun A : SymmetricAlias n => A.toMatrix)) 1
  assertAffine (← `(fun A : SymmetricMatrix 2 => A.val 0 1))
  assertAffine (← `(fun A : SymmetricMatrix 2 => A.toMatrix 0 1))
  assertAffine (← `(fun p : ℝ × SymmetricAlias 2 => p.1 + p.2.toMatrix 0 1))
  assertAffine (← `(fun A : SymmetricMatrix 2 => 2 • A - (-A)))
  assertAffine (← `(fun n : Nat => fun x : Fin n → ℝ =>
    SymmetricMatrix.ofMatrix (Matrix.diagonal x) (Matrix.isSymm_diagonal x))) 1
  assertAffine (← `(fun (n : Nat) (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ x, (F x).IsSymm) => fun _ : ℝ => SymmetricMatrix.ofMatrix (F 0) (h 0))) 3
  assertAffine (← `(fun [AddCommGroup (SymmetricMatrix 2)] =>
    fun A : SymmetricMatrix 2 => A)) 1

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => matrixHelper x))
  assertAffine (← `(fun x : ℝ => !![scalarHelper x, x; x, scalarHelper x]))
  assertAffine (← `(fun x : ℝ => (matrixHelper x)ᵀ))
  assertAffine (← `(fun x : Fin 2 → ℝ =>
    SymmetricMatrix.ofMatrix (Matrix.diagonal (fun i => scalarHelper (x i)))
      (Matrix.isSymm_diagonal _)))

/-! The restriction certificate proves equality for every entry, including n=0. -/

example {X : Type*} [AddCommGroup X] [Module ℝ X] {n : Nat}
    (f : X →ᵃ[ℝ] Matrix (Fin n) (Fin n) ℝ) (h : ∀ x, (f x).IsSymm)
    (x : X) (i j : Fin n) :
    (Morew.Affine.restrictSymmetricMatrix f h x).toMatrix i j = f x i j := rfl

/-! Nonlinear entries, bilinear matrix products and altered operation instances fail. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => !![x * x, x; x, 1])) 0 (some ``HMul.hMul)
  assertUnsupported (← `(fun x : ℝ => !![Real.exp x, x; x, 1])) 0 (some ``Real.exp)
  assertUnsupported (← `(fun A : Matrix (Fin 2) (Fin 2) ℝ => A * A))
  assertUnsupported (← `(fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ => p.1 • p.2))
  assertUnsupported (← `(fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
    p.2.submatrix (fun i => if p.1 ≤ 0 then i else 0) id))
  assertUnsupported (← `(fun A : Matrix (Fin 2) (Fin 2) ℝ =>
    @HMul.hMul _ _ _ ⟨fun B C => B + C⟩ A (1 : Matrix (Fin 2) (Fin 2) ℝ)))
  assertUnsupported (← `(fun A : Matrix (Fin 2) (Fin 2) ℝ =>
    letI := if A 0 0 ≤ 0 then Fintype.ofFinite (Fin 2) else Fin.fintype 2
    A * (1 : Matrix (Fin 2) (Fin 2) ℝ)))
  assertUnsupported (← `(fun x : {x : ℝ // 0 ≤ x} => x.val))

/-! A placeholder cannot supply symmetry, including through a hidden proof let
or the constant-map fast path. These malformed terms never become declarations. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate (← `(fun h : (Matrix.diagonal ![(1 : ℝ)]).IsSymm =>
    fun _ : ℝ => SymmetricMatrix.ofMatrix (Matrix.diagonal ![1]) h))
  lambdaBoundedTelescope expression 1 fun parameters source => do
    let proofType ← inferType parameters[0]!
    for synthetic in [true, false] do
      let placeholder ← mkSorry proofType synthetic
      let checkRejected := fun bad => do
        match ← Morew.Elab.Affine.reifyAffine bad with
        | .ok _ => throwError "affine matrix accepted a placeholder symmetry proof"
        | .error _ => pure ()
      checkRejected (source.replaceFVars parameters #[placeholder])
      withLetDecl `hiddenSymmetry proofType placeholder fun binding => do
        checkRejected (source.replaceFVars parameters #[binding])

end MorewTest.Affine.MatrixReification
