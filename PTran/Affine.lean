import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Certified affine constructions

Each construction retains both an affine map and its pointwise equality with
the original function. These algebraic helpers are independent of elaboration
and of the modeling surface language.
-/

namespace PTran.Affine

variable {X Y Z : Type*}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Y] [Module ℝ Y]
variable [AddCommGroup Z] [Module ℝ Z]

/-- An affine map together with its pointwise agreement with a function. -/
structure Certified (f : X → Y) where
  /-- The concrete affine map. -/
  map : X →ᵃ[ℝ] Y
  /-- The map agrees with the original function at every decision point. -/
  correct : ∀ x, map x = f x

namespace Certified

/-- A decision-independent constant is affine. -/
noncomputable def const (X : Type*) [AddCommGroup X] [Module ℝ X] (c : Y) :
    Certified (fun _ : X => c) where
  map := AffineMap.const ℝ X c
  correct _ := rfl

/-- The complete decision point is an affine function of itself. -/
noncomputable def id (X : Type*) [AddCommGroup X] [Module ℝ X] :
    Certified (fun x : X => x) where
  map := AffineMap.id ℝ X
  correct _ := rfl

/-- Transfer certification across a pointwise equality. -/
noncomputable def transport {f g : X → Y} (a : Certified f)
    (h : ∀ x, f x = g x) : Certified g where
  map := a.map
  correct x := (a.correct x).trans (h x)

/-- Add two certified affine functions. -/
noncomputable def add {f g : X → Y} (a : Certified f) (b : Certified g) :
    Certified (fun x => f x + g x) where
  map := a.map + b.map
  correct x := congrArg₂ (· + ·) (a.correct x) (b.correct x)

/-- Subtract two certified affine functions. -/
noncomputable def sub {f g : X → Y} (a : Certified f) (b : Certified g) :
    Certified (fun x => f x - g x) where
  map := a.map - b.map
  correct x := congrArg₂ (· - ·) (a.correct x) (b.correct x)

/-- Negate a certified affine function. -/
noncomputable def neg {f : X → Y} (a : Certified f) :
    Certified (fun x => -f x) where
  map := -a.map
  correct x := congrArg Neg.neg (a.correct x)

/-- Multiply by a decision-independent real scalar. -/
noncomputable def realSMul {f : X → Y} (c : ℝ) (a : Certified f) :
    Certified (fun x => c • f x) where
  map := c • a.map
  correct x := congrArg (c • ·) (a.correct x)

/-- Multiply by a decision-independent natural scalar. -/
noncomputable def natSMul {f : X → Y} (n : ℕ) (a : Certified f) :
    Certified (fun x => n • f x) where
  map := n • a.map
  correct x := congrArg (n • ·) (a.correct x)

/-- Scale a fixed vector by an affine real-valued function. -/
noncomputable def smulConst {f : X → ℝ} (a : Certified f) (c : Y) :
    Certified (fun x => f x • c) where
  map := ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c).toAffineMap.comp a.map
  correct x := congrArg (· • c) (a.correct x)

/-- Multiply a scalar affine function by a constant on the left. -/
noncomputable def mulConstLeft {f : X → ℝ} (c : ℝ) (a : Certified f) :
    Certified (fun x => c * f x) :=
  realSMul c a

/-- Multiply a scalar affine function by a constant on the right. -/
noncomputable def mulConstRight {f : X → ℝ} (a : Certified f) (c : ℝ) :
    Certified (fun x => f x * c) :=
  smulConst a c

/-- Divide by a certified nonzero constant.

The nonzero witness records the reifier's supported fragment, even though
totalized real division would also define an affine function at zero.
-/
noncomputable def divConst {f : X → ℝ} (a : Certified f) (c : ℝ) (_h : c ≠ 0) :
    Certified (fun x => f x / c) where
  map := (mulConstRight a c⁻¹).map
  correct x := by
    simpa only [div_eq_mul_inv] using (mulConstRight a c⁻¹).correct x

/-- The zeroth power of a scalar affine function is constant. -/
noncomputable def powZero {f : X → ℝ} (_a : Certified f) :
    Certified (fun x => f x ^ (0 : ℕ)) where
  map := AffineMap.const ℝ X 1
  correct x := (pow_zero (f x)).symm

/-- The zeroth power is constant without requiring its base to be affine. -/
noncomputable def powZeroSource (f : X → ℝ) :
    Certified (fun x => f x ^ (0 : ℕ)) where
  map := AffineMap.const ℝ X 1
  correct x := (pow_zero (f x)).symm

/-- The first power preserves a scalar affine function. -/
noncomputable def powOne {f : X → ℝ} (a : Certified f) :
    Certified (fun x => f x ^ (1 : ℕ)) where
  map := a.map
  correct x := (a.correct x).trans (pow_one (f x)).symm

/-- Pair two certified affine functions. -/
noncomputable def pair {f : X → Y} {g : X → Z}
    (a : Certified f) (b : Certified g) :
    Certified (fun x => (f x, g x)) where
  map := a.map.prod b.map
  correct x := congrArg₂ Prod.mk (a.correct x) (b.correct x)

/-- Project the first component of a certified product-valued function. -/
noncomputable def fst {f : X → Y × Z} (a : Certified f) :
    Certified (fun x => (f x).1) where
  map := AffineMap.fst.comp a.map
  correct x := congrArg Prod.fst (a.correct x)

/-- Project the second component of a certified product-valued function. -/
noncomputable def snd {f : X → Y × Z} (a : Certified f) :
    Certified (fun x => (f x).2) where
  map := AffineMap.snd.comp a.map
  correct x := congrArg Prod.snd (a.correct x)

/-- Evaluate a certified vector-valued function at a fixed index. -/
noncomputable def eval {ι : Type*} {f : X → ι → Y} (a : Certified f) (i : ι) :
    Certified (fun x => f x i) where
  map := (AffineMap.proj i).comp a.map
  correct x := congrFun (a.correct x) i

/-- Assemble a family of affine functions into a vector-valued function. -/
noncomputable def pi {ι : Type*} {f : ι → X → Y}
    (a : ∀ i, Certified (f i)) : Certified (fun x i => f i x) where
  map := AffineMap.pi fun i => (a i).map
  correct x := funext fun i => (a i).correct x

/-- Construct a finite vector by prepending one affine coordinate. -/
noncomputable def vecCons {n : ℕ} {f : X → Y} {g : X → Fin n → Y}
    (a : Certified f) (b : Certified g) :
    Certified (fun x => Matrix.vecCons (f x) (g x)) where
  map := AffineMap.pi fun i => Fin.cases a.map (fun j => (eval b j).map) i
  correct x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact a.correct x
    · exact congrFun (b.correct x) j

/-- The empty real vector is constant. -/
noncomputable def vecEmpty (X : Type*) [AddCommGroup X] [Module ℝ X] :
    Certified (fun _ : X => (Matrix.vecEmpty : Fin 0 → ℝ)) :=
  const X Matrix.vecEmpty

/-- Equip an affine finite real vector with its Euclidean norm. -/
noncomputable def toEuclidean {n : ℕ} {f : X → Fin n → ℝ} (a : Certified f) :
    Certified (fun x => WithLp.toLp 2 (f x)) where
  map := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toAffineEquiv.toAffineMap.comp a.map
  correct x := congrArg (WithLp.toLp 2) (a.correct x)

/-- Forget the norm of a Euclidean affine vector to obtain its coordinates. -/
noncomputable def ofEuclidean {n : ℕ} {f : X → EuclideanSpace ℝ (Fin n)}
    (a : Certified f) : Certified (fun x => WithLp.ofLp (f x)) where
  map := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toAffineEquiv.toAffineMap.comp a.map
  correct x := congrArg WithLp.ofLp (a.correct x)

/-- Sum an indexed family of certified functions over a fixed finite set. -/
noncomputable def sum {ι : Type*} {f : ι → X → Y}
    (s : Finset ι) (a : ∀ i, Certified (f i)) :
    Certified (fun x => ∑ i ∈ s, f i x) where
  map := ∑ i ∈ s, (a i).map
  correct x := by
    classical
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, AffineMap.coe_add, Pi.add_apply]
        exact congrArg₂ (· + ·) ((a i).correct x) ih

/-- Take a dot product with a fixed vector on the left. -/
noncomputable def dotConstLeft {ι : Type*} [Fintype ι] {f : X → ι → ℝ}
    (c : ι → ℝ) (a : Certified f) :
    Certified (fun x => dotProduct c (f x)) where
  map := (dotProductBilin ℝ ℝ c).toAffineMap.comp a.map
  correct x := congrArg (dotProduct c) (a.correct x)

/-- Take a dot product with a fixed vector on the right. -/
noncomputable def dotConstRight {ι : Type*} [Fintype ι] {f : X → ι → ℝ}
    (a : Certified f) (c : ι → ℝ) :
    Certified (fun x => dotProduct (f x) c) where
  map := ((dotProductBilin ℝ ℝ).flip c).toAffineMap.comp a.map
  correct x := congrArg (fun v => dotProduct v c) (a.correct x)

/-- Multiply an affine vector by a fixed matrix. -/
noncomputable def mulVec {m n : Type*} [Fintype n] {f : X → n → ℝ}
    (A : Matrix m n ℝ) (a : Certified f) :
    Certified (fun x => A.mulVec (f x)) where
  map := A.mulVecLin.toAffineMap.comp a.map
  correct x := congrArg A.mulVec (a.correct x)

/-- Multiply an affine row vector by a fixed matrix. -/
noncomputable def vecMul {m n : Type*} [Fintype m] {f : X → m → ℝ}
    (a : Certified f) (A : Matrix m n ℝ) :
    Certified (fun x => Matrix.vecMul (f x) A) where
  map := A.vecMulLinear.toAffineMap.comp a.map
  correct x := congrArg (fun v => Matrix.vecMul v A) (a.correct x)

end Certified
end PTran.Affine
