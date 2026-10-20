import PTranTest.Affine.Support
import PTran.Elab.Affine.Space

/-!
# Canonical structures for affine maps and rows

Unrelated ambient instances must not affect certification. Source operations
that actually change the arithmetic or order remain unsupported, and temporary
canonical instances must not escape into certificates.
-/

namespace PTranTest.Affine.CanonicalInstances

open Lean Lean.Meta Lean.Elab.Term
open PTran.Elab.Affine PTranTest.Affine Matrix
open Lean.Elab.Command PTran.Elab.Affine.Space

private noncomputable abbrev canonicalScalarLE : LE ℝ := inferInstance
private noncomputable abbrev canonicalVectorLE (n : ℕ) : LE (Fin n → ℝ) := inferInstance
private abbrev GroupedAlias := (Matrix (Fin 2) (Fin 3) ℝ × ℝ) × ℝ

private partial def completeInstances (term : Expr) : MetaM Expr := do
  let type ← whnf (← inferType term)
  if let .forallE _ domain _ .instImplicit := type then
    completeInstances (mkApp term (← synthInstance domain))
  else
    pure term
private def canonicalIdentity (type : Expr) : MetaM Expr :=
  withCanonicalSpaces #[type] do
    completeInstances (← mkAppM ``PTran.Affine.Certified.id #[type])

run_cmd liftTermElabM do
  let real := Lean.mkConst ``Real
  let nested ← elabTerm (← `(ℝ × (Fin 2 → ℝ))) none
  let matrix ← elabTerm (← `(Matrix (Fin 2) (Fin 3) ℝ)) none
  synthesizeSyntheticMVarsNoPostponing
  for type in #[real, nested, matrix] do
    let type ← instantiateMVars type
    let expected ← completeInstances (← mkAppM ``PTran.Affine.Certified.id #[type])
    let (canonicalGroup, canonicalModule) ← canonicalSpace type
    let groupType ← inferType canonicalGroup
    withLocalDecl `ambientGroup .instImplicit groupType fun ambientGroup => do
      let ambientMonoid ← mkAppOptM ``AddCommGroup.toAddCommMonoid
        #[some type, some ambientGroup]
      let canonicalModuleType ← inferType canonicalModule
      let ambientModuleType := mkAppN canonicalModuleType.getAppFn
        (canonicalModuleType.getAppArgs.set! 3 ambientMonoid)
      withLocalDecl `ambientModule .instImplicit ambientModuleType fun ambientModule => do
        let certified ← canonicalIdentity type
        check certified
        if certified.containsFVar ambientGroup.fvarId! ||
            certified.containsFVar ambientModule.fvarId! then
          throwError "affine certification captured an ambient algebraic instance"
        unless ← isDefEq certified expected do
          throwError "affine certification did not use the standard structures"
    let certified ← canonicalIdentity type
    check certified
    if certified.hasFVar || certified.hasMVar then
      throwError "a temporary canonical instance escaped its scope"
  withLocalDeclD `A matrix fun matrixValue => do
    let certified ← withCanonicalSpaces #[real, matrix] <|
      mkAppM ``PTran.Affine.Certified.const #[real, matrixValue]
    check certified

run_cmd liftTermElabM do
  withLocalDeclD `I (mkSort (.succ .zero)) fun index => do
    let finiteType ← mkAppM ``Fintype #[index]
    withLocalDecl `finite .instImplicit finiteType fun finite => do
      let vector ← mkArrow index (Lean.mkConst ``Real)
      let preserved ← withCanonicalSpaces #[vector] <| synthInstance finiteType
      unless preserved == finite do
        throwError "canonical spaces changed the local finite index instance"


/-! Unused ambient instances do not change the arithmetic in the source. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun [AddCommGroup ℝ] => fun x : ℝ => x)) 1
  assertAffine (← `(fun [AddCommGroup ℝ] => fun _ : ℝ => (2 : ℝ))) 1
  assertAffine (← `(fun [AddCommGroup ℝ] => fun x : ℝ => x + x)) 1
  assertAffine (← `(fun [Module ℝ ℝ] => fun x : ℝ => x)) 1
  assertAffine (← `(fun [Module ℝ ℝ] => fun _ : ℝ => (2 : ℝ))) 1
  assertAffine (← `(fun [Module ℝ (Fin 2 → ℝ)] =>
    fun x : Fin 2 → ℝ => (2 : ℝ) • x)) 1
  assertAffine (← `(fun [AddCommGroup ℝ] [Module ℝ ℝ] => fun x : ℝ => x)) 2
  assertAffine (← `(fun [Zero ℝ] => fun x : ℝ => x / 2)) 1
  assertAffine (← `(fun [OfNat ℝ 0] => fun x : ℝ => x / 2)) 1
  assertAffine (← `(fun c : ℝ => fun (_ : c ≠ 0) =>
    fun [Zero ℝ] => fun x : ℝ => x / c)) 3
  assertAffine (← `(fun c : ℝ => fun (_ : c ≠ 0) =>
    fun [OfNat ℝ 0] => fun x : ℝ => x / c)) 3


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
  assertRowUnsupported (← `(fun x : ℝ => @LE.le ℝ ⟨fun a b => a + 1 ≤ b⟩ x 3))
  assertRowUnsupported (← `(fun x : Fin 2 → ℝ =>
    @LE.le (Fin 2 → ℝ) ⟨fun a b => a 0 ≤ b 1⟩ x (fun _ => 3)))
  assertRowUnsupported (← `(fun x : ℝ =>
    @HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a * b⟩ x x ≤ 3))

end PTranTest.Affine.CanonicalInstances
