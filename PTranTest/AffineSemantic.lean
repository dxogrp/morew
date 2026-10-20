import PTran.Elab.Affine.Space
import Lean.Meta.Check

/-!
# Canonical structures in affine certificates

Certification must use the standard real vector-space structures even when
the elaboration context supplies other algebraic instances. Temporary local
instances must not escape into the resulting proof terms.
-/

namespace PTranTest.AffineSemantic

open Lean Lean.Meta Lean.Elab.Command Lean.Elab.Term
open PTran.Elab.Affine.Space

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

end PTranTest.AffineSemantic
