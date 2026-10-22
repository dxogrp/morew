import PTran.Elab.Affine

/-!
# Checked conjunction decomposition

Flatten inspectable conjunctions while retaining their exact equivalence and
the local evidence needed by each resulting predicate. Atomic predicates are
left intact for the caller's recognizer.
-/

namespace PTran.Elab.Conic

open Lean Lean.Meta

namespace Decomposition

/-- The conjunction convention shared by typed problem presentations. -/
def conjunction : List Expr → Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: rest => mkApp2 (mkConst ``And) p (conjunction rest)

private theorem emptyLeft (p : Prop) : True ∧ p ↔ p :=
  ⟨fun h => h.2, fun h => ⟨True.intro, h⟩⟩

private theorem emptyRight (p : Prop) : p ∧ True ↔ p :=
  ⟨fun h => h.1, fun h => ⟨h, True.intro⟩⟩

private theorem appendHead (p q r s : Prop) (h : q ∧ r ↔ s) :
    (p ∧ q) ∧ r ↔ p ∧ s :=
  and_assoc.trans (and_congr Iff.rfl h)

/-- Join two normalized conjunctions without losing their equivalence. -/
partial def appendIff (left right : List Expr) : MetaM Expr := do
  match left, right with
  | [], _ => mkAppM ``emptyLeft #[conjunction right]
  | _, [] => mkAppM ``emptyRight #[conjunction left]
  | [_], _ => pure <| mkApp (mkConst ``Iff.rfl) (conjunction (left ++ right))
  | p :: rest, _ =>
      mkAppM ``appendHead #[p, conjunction rest, conjunction right,
        conjunction (rest ++ right), ← appendIff rest right]

/-- Split a proposition using only the supplied structural reduction. Local
lets remain attached to every leaf and to the decomposition proof. -/
partial def split (body : Expr) (reduce : Expr → MetaM Expr) :
    MetaM (List Expr × Expr) := do
  let body ← reduce body
  if let .letE name type value rest _ := body then
    return ← withLetDecl name type value fun binding => do
      let (rows, proof) ← split (rest.instantiate1 binding) reduce
      let rows ← rows.mapM fun row =>
        mkLetFVars #[binding] row (usedLetOnly := false) (generalizeNondepLet := false)
      let proof ← mkLetFVars #[binding] proof
        (usedLetOnly := false) (generalizeNondepLet := false)
      return (rows, proof)
  if body.isConstOf ``True then
    return ([], mkApp (mkConst ``Iff.rfl) body)
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    let (left, hl) ← split args[0]! reduce
    let (right, hr) ← split args[1]! reduce
    let split ← mkAppM ``and_congr #[hl, hr]
    let combined ← mkAppM ``Iff.trans #[split, ← appendIff left right]
    return (left ++ right, combined)
  return ([body], mkApp (mkConst ``Iff.rfl) body)

end Decomposition

/-- Decompose a predicate into ordered atomic predicates and a checked proof
of its equivalence with their conjunction. `True` contributes no leaves;
unsupported atomic heads remain available for a more specific diagnostic. -/
def decomposePredicate (predicate : Expr) : MetaM (Array Expr × Expr) := do
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | throwError "expected a predicate on the decision space"
  unless codomain == mkSort .zero do
    throwError "expected a predicate on the decision space"
  withLocalDeclD `point domain fun point => do
    let (bodies, proof) ← Decomposition.split (mkApp predicate point)
      (fun body => Affine.reduceStructure body (preserveLets := true))
    let predicates ← bodies.toArray.mapM (mkLambdaFVars #[point])
    let proof ← instantiateMVars (← mkLambdaFVars #[point] proof)
    let expected ← mkForallFVars #[point] (mkApp2 (mkConst ``Iff)
      (mkApp predicate point) (Decomposition.conjunction bodies))
    unless ← isDefEq (← inferType proof) expected do
      throwError "constraint decomposition does not match its source predicate"
    if proof.hasMVar then
      throwError "constraint decomposition contains unresolved metavariables"
    checkWithKernel proof
    return (predicates, proof)

end PTran.Elab.Conic
