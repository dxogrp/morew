import PTranTest.Atom.Support

/-!
# Atom recognition boundaries
-/

namespace PTranTest.Atom.Unsupported

open Lean Lean.Meta Lean.Elab.Term
open PTran PTran.Elab.Atom

/-! Recognition is intentionally bounded by typed heads and canonical instances. -/

noncomputable def equivalentExponential (x : ℝ) : ℝ := Real.exp (x + 0)

theorem equivalentExponential_eq (x : ℝ) :
    equivalentExponential x = Real.exp x := by
  simp [equivalentExponential]

namespace Shadowed

def exp (x : ℝ) : ℝ := x

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => exp x))

end Shadowed

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => exponentialAlias x))
  assertUnsupported (← `(fun x : ℝ => equivalentExponential x))
  assertUnsupported (← `(fun x : ℚ => x⁻¹))
  assertUnsupported (← `(fun x : ℤ => |x|))
  assertUnsupported (← `(fun x : ℤ => x⁺))
  assertUnsupported (← `(fun x y : ℕ => max x y))
  assertUnsupported (← `(fun x y : ℕ => min x y))
  assertUnsupported (← `(Real.exp))
  assertUnsupported (← `((Inv.inv : ℝ → ℝ)))
  assertUnsupported (← `((abs : ℝ → ℝ)))
  assertUnsupported (← `((posPart : ℝ → ℝ)))
  assertUnsupported (← `(fun x : ℝ => max x))
  assertUnsupported (← `(fun x : ℝ => min x))
  assertUnsupported (← `(fun [Inv ℝ] (x : ℝ) => x⁻¹))
  assertUnsupported (← `(fun [Max ℝ] (x y : ℝ) => max x y))
  assertUnsupported (← `(fun [Min ℝ] (x y : ℝ) => min x y))
  assertUnsupported (← `(fun [Lattice ℝ] (x : ℝ) => |x|))
  assertUnsupported (← `(fun [AddGroup ℝ] (x : ℝ) => |x|))
  assertUnsupported (← `(fun [PosPart ℝ] (x : ℝ) => x⁺))
  assertUnsupported (← `(fun [Lattice ℝ] (x : ℝ) => x⁺))
  assertUnsupported (← `(fun [SubNegMonoid ℝ] (x : ℝ) => x⁺))

private noncomputable abbrev canonicalInverse : Inv ℝ := inferInstance

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAtom (← `(fun x : ℝ => @Inv.inv ℝ canonicalInverse x)) .inv #[0]
  assertUnsupported (← `(fun x : ℝ => @Inv.inv ℝ ⟨fun _ => 0⟩ x))
  assertUnsupported (← `(fun x y : ℝ => @max ℝ ⟨fun a _ => a⟩ x y))
  assertUnsupported (← `(fun x y : ℝ => @min ℝ ⟨fun _ b => b⟩ x y))
  assertUnsupported (← `(fun x : ℝ => @posPart ℝ ⟨fun _ => 0⟩ x))
  assertUnsupported (← `(fun x : ℝ =>
    @abs ℝ (inferInstanceAs (Lattice (OrderDual ℝ))) Real.instAddGroup x))

run_cmd Lean.Elab.Command.liftTermElabM do
  let real := Lean.mkConst ``Real
  let instanceType ← elaborate (← `(Inv ℝ))
  let unresolvedInstance ← mkFreshExprMVar instanceType
  withLocalDeclD `x real fun x => do
    let expression := mkAppN (mkConst ``Inv.inv [Level.zero]) #[real, unresolvedInstance, x]
    if (← recognizeAtom? expression).isSome then
      throwError "recognized an unresolved inverse instance"
    if ← unresolvedInstance.mvarId!.isAssigned then
      throwError "recognition assigned an instance metavariable"
    withLetDecl `hiddenInstance instanceType unresolvedInstance fun hiddenInstance => do
      let expression := mkAppN (mkConst ``Inv.inv [Level.zero]) #[real, hiddenInstance, x]
      if expression.hasMVar then
        throwError "the hidden-instance regression no longer hides its metavariable"
      if (← recognizeAtom? expression).isSome then
        throwError "recognized an unresolved inverse instance hidden behind a local let"
      if ← unresolvedInstance.mvarId!.isAssigned then
        throwError "recognition assigned a hidden instance metavariable"

end PTranTest.Atom.Unsupported
