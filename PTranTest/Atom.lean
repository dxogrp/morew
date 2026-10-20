import PTran

/-!
# Native atom recognition

Recognition identifies supported mathematical operations without changing expressions,
presentation metadata, or the language accepted by the modeling frontend.
-/

namespace PTranTest.Atom

open Lean Lean.Meta Lean.Elab.Term
open PTran PTran.Elab.Atom

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

private def assertAtom (term : TSyntax `term) (kind : AtomKind)
    (operandIndices : Array Nat) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaTelescope expression fun binders body => do
    let some atom ← recognizeAtom? body
      | throwError "expected an atom in {body}"
    unless atom.kind == kind do
      throwError "recognized the wrong operation in {body}"
    unless atom.original == body do
      throwError "recognition changed the original expression"
    unless atom.operands == operandIndices.map (binders[·]!) do
      throwError "recognition changed the operands or their order in {body}"

private def assertUnsupported (term : TSyntax `term) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaTelescope expression fun _ body => do
    if (← recognizeAtom? body).isSome then
      throwError "unexpectedly recognized unsupported expression {body}"

/-! Native notation, qualified names, and ordinary namespace resolution. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAtom (← `(fun x : ℝ => Real.exp x)) .exp #[0]
  assertAtom (← `(fun x : ℝ => Real.log x)) .log #[0]
  assertAtom (← `(fun x : ℝ => Real.sqrt x)) .sqrt #[0]
  assertAtom (← `(fun x : ℝ => x⁻¹)) .inv #[0]
  assertAtom (← `(fun x : ℝ => Inv.inv x)) .inv #[0]
  assertAtom (← `(fun x : ℝ => |x|)) .abs #[0]
  assertAtom (← `(fun x : ℝ => abs x)) .abs #[0]
  assertAtom (← `(fun x : ℝ => x⁺)) .pos #[0]
  assertAtom (← `(fun x : ℝ => posPart x)) .pos #[0]
  assertAtom (← `(fun x y : ℝ => max x y)) .maximum #[0, 1]
  assertAtom (← `(fun x y : ℝ => min y x)) .minimum #[1, 0]

open Real in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAtom (← `(fun x : ℝ => exp x)) .exp #[0]
  assertAtom (← `(fun x : ℝ => log x)) .log #[0]
  assertAtom (← `(fun x : ℝ => sqrt x)) .sqrt #[0]

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← elaborate (← `(fun x : ℝ => Real.log (Real.exp x)))
  lambdaTelescope expression fun binders body => do
    let some outer ← recognizeAtom? body
      | throwError "did not recognize a logarithm with a nested operand"
    unless outer.kind == .log && outer.original == body && outer.operands.size == 1 do
      throwError "changed the outer logarithm"
    let some inner ← recognizeAtom? outer.operands[0]!
      | throwError "did not preserve the nested exponential"
    unless inner.kind == .exp && inner.operands == binders do
      throwError "changed the nested exponential operand"

  let expression ← elaborate (← `(fun x : ℝ => max x 0))
  lambdaTelescope expression fun binders body => do
    let some atom ← recognizeAtom? body
      | throwError "did not recognize maximum with zero"
    unless atom.kind == .maximum && atom.operands.size == 2 &&
        atom.operands[0]! == binders[0]! do
      throwError "reclassified maximum with zero as positive part"
    unless ← isDefEq atom.operands[1]! (← mkNumeral (mkConst ``Real) 0) do
      throwError "changed the second maximum operand"

  withLocalDeclD `x (mkConst ``Real) fun x => do
    let operand := mkMData {} x
    let function := mkMData {} (Lean.mkConst ``Real.exp)
    let expression := mkMData {} (mkApp function operand)
    let some atom ← recognizeAtom? expression
      | throwError "application metadata prevented recognition"
    unless atom.kind == .exp && atom.original == expression && atom.operands == #[operand] do
      throwError "recognition changed application or operand metadata"

/-! Recognition is intentionally bounded by typed heads and canonical instances. -/

noncomputable abbrev exponentialAlias (x : ℝ) : ℝ := Real.exp x

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

/-! A consuming rule owns domain conditions, independently of recognition. -/

private def mockLogConsumer (expression : Expr) (evidence? : Option Expr := none) :
    MetaM Expr := do
  let some atom ← recognizeAtom? expression
    | throwError "mock logarithm consumer requires a recognized operation"
  unless atom.kind == .log do
    throwError "mock logarithm consumer requires a logarithm"
  let obligation ← mkLT (← mkNumeral (mkConst ``Real) 0) atom.operands[0]!
  let proof ← mkFreshExprMVar obligation
  if let some evidence := evidence? then
    unless ← isDefEq (← inferType evidence) obligation do
      throwError "provided evidence does not establish logarithm positivity"
    proof.mvarId!.assign evidence
  return proof

open Real in
run_cmd Lean.Elab.Command.liftTermElabM do
  let qualified ← elaborate (← `(fun x : ℝ => Real.log x))
  let unqualified ← elaborate (← `(fun x : ℝ => log x))
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let first ← mockLogConsumer (qualified.beta #[x])
    let second ← mockLogConsumer (unqualified.beta #[x])
    let expected ← mkLT (← mkNumeral (mkConst ``Real) 0) x
    unless ← isDefEq (← inferType first) expected do
      throwError "qualified logarithm has the wrong domain obligation"
    unless ← isDefEq (← inferType second) expected do
      throwError "unqualified logarithm has the wrong domain obligation"
    if (← first.mvarId!.isAssigned) || (← second.mvarId!.isAssigned) then
      throwError "missing domain evidence was silently supplied"
    withLocalDeclD `positive expected fun positive => do
      for expression in #[qualified.beta #[x], unqualified.beta #[x]] do
        let proof ← mockLogConsumer expression (some positive)
        unless (← instantiateMVars proof) == positive do
          throwError "the logarithm consumer did not use the supplied evidence"

/-! Ordinary custom functions remain valid in models and proofs. -/

noncomputable section

def customLoss (x : ℝ) : ℝ := x ^ 2 + x

def customProblem :=
  problem (x : ℝ)
    minimize customLoss x

example (x : ℝ) : customProblem.objective x = x ^ 2 + x := rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  assertUnsupported (← `(fun x : ℝ => customLoss x))

def customSubstitutionSource :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      positive : 0 < x

/-- error: no registered substitution rule matches this expression; provide `using` with a `FeasibleSurjection` certificate -/
#guard_msgs in
reformulation customSubstitutionTarget : customSubstitutionSource := by
  substitute x := exponentialAlias u

run_cmd do
  let env ← getEnv
  if env.contains `PTranTest.Atom.customSubstitutionTarget ||
      env.contains `PTranTest.Atom.customSubstitutionTarget.equivalence ||
      (PTran.Syntax.getProblemView? env `PTranTest.Atom.customSubstitutionTarget).isSome then
    throwError "an unsupported substitution committed output"

/-! Source spellings and all presentation fields survive recognition unchanged. -/

def absoluteFunction :=
  problem (x : ℝ)
    minimize abs x
    subject to
      nonnegative : 0 ≤ x

def absoluteNotation :=
  problem (x : ℝ)
    minimize |x|
    subject to
      nonnegative : 0 ≤ x

/--
info: problem (x : ℝ)
  minimize abs x
  subject to
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp absoluteFunction

/--
info: problem (x : ℝ)
  minimize |x|
  subject to
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp absoluteNotation

run_cmd Lean.Elab.Command.liftTermElabM do
  for name in #[``absoluteFunction, ``absoluteNotation] do
    let some before := PTran.Syntax.getProblemView? (← getEnv) name
      | throwError "missing original problem presentation"
    withLocalDeclD before.binders[0]!.name (mkConst ``Real) fun x => do
      let expression ← elaborate ⟨before.objective⟩
      let some atom ← recognizeAtom? expression
        | throwError "did not recognize the source objective"
      unless atom.original == expression && atom.kind == .abs && atom.operands == #[x] do
        throwError "recognition changed the source objective"
    let some after := PTran.Syntax.getProblemView? (← getEnv) name
      | throwError "recognition removed presentation metadata"
    unless before.sense == after.sense && before.objective == after.objective &&
        before.binders.map (fun b => (b.name, b.typeSyntax)) ==
          after.binders.map (fun b => (b.name, b.typeSyntax)) &&
        before.constraints.map (fun c => (c.name, c.proposition)) ==
          after.constraints.map (fun c => (c.name, c.proposition)) do
      throwError "recognition changed stored presentation metadata"

/--
info: problem (x : ℝ)
  minimize abs x
  subject to
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp absoluteFunction

/--
info: problem (x : ℝ)
  minimize |x|
  subject to
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp absoluteNotation

end

end PTranTest.Atom
