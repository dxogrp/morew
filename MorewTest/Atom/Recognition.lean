/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Atom.Support

/-!
# Native atom recognition
-/

namespace MorewTest.Atom.Recognition

open Lean Lean.Meta Lean.Elab.Term
open Morew Morew.Elab.Atom

/-! Native notation, qualified names, and ordinary namespace resolution. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  assertAtom (← `(fun x : ℝ => Real.exp x)) .exp #[0]
  assertAtom (← `(fun x : ℝ => Real.log x)) .log #[0]
  assertAtom (← `(fun x : ℝ => Real.sqrt x)) .sqrt #[0]
  assertAtom (← `(fun x : ℝ => Real.sin x)) .sin #[0]
  assertAtom (← `(fun x : ℝ => Real.cos x)) .cos #[0]
  assertAtom (← `(fun x : ℝ => Real.sinh x)) .sinh #[0]
  assertAtom (← `(fun x : ℝ => Real.cosh x)) .cosh #[0]
  assertAtom (← `(fun x : ℝ => Real.tanh x)) .tanh #[0]
  assertAtom (← `(fun x y : ℝ => Real.rpow x y)) .rpow #[0, 1]
  assertAtom (← `(fun x y : ℝ => x ^ y)) .rpow #[0, 1]
  assertAtom (← `(fun x y : ℝ => y ^ x)) .rpow #[1, 0]
  -- Atom identity imposes neither exponent independence nor domain evidence.
  assertAtom (← `(fun x : ℝ => x ^ x)) .rpow #[0, 0]
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
  assertAtom (← `(fun x : ℝ => sin x)) .sin #[0]
  assertAtom (← `(fun x : ℝ => cos x)) .cos #[0]
  assertAtom (← `(fun x : ℝ => sinh x)) .sinh #[0]
  assertAtom (← `(fun x : ℝ => cosh x)) .cosh #[0]
  assertAtom (← `(fun x : ℝ => tanh x)) .tanh #[0]
  assertAtom (← `(fun x y : ℝ => rpow x y)) .rpow #[0, 1]

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

  let expression ← elaborate (← `(fun x : ℝ => Real.tanh (Real.sin x)))
  lambdaTelescope expression fun binders body => do
    let some outer ← recognizeAtom? body
      | throwError "did not recognize a hyperbolic tangent with a nested operand"
    unless outer.kind == .tanh && outer.original == body && outer.operands.size == 1 do
      throwError "changed the outer hyperbolic tangent"
    let some inner ← recognizeAtom? outer.operands[0]!
      | throwError "did not preserve the nested sine"
    unless inner.kind == .sin && inner.operands == binders do
      throwError "changed the nested sine operand"

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

  withLocalDeclD `x (mkConst ``Real) fun x =>
    withLocalDeclD `y (mkConst ``Real) fun y => do
      let base := mkMData {} x
      let exponent := mkMData {} y
      let function := mkMData {} (Lean.mkConst ``Real.rpow)
      let appliedBase := mkMData {} (mkApp function base)
      let expression := mkMData {} (mkApp appliedBase exponent)
      let some atom ← recognizeAtom? expression
        | throwError "application metadata prevented real-power recognition"
      unless atom.kind == .rpow && atom.original == expression &&
          atom.operands == #[base, exponent] do
        throwError "real-power recognition changed its expression or operands"

end MorewTest.Atom.Recognition
