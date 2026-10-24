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

end MorewTest.Atom.Recognition
