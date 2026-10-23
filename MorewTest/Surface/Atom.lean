import Morew.Reformulation
import MorewTest.Atom.Support

/-!
# Atom recognition in surface models

Ordinary custom functions remain valid model expressions, while atom recognition
preserves source spelling and presentation metadata.
-/

namespace MorewTest.Surface.Atom

open Lean Lean.Meta Lean.Elab.Term
open Morew Morew.Elab.Atom
open MorewTest.Atom

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
  if env.contains `MorewTest.Surface.Atom.customSubstitutionTarget ||
      env.contains `MorewTest.Surface.Atom.customSubstitutionTarget.equivalence ||
      (Morew.Syntax.getProblemView? env `MorewTest.Surface.Atom.customSubstitutionTarget).isSome then
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
    let some before := Morew.Syntax.getProblemView? (← getEnv) name
      | throwError "missing original problem presentation"
    withLocalDeclD before.binders[0]!.name (mkConst ``Real) fun x => do
      let expression ← elaborate ⟨before.objective⟩
      let some atom ← recognizeAtom? expression
        | throwError "did not recognize the source objective"
      unless atom.original == expression && atom.kind == .abs && atom.operands == #[x] do
        throwError "recognition changed the source objective"
    let some after := Morew.Syntax.getProblemView? (← getEnv) name
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

end MorewTest.Surface.Atom
