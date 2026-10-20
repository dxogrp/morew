import PTranTest.ImportCompatibility.ProblemPresentation.Defined
import PTranTest.ImportCompatibility.ProblemPresentation.Registered
import PTran.Syntax.Printer

/-!
# Presentations across compiled module boundaries

The separately compiled producers contribute independent registry entries.
Check their source-aligned output and reconstruct an imported problem in a
namespace that shadows its source type, objective function, and constraint predicate.
-/

namespace PTranTest.ImportCompatibility.ProblemPresentation

open PTran

abbrev Coordinate := Int

def value (x : Nat) := x + 100

def within (x y : Nat) : Prop := y < x

/--
info: problem (x y : Coordinate)
  minimize value x + y
  subject to
    lower : within x y
    positive : 0 < y
-/
#guard_msgs in
#printp Defined.minimum

/--
info: problem (n : Nat)
  maximize value n
-/
#guard_msgs in
#printp Defined.maximum

/--
info: problem (z : Nat)
  minimize z
  subject to
    generated : True
-/
#guard_msgs in
#printp Defined.generated

/--
info: problem (m : Nat)
  minimize m
-/
#guard_msgs in
#printp Registered.manual

run_cmd do
  let some view := PTran.Syntax.getProblemView? (← Lean.getEnv) ``Defined.minimum
    | throwError "import lost the source problem presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `copied
  Lean.Elab.Command.elabCommand (← `(def $name : Problem (Nat × Nat) Nat := $term))

-- Rebinding imported names to the consumer's definitions would break these checks.
example (x y : Nat) : copied.objective (x, y) = x + 1 + y := rfl

example (x y : Nat) : copied.feasible (x, y) ↔ x ≤ y ∧ 0 < y := Iff.rfl

end PTranTest.ImportCompatibility.ProblemPresentation
