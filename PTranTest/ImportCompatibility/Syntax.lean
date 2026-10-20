import PTran.Syntax

/-!
# Syntax entry-point compatibility

The narrow syntax import retains the DSL, source metadata, public elaborators,
and printer after the implementation is split into focused modules.
-/

namespace PTranTest.ImportCompatibility.Syntax

open PTran

def minimum : Problem Nat Nat :=
  problem (n : Nat)
    minimize n

def maximum : Problem Nat (OrderDual Nat) :=
  problem (n : Nat)
    maximize n
    subject to
      upper : n ≤ 3

example (n : Nat) : minimum.objective n = n := rfl
example (n : Nat) : maximum.feasible n ↔ n ≤ 3 := Iff.rfl

/--
info: problem (n : Nat)
  minimize n
-/
#guard_msgs in
#printp minimum

/--
info: problem (n : Nat)
  maximize n
  subject to
    upper : n ≤ 3
-/
#guard_msgs in
#printp maximum

run_cmd do
  let env ← Lean.getEnv
  for name in #[``PTran.elabProblem, ``PTran.elabConstrainedMinProblem,
      ``PTran.elabMaxProblem, ``PTran.elabConstrainedMaxProblem,
      ``PTran.elabPrintProblem, ``PTran.Syntax.addProblemView,
      ``PTran.Syntax.registerProblemView, ``PTran.Syntax.replaceIdent,
      ``PTran.Syntax.preResolveTerm, ``PTran.Syntax.ProblemView.toTermSyntax] do
    unless env.contains name do
      throwError "the syntax entry point did not retain {name}"
  for (name, sense) in
      #[(``minimum, ObjectiveSense.minimize), (``maximum, ObjectiveSense.maximize)] do
    let some view := PTran.Syntax.getProblemView? env name
      | throwError "the syntax entry point did not register {name}"
    unless view.sense == sense do
      throwError "the syntax entry point changed the objective sense of {name}"

end PTranTest.ImportCompatibility.Syntax
