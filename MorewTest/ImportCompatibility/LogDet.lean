/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.LogDet

/-! Imported log-det certificates retain domain evidence and exact presentation replay. -/

namespace MorewTest.ImportCompatibility.LogDet

open Morew Morew.Conic

noncomputable section

variable (n : Nat) (hn : 0 < n)

reformulation continued : (MorewTest.Reformulation.LogDet.domainIntermediate n) := by
  conic at bound
  conic

example : GlobalEquivalence (MorewTest.Reformulation.LogDet.source n) (continued n) :=
  (MorewTest.Reformulation.LogDet.domainIntermediate.equivalence n).trans
    (continued.equivalence n hn)

-- Packed triangular auxiliaries need no ambient matrix norm at the use site.
def importedForm : Conic.Form (continued n) := continued.conicForm n

example : (importedForm n).data.rowCount = 4 := rfl
example : (importedForm n).data.toProblem = continued n := (importedForm n).represents
example : IsConic (continued n) := (importedForm n).isConic

reformulation nativeContinued :
    (MorewTest.Reformulation.LogDet.nativeDomainIntermediate n) := by
  conic at bound using Morew.Conic.LogDet.nativeHypograph
  conic

example : GlobalEquivalence (MorewTest.Reformulation.LogDet.reverseSource n)
    (nativeContinued n) :=
  (MorewTest.Reformulation.LogDet.nativeDomainIntermediate.equivalence n).trans
    (nativeContinued.equivalence n hn)
example : IsConic (nativeContinued n) := nativeContinued.isConic n

namespace Shadow

def Fn.logDet (x : ℝ) : ℝ := x + 100
def lowerTriangularMatrix (x : ℝ) : ℝ := x + 200
def Real.log (x : ℝ) : ℝ := x + 300
def Matrix.det (x : ℝ) : ℝ := x + 400

run_cmd do
  for (original, copied) in #[
      (``MorewTest.Reformulation.LogDet.domainIntermediate, `domainCopy),
      (``continued, `continuedCopy),
      (``MorewTest.Reformulation.LogDet.nativeDomainIntermediate, `nativeDomainCopy),
      (``nativeContinued, `nativeContinuedCopy),
      (``MorewTest.Reformulation.LogDet.maximumTarget, `maximumCopy),
      (``MorewTest.Reformulation.LogDet.negativeMinimumTarget, `negativeCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported log-det declaration lost replay metadata: {original}"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "log-det replay contains incomplete evidence"

example : domainCopy n = MorewTest.Reformulation.LogDet.domainIntermediate n := rfl
example : continuedCopy n = continued n := rfl
example : nativeDomainCopy n =
    MorewTest.Reformulation.LogDet.nativeDomainIntermediate n := rfl
example : nativeContinuedCopy n = nativeContinued n := rfl
example : maximumCopy = MorewTest.Reformulation.LogDet.maximumTarget := rfl
example : negativeCopy = MorewTest.Reformulation.LogDet.negativeMinimumTarget := rfl

end Shadow

end
end MorewTest.ImportCompatibility.LogDet
