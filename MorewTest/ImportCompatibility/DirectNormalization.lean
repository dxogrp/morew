/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.DirectNormalization

/-!
# Imported directly normalized forms and replay
-/

namespace MorewTest.ImportCompatibility.DirectNormalization

open Lean Lean.Elab.Command Morew
open MorewTest.Reformulation.DirectNormalization

noncomputable section

example : IsConic affineConic := affineConic.isConic
example : IsSmoothNLP affineNLP := affineNLP.isSmoothNLP
example : IsSmoothNLP loweredDomainNLP := loweredDomainNLP.isSmoothNLP
example : loweredDomainNLP.nlpForm.data.toProblem = loweredDomainNLP :=
  loweredDomainNLP.nlpForm.represents

run_cmd do
  for (declaration, name) in #[(``affineConic, `conicReplay),
      (``maximumNLP, `maximumReplay), (``loweredDomainNLP, `domainReplay)] do
    let some view := Syntax.getProblemView? (← getEnv) declaration
      | throwError "missing directly normalized replay view"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(noncomputable def $(mkIdent name) := $term))

example : conicReplay = affineConic := rfl
example : maximumReplay = maximumNLP := rfl
example : domainReplay = loweredDomainNLP := rfl

reformulation continued : loweredDomainNLP := by nlp

example : GlobalEquivalence loweredDomain continued :=
  loweredDomainNLP.equivalence.trans continued.equivalence
example : continued.nlpForm.data.toProblem = continued := continued.nlpForm.represents

end
end MorewTest.ImportCompatibility.DirectNormalization
