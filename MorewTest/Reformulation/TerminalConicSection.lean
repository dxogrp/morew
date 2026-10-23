import Morew.Reformulation

/-!
# Terminal artifacts with proof-only section dependencies

A decision-independent opaque coefficient may retain an instance only through
a proof argument. Definitional equality can ignore that argument by proof
irrelevance, so final target application cannot rely on unification alone.
-/

namespace MorewTest.Reformulation.TerminalConicSection

open Morew
noncomputable section

class Evidence where
  witness : True

opaque coefficient (_ : True) : ℝ := 7

variable [Evidence]

def objectiveSource :=
  problem (x : ℝ)
    minimize coefficient Evidence.witness + x

reformulation objectiveTarget : objectiveSource := by
  conic

example : GlobalEquivalence objectiveSource objectiveTarget := objectiveTarget.equivalence
example : Conic.Form objectiveTarget := objectiveTarget.conicForm
example : IsConic objectiveTarget := objectiveTarget.isConic

def rowSource :=
  problem (x : ℝ)
    maximize x
    subject to
      upper : x ≤ coefficient Evidence.witness

reformulation rowTarget : rowSource := by
  conic

example : GlobalEquivalence rowSource rowTarget := rowTarget.equivalence
example : Conic.Form rowTarget := rowTarget.conicForm
example : IsConic rowTarget := rowTarget.isConic

def namedForm : Conic.Form rowTarget := rowTarget.conicForm
example : namedForm.data.sense = .maximize := rfl
example : namedForm.data.rowCount = 1 := rfl

end
end MorewTest.Reformulation.TerminalConicSection
