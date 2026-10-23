import MorewTest.Reformulation.ExponentialCustom

/-!
# Terminal validation after explicit certificates

All four targeted certificate interfaces can prepare a problem for terminal
validation. The stored form includes the generated scalar and finite cone rows.
-/

namespace MorewTest.Reformulation.TerminalConicCustom

open Morew Morew.Conic
open MorewTest.Reformulation.ExponentialCustom
noncomputable section

reformulation graph : graphSource := by
  conic at graph using graphRule
  conic
example : IsConic graph := graph.isConic
example : graph.conicForm.data.rowCount = 2 := rfl

reformulation epigraphCertified : epigraphSource := by
  conic at epi_row using epigraphRule
  conic
example : IsConic epigraphCertified := epigraphCertified.isConic
example : epigraphCertified.conicForm.data.rowCount = 2 := rfl

reformulation hypographCertified : hypographSource := by
  conic at hypo_row using hypographRule
  conic
example : IsConic hypographCertified := hypographCertified.isConic
example : hypographCertified.conicForm.data.sense = .maximize := rfl

def scalarSource :=
  problem (x t : ℝ)
    minimize t
    subject to exponential : Real.exp x ≤ t

reformulation scalar : scalarSource := by
  conic at exponential using scalarAuxiliaryRule
  conic
example : IsConic scalar := scalar.isConic
example : scalar.conicForm.data.rowCount = 2 := rfl

reformulation empty : emptySource := by
  conic at empty using emptyRule
  conic
-- An empty quantified family is still one structural cone row.
example : empty.conicForm.data.rowCount = 3 := rfl
example : empty.conicForm.data.toProblem = empty := empty.conicForm.represents

end
end MorewTest.Reformulation.TerminalConicCustom
