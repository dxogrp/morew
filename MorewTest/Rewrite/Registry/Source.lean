/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Rewrite.Registry
import Morew.Rewrite.Polyhedral

namespace MorewTest.Rewrite.Registry.Source

/-- A custom head whose implementation is irrelevant to registry lookup. -/
def shifted (c x : ℝ) : ℝ := x + c

@[morew_conic, morew_nlp]
def shiftedGraph (c : ℝ) : Morew.GraphRepresentation (shifted c) where
  Auxiliary := Unit
  target x y _ := y = x + c
  source_iff_exists _ _ := by simp [shifted]

namespace Scoped

def shiftedEpigraph (c : ℝ) : Morew.EpigraphRepresentation (shifted c) where
  Auxiliary := Unit
  target x y _ := x + c ≤ y
  source_iff_exists _ _ := by simp [shifted]

attribute [scoped morew_nlp] shiftedEpigraph

end Scoped

namespace HelperOpacity

noncomputable def projectedAbs (x : ℝ) : ℝ × ℝ := (|x|, 0)

noncomputable def hiddenProjectedAbs (x : ℝ) : ℝ × ℝ := projectedAbs x

noncomputable def projectedAbsRule :
    Morew.ExactConstraintLift (fun x : ℝ => (projectedAbs x).1 ≤ 3) :=
  .ofIff (fun x => x ≤ 3 ∧ -x ≤ 3) (by
    intro x
    simpa only [projectedAbs] using Morew.Rewrite.Polyhedral.abs_le_iff x 3)

noncomputable def namedAbs (x : ℝ) : ℝ := |x|

noncomputable def aliasAbs (x : ℝ) : ℝ := namedAbs x

noncomputable def implicationAbsRule :
    Morew.ExactConstraintLift (fun x : ℝ => (|x| ≤ 3 → |x| ≤ 3) ∧ x ≤ 3) :=
  .ofIff (fun x => x ≤ 3) (by intro x; simp)

def applyFunction (f : ℝ → ℝ) (x : ℝ) : ℝ := f x

noncomputable def appliedAbsRule :
    Morew.EpigraphRepresentation (applyFunction namedAbs) where
  Auxiliary := Unit
  target x t _ := x ≤ t ∧ -x ≤ t
  source_iff_exists x t := by
    simpa only [applyFunction, namedAbs, exists_const] using
      Morew.Rewrite.Polyhedral.abs_le_iff x t

end HelperOpacity

end MorewTest.Rewrite.Registry.Source
