import Morew.Reformulation.Command

/-! Imported problem containers surrounding retained model-local definitions. -/

namespace MorewTest.Reformulation.LocalDefinitionRecovery.Defined

open Morew
noncomputable section

def surrounding :=
  let offset : ℝ := 2
  problem (x : ℝ)
    let loss := x + offset
    let same := x + offset
    let unused := x - offset
    minimize loss + same

@[irreducible] def irreducible :=
  problem (x : ℝ)
    let loss := x + 2
    let same := x + 2
    minimize loss + same

@[irreducible] def family (offset : ℝ) :=
  let coefficient := offset + 1
  problem (x : ℝ)
    let loss := x + coefficient
    let same := x + coefficient
    minimize loss + same

universe u

@[irreducible] def generic (α : Type u) [Preorder α] (witness : True) :=
  let proof := witness
  problem (x : α)
    let label : α := x
    let evidence := proof
    minimize label

end
end MorewTest.Reformulation.LocalDefinitionRecovery.Defined
