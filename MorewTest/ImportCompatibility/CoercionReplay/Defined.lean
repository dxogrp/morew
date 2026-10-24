import Morew.Reformulation.Command

/-! Problems whose coercion functions must survive imported presentation replay. -/

namespace MorewTest.ImportCompatibility.CoercionReplay.Defined

open Morew
noncomputable section

structure Box where
  value : ℝ
  size : ℕ

@[coe] def boxToReal (box : Box) : ℝ := box.value
@[coe] def boxToNat (box : Box) : ℕ := box.size

instance : Coe Box ℝ := ⟨boxToReal⟩
instance : Coe Box ℕ := ⟨boxToNat⟩

def explicitSource := problem (x : Box) minimize boxToReal x
def castSource := problem (x : Box) minimize (x : ℝ)

def family (offset : ℝ) :=
  problem (x : Box)
    let loss := boxToReal x
    minimize loss + offset
    subject to cap : boxToReal x ≤ 10

reformulation generated : (family 2) := by
  epigraph t at loss

def indexedFamily (box : Box) :=
  problem (i : Fin (boxToNat box + 1))
    minimize (i.val : ℝ)

end
end MorewTest.ImportCompatibility.CoercionReplay.Defined
