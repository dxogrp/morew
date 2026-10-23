import Morew.Conic
import Morew.Reformulation

/-!
# Manual conic forms for surface problems

Certified conic data shares the semantic objective sense with the DSL and its
typed runner. Attaching a form leaves source and transformed printer output intact.
-/

assert_not_exists Morew.Syntax.ObjectiveSense

namespace MorewTest.Surface.Conic

open Morew
noncomputable section

def nonnegativeRow : Conic.Constraint ℝ where
  cone := Conic.Cone.nonnegative 1
  map := AffineMap.pi fun _ : Fin 1 => AffineMap.id ℝ ℝ

def minimum : Problem ℝ ℝ :=
  problem (x : ℝ)
    minimize x
    subject to
      nonnegative : 0 ≤ x

def minimumData : Conic.Data ℝ where
  sense := .minimize
  objective := AffineMap.id ℝ ℝ
  rowCount := 1
  constraints := fun _ => nonnegativeRow

def minimumForm : Conic.Form minimum where
  data := minimumData
  represents := by
    change Problem.mk (fun x : ℝ => x) _ = Problem.mk (fun x : ℝ => x) _
    congr 1
    funext x
    apply propext
    change (∀ _ : Fin 1,
      (fun _ : Fin 1 => x) ∈ (Conic.Cone.nonnegative 1).carrier) ↔ 0 ≤ x
    simp

example : IsConic minimum := minimumForm.isConic
example : minimumForm.data.sense = ObjectiveSense.minimize := rfl

/--
info: problem (x : ℝ)
  minimize x
  subject to
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp minimum

def maximum : Problem ℝ (OrderDual ℝ) :=
  problem (x : ℝ)
    maximize -x
    subject to
      nonnegative : 0 ≤ x

def maximumData : Conic.Data ℝ where
  sense := .maximize
  objective := -(AffineMap.id ℝ ℝ)
  rowCount := 1
  constraints := fun _ => nonnegativeRow

def maximumForm : Conic.Form maximum where
  data := maximumData
  represents := by
    change Problem.mk (fun x : ℝ => -x) _ = Problem.mk (fun x : ℝ => -x) _
    congr 1
    funext x
    apply propext
    change (∀ _ : Fin 1,
      (fun _ : Fin 1 => x) ∈ (Conic.Cone.nonnegative 1).carrier) ↔ 0 ≤ x
    simp

example : IsConic maximum := maximumForm.isConic
example : maximumForm.data.sense = ObjectiveSense.maximize := rfl

/--
info: problem (x : ℝ)
  maximize -x
  subject to
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp maximum

reformulation minimumEpigraph : minimum := by
  epigraph t

example : GlobalEquivalence minimum minimumEpigraph := minimumEpigraph.equivalence

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    nonnegative : 0 ≤ x
    epigraph_t : x ≤ t
-/
#guard_msgs in
#printp minimumEpigraph

reformulation maximumHypograph : maximum := by
  hypograph t

example : GlobalEquivalence maximum maximumHypograph := maximumHypograph.equivalence

/--
info: problem (x t : ℝ)
  maximize t
  subject to
    nonnegative : 0 ≤ x
    hypograph_t : t ≤ -x
-/
#guard_msgs in
#printp maximumHypograph

end

end MorewTest.Surface.Conic
