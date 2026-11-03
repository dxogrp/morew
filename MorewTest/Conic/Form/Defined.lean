/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Conic.Form.Support

/-! # Separately compiled form using a finite index without an enumeration -/

namespace MorewTest.Conic.Form

open Morew

noncomputable section

def finiteSource (ι : Type) (i : ι) : Problem (ι → ℝ) ℝ :=
  ⟨fun x => x i, fun x => x i ≤ 1⟩

def inferredFiniteForm (ι : Type) [Finite ι] (i : ι) :=
  form_for% (finiteSource ι i)

end
end MorewTest.Conic.Form
