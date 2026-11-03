/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Reformulation.LogDet.Sources

/-! Domain-lowered log-det producers for imported certificate and presentation replay. -/

namespace MorewTest.Reformulation.LogDet

open Morew Morew.Conic

noncomputable section

variable (n : Nat) (hn : 0 < n)

reformulation domainIntermediate : (source n) := by conic at domain

reformulation nativeDomainIntermediate : (reverseSource n) := by conic at domain

end
end MorewTest.Reformulation.LogDet
