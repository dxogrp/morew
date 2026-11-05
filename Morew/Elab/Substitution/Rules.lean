/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Substitution
import Morew.Elab.Substitution.Registry

/-! Install built-in coordinate parameterizations. Explicit `via` also accepts unregistered records. -/

attribute [morew_substitute]
  Morew.Substitution.identity
  Morew.Substitution.neg
  Morew.Substitution.mulLeft
  Morew.Substitution.mulRight
  Morew.Substitution.addRight
  Morew.Substitution.addLeft
  Morew.Substitution.subRight
  Morew.Substitution.subLeft
  Morew.Substitution.affine
  Morew.Substitution.exp
  Morew.Substitution.square
