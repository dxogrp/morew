/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Substitution
import Morew.Elab.Substitution.Registry

/-!
# Built-in coordinate parameterizations

These declarations use the same public attribute as downstream rules. Explicit
`via` selection also accepts records that have never been registered.
-/

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
