/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite
import Morew.Elab.Rewrite.Registry

/-!
# Registered exact NLP rules

These ordinary registrations make the shared semantic representations available
for automatic selected-row rewriting. The same checked matching and smoothness
certification applies to user registrations. Importing `Morew.NLP` alone does not
activate attributes or import elaboration infrastructure.

The native `norm2Epigraph` record covers both Euclidean-space values and explicit
`toLp 2` inputs. The separate `fnNorm2Epigraph` record matches the named function.
-/

attribute [morew_nlp]
  Morew.Rewrite.absEpigraph
  Morew.Rewrite.posEpigraph
  Morew.Rewrite.maxEpigraph
  Morew.Rewrite.minHypograph
  Morew.Rewrite.finsetSupEpigraph
  Morew.Rewrite.finsetInfHypograph
  Morew.Rewrite.norm1Epigraph
  Morew.Rewrite.normInfEpigraph
  Morew.Rewrite.normInfToLpEpigraph
  Morew.Rewrite.fnNorm1Epigraph
  Morew.Rewrite.fnNormInfEpigraph
  Morew.Rewrite.fnNorm2Epigraph
  Morew.Rewrite.norm2Epigraph
