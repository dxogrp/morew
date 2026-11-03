/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite
import Morew.Elab.Rewrite.Registry

/-! Install exact NLP rules for automatic rewriting.
norm2Epigraph covers Euclidean values and explicit toLp 2 inputs;
fnNorm2Epigraph matches the named function. -/

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
