/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import MorewTest.Rewrite.Registry.Source


@[expose] public section

namespace MorewTest.Rewrite.Registry.Second

/-- Independent imported registration used to check candidate-order invariance. -/
@[morew_nlp]
def second (c : ℝ) :
    Morew.EpigraphRepr (MorewTest.Rewrite.Registry.Source.shifted c) :=
  MorewTest.Rewrite.Registry.Source.Scoped.shiftedEpigraph c

end MorewTest.Rewrite.Registry.Second
