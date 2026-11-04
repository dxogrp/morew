/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Basic
import Morew.NLP.Smooth
import Morew.NLP.Domain

/-!
# Smooth nonlinear programs

`NLP.Data` stores an objective and scalar residuals with closed bounds, all C²
on a common open domain containing every feasible point. `NLP.Form p` certifies
`data.toProblem = p`, including objective equality outside that domain.

`Morew.NLP.Smooth` provides smoothness rules for arithmetic, finite sums,
components, and elementary functions. `Morew.NLP.Domain` provides open domains
and rules for logarithms, square roots, reciprocals, and real powers.

For maximization, use `Problem X (OrderDual ℝ)` and set `data.sense` to
`.maximize`. Import `Morew.Reformulation.NLP` for modeling commands and
automatic certification.
-/
