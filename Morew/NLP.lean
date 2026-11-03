/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Basic
import Morew.NLP.Smooth
import Morew.NLP.Domain

/-!
# Smooth nonlinear programs

`NLP.Data` stores an objective, scalar residuals with closed bounds, and C²
proofs on a common open domain containing every feasible point. The residual
bounds define feasibility. `NLP.Form p` pairs these data with the equality
`data.toProblem = p`, preserving objective values on the whole decision space.

`Morew.NLP.Smooth` provides smoothness rules for arithmetic, finite sums,
components, and elementary functions. `Morew.NLP.Domain` provides open domains
and rules for logarithms, square roots, reciprocals, and real powers.

For maximization, use `Problem X (OrderDual ℝ)` and set `data.sense` to
`.maximize`. Import `Morew.Reformulation.NLP` for modeling commands and
automatic certification.
-/
