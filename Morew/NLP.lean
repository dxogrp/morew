/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Basic
import Morew.NLP.Smooth
import Morew.NLP.Domain

/-!
# Certified smooth-NLP forms

This semantic entry point provides `Morew.NLP.Bounds`, `Row`, `Data`, and `Form`
without installing the problem or reformulation DSL.

`Morew.NLP.Smooth` supplies C² closure rules for arithmetic, finite sums,
product and finite-function components, and globally smooth elementary
functions. `Morew.NLP.Domain` adds open domain intersections, finite families,
and rules for logarithms, square roots, reciprocals, and fixed real powers.
These rules can be used in manual representations or by expression certifiers.

To construct a representation manually, supply each row's residual, closed
bounds, and `ContDiffOn ℝ 2` proof on a common domain. Assemble the rows and an
objective in `NLP.Data`, proving that the domain is open and that row feasibility
implies membership in it. The bounds may describe equalities, one-sided or
two-sided inequalities, or an infeasible interval.

`data.toProblem` is the represented ordinary problem. To represent an existing
`p`, construct `NLP.Form p` with this data and a proof of `data.toProblem = p`.
The form retains the concrete representation, and `form.isSmoothNLP` supplies
the corresponding existential proposition. Representation equality preserves
the objective on the whole decision space, not just on feasible points.

The open domain supplies analytic evidence without adding a hidden constraint.
At a feasible point, `data.feasible_mem_domain` and `data.domain_isOpen.mem_nhds`
allow the stored smoothness proofs to yield ordinary `ContDiffAt` proofs.
An unconstrained representation requires the full decision space as its domain;
an infeasible representation may use the empty domain.

For maximization, keep the problem explicitly typed as
`Problem X (OrderDual ℝ)` and set `data.sense` to `.maximize`. The objective is
unchanged, and representation equality alone does not determine its sense.
Native global smoothness certification is available through the separate
`Morew.Elab.NLP.Smooth` import. The separate `Morew.Elab.NLP.Domain` import
infers domains and proves inclusion from existing feasibility. The separate
`Morew.Reformulation` import provides targeted `nlp at label` exact smooth
rewrites and terminal `nlp` validation. The terminal step certifies the whole
problem, retaining its displayed comparisons while storing scalar residuals
and closed bounds in a concrete `NLP.Form`. It emits `target.nlpForm` and
`target.isSmoothNLP` alongside the ordinary target and its equivalence proof.
-/
