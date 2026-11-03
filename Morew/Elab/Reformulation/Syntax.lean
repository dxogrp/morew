/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax

/-! Reformulation grammar with parser names in Morew. -/

namespace Morew

/-- Syntax category for a reformulation step. -/
declare_syntax_cat reformulationStep

/-- Substitute a decision variable using a map whose range contains every feasible source point. -/
syntax (name := substituteStep)
  "substitute " ident " := " term (" using " term)? : reformulationStep
/-- Select an explicit coordinate parameterization. -/
syntax (name := substituteViaStep)
  "substitute " ident " := " term " via " term : reformulationStep
/-- Append a named consequence of the complete current feasible predicate. -/
syntax (name := deriveStep)
  "derive " ident " : " term " using " term : reformulationStep
/-- Restrict feasibility using an explicit improvement to the restricted problem. -/
syntax (name := restrictStep)
  "restrict " ident " : " term " using " term : reformulationStep
/-- Change one current constraint label without changing its predicate. -/
syntax (name := renameConstraintStep)
  "rename " ident &" to " ident : reformulationStep
/-- Remove a row implied by retained constraints, using explicit evidence or bounded proof search. -/
syntax (name := removeStep)
  "remove " "at " ident (" using " term)? : reformulationStep
/-- Introduce a minimization epigraph variable with an optional constraint label. -/
syntax (name := epigraphStep)
  "epigraph " ident (" as " ident)? : reformulationStep
/-- Introduce a maximization hypograph variable with an optional constraint label. -/
syntax (name := hypographStep)
  "hypograph " ident (" as " ident)? : reformulationStep

/-- Select either a direct model-local definition reference or a typed term. -/
declare_syntax_cat boundOccurrence
/-- A named selector resolves a model-local definition. -/
syntax (name := namedBoundOccurrence) ident : boundOccurrence
/-- Parentheses distinguish expression matching from named selection. -/
syntax (name := expressionBoundOccurrence) "(" term ")" : boundOccurrence

/-- Introduce an upper bound `f(x) ≤ t` for a selected expression. -/
syntax (name := epigraphAtStep)
  "epigraph " ident " at " boundOccurrence (" in " ident)?
    (" as " ident)? (" using " term)? : reformulationStep
/-- Introduce a lower bound `t ≤ f(x)` for a selected expression. -/
syntax (name := hypographAtStep)
  "hypograph " ident " at " boundOccurrence (" in " ident)?
    (" as " ident)? (" using " term)? : reformulationStep

/-- Replace a constraint by an exact conic representation, optionally supplying its certificate. -/
syntax (name := conicAtStep)
  "conic " "at " ident (" using " term)? : reformulationStep

/-- Replace a constraint by an exact smooth representation, optionally supplying its certificate. -/
syntax (name := nlpAtStep)
  "nlp " "at " ident (" using " term)? : reformulationStep

/-- Certify the complete problem and finish the reformulation script. -/
syntax (name := conicStep) "conic" : reformulationStep

/-- Certify every objective and residual as a smooth NLP and finish the script. -/
syntax (name := nlpStep) "nlp" : reformulationStep

/-- Declare a transformed problem together with its global-equivalence
certificate. -/
syntax (name := reformulationCmd)
  "reformulation" ident ":" ident ("certificate" ident)? ":=" "by" ppLine
    ppIndent(reformulationStep*) : command

/-- Reformulate an applied registered problem family. -/
syntax (name := appliedReformulationCmd)
  "reformulation" ident ":" "(" term ")" ("certificate" ident)? ":=" "by" ppLine
    ppIndent(reformulationStep*) : command

end Morew
