import Morew.Syntax

/-!
# Reformulation command syntax

Grammar for proof-producing reformulation scripts. Parser names remain in `Morew`.
-/

namespace Morew

/-- Syntax category for one proof-producing reformulation step. -/
declare_syntax_cat reformulationStep

/-- Substitute a decision variable with a parameterization, optionally using
an explicit feasible-surjection certificate. -/
syntax (name := substituteStep)
  "substitute " ident " := " term (" using " term)? : reformulationStep
/-- Introduce an epigraph variable for a minimization objective, optionally
choosing the generated constraint's presentation label. -/
syntax (name := epigraphStep)
  "epigraph " ident (" as " ident)? : reformulationStep
/-- Introduce a hypograph variable for a maximization objective, optionally
choosing the generated constraint's presentation label. -/
syntax (name := hypographStep)
  "hypograph " ident (" as " ident)? : reformulationStep

/-- Replace one current constraint by an exact conic representation,
optionally using an explicitly supplied representation certificate. -/
syntax (name := conicAtStep)
  "conic " "at " ident (" using " term)? : reformulationStep

/-- Certify the complete problem and finish the reformulation script. -/
syntax (name := conicStep) "conic" : reformulationStep

/-- Declare a transformed problem together with its global-equivalence
certificate. -/
syntax (name := reformulationCmd)
  "reformulation" ident ":" ident ("certificate" ident)? ":=" "by" ppLine
    ppIndent(reformulationStep*) : command

/-- Reformulate an explicitly applied registered problem family. Keep this
separate from the bare-name grammar so existing command quotations still work. -/
syntax (name := appliedReformulationCmd)
  "reformulation" ident ":" "(" term ")" ("certificate" ident)? ":=" "by" ppLine
    ppIndent(reformulationStep*) : command

end Morew
