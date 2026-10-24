import Lean.Parser

/-!
# Problem surface grammar

Syntax categories and parser declarations for problem terms and `#printp`.
Parser names remain in `Morew`; elaboration and printing are separate modules.
-/

namespace Morew

open Lean.Parser

/-- Syntax category for an explicitly typed, nondependent problem binder. -/
declare_syntax_cat problemBinder
/-- Parse one or more decision-variable names sharing an explicit type. -/
syntax (name := problemBinderStx) "(" ident+ " : " term ")" : problemBinder

/-- Syntax category for a labeled problem constraint. -/
declare_syntax_cat problemConstraint
/-- Parse a constraint label followed by its proposition. -/
syntax (name := problemConstraintStx) ident " : " term : problemConstraint

/-- A sequential, nonrecursive definition local to a problem. -/
declare_syntax_cat problemDefinition
/-- Local definitions may optionally declare their value type. -/
syntax (name := problemDefinitionStx)
  "let " ident (" : " term)? " := " term : problemDefinition

/-- An unconstrained minimization problem with one or more explicitly typed,
nondependent decision-variable binders. -/
syntax (name := minimizeProblemTerm)
  "problem " problemBinder+ (ppLine problemDefinition)* ppLine "minimize " term : term
/-- A constrained minimization problem with explicitly typed, nondependent
decision-variable binders and an indented block of named constraints. -/
syntax (name := minimizeConstrainedProblemTerm)
  "problem " problemBinder+ (ppLine problemDefinition)* ppLine "minimize " term ppLine
  "subject " "to" ppLine
    ppIndent(many1Indent(problemConstraint)) : term
/-- An unconstrained maximization problem with one or more explicitly typed,
nondependent decision-variable binders. -/
syntax (name := maximizeProblemTerm)
  "problem " problemBinder+ (ppLine problemDefinition)* ppLine "maximize " term : term
/-- A constrained maximization problem with explicitly typed, nondependent
decision-variable binders and an indented block of named constraints. -/
syntax (name := maximizeConstrainedProblemTerm)
  "problem " problemBinder+ (ppLine problemDefinition)* ppLine "maximize " term ppLine
  "subject " "to" ppLine
    ppIndent(many1Indent(problemConstraint)) : term

/-- Print the source-aligned mathematical presentation of a registered problem. -/
syntax (name := printProblemCmd) "#printp " ident : command

end Morew
