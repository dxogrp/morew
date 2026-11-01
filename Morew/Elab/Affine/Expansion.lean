/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Affine
import Morew.Elab.Expansion

/-!
# Bounded helper expansion for affine certification

Affine recognition retains its eager expansion policy and its own locally
scoped options. The shared engine supplies accounting and structural reduction.
-/

/-- Maximum nested helper expansions; zero disables expansion. -/
register_option morew.affine.maxExpansionDepth : Nat := {
  defValue := 32
  descr := "Maximum nested helper expansions during affine certification (zero disables expansion)"
}

/-- Maximum helper unfoldings shared across branches; zero disables expansion. -/
register_option morew.affine.maxExpansionSteps : Nat := {
  defValue := 1024
  descr := "Maximum helper unfoldings during affine certification (zero disables expansion)"
}

/-- Maximum cumulative expanded expression size; zero disables expansion. -/
register_option morew.affine.maxExpansionNodes : Nat := {
  defValue := 100000
  descr := "Maximum cumulative expanded expression size during affine certification (zero disables expansion)"
}

namespace Morew.Elab.Affine.Expansion

open Lean Lean.Meta
open Morew.Elab.Expansion (ExpandM reduceChecked unfoldHead?)

/-- The temporary expression and the number of helper occurrences expanded. -/
structure Result where
  /-- A definitionally equal expression used only for proof construction. -/
  expression : Expr
  /-- Number of helper occurrences expanded, counting repeated applications. -/
  expansions : Nat

private def config : MetaM Morew.Elab.Expansion.Config := do
  let options ← getOptions
  return {
    depth := morew.affine.maxExpansionDepth.get options
    steps := morew.affine.maxExpansionSteps.get options
    nodes := morew.affine.maxExpansionNodes.get options
    depthOption := `morew.affine.maxExpansionDepth
    stepsOption := `morew.affine.maxExpansionSteps
    nodesOption := `morew.affine.maxExpansionNodes
    label := "affine"
  }

/-- Whether every helper-expansion budget is nonzero. -/
def enabled : MetaM Bool := do
  return Morew.Elab.Expansion.enabled (← config)

-- Keep each native operation's type/instance prefix intact, including when
-- its result is applied to further arguments (for example, a vector index).
-- Visit supplied value operands even before the operation is fully applied:
-- a helper can return a partial operation through a projection or local alias.
private def operandStart? (name : Name) (arity : Nat) : Option Nat := do
  let first ←
    if ([``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HSMul.hSMul,
        ``HPow.hPow].contains name) then some 4
    else if name == ``Neg.neg then some 2
    else if ([``Prod.mk, ``Matrix.vecCons].contains name) then some 2
    else if name == ``Finset.sum then some 3
    else if ([`Finset.sup', `Finset.inf'].contains name) then some 3
    else if ([``dotProduct, ``Matrix.mulVec, ``Matrix.vecMul].contains name) then some 5
    else if name == ``Matrix.transpose then some 3
    else if name == ``Matrix.diagonal then some 4
    else if name == `Matrix.trace then some 4
    else if name == `Matrix.det then some 5
    else if name == ``Matrix.submatrix then some 5
    else if name == ``Matrix.fromBlocks then some 5
    else if name == `Morew.Conic.fromBlocksFin then some 2
    else if name == `Morew.Conic.SymmetricMatrix.toMatrix then some 1
    else if name == `Morew.Conic.lowerTriangularMatrix then some 1
    else if ([`Morew.Fn.lambdaMax, `Morew.Fn.matrixFrac, `Morew.Fn.logDet].contains name)
      then some 1
    else if name == `Morew.Fn.nuclearNorm then some 2
    else if ([``WithLp.toLp, ``WithLp.ofLp].contains name) then some 2
    else if ([``LE.le, ``GE.ge, ``LT.lt].contains name) then some 2
    else if name == ``Eq then some 1
    else if name == ``And then some 0
    else if name == ``Membership.mem then some 3
    else if ([`Real.exp, `Real.log, `Real.sqrt, `Real.sin, `Real.cos, `Real.tan,
        `Real.arcsin, `Real.arccos, `Real.arctan, `Real.sinh, `Real.cosh,
        `Real.tanh, `Complex.exp, `Complex.log].contains name) then some 0
    else if name == `Real.rpow then some 0
    else if ([``Norm.norm, ``NNNorm.nnnorm, ``ENorm.enorm, `Inv.inv,
        `PosPart.posPart].contains name) then some 2
    else if name == `abs then some 3
    else if ([`Min.min, `Max.max].contains name) then some 2
    else none
  if first < arity then some first else none

-- Preserve blocked field selections without leaving named inner projections
-- for the downstream structural reducer to open through unrestricted whnf.
private partial def rawProblemProjections (source : Expr) : Expr :=
  source.replace fun expression =>
    let head := expression.getAppFn
    let arguments := expression.getAppArgs
    if (head.isConstOf ``Morew.Problem.objective ||
        head.isConstOf ``Morew.Problem.feasible) && arguments.size ≥ 3 then
      let index := if head.isConstOf ``Morew.Problem.objective then 0 else 1
      some (mkAppN (.proj ``Morew.Problem index (rawProblemProjections arguments[2]!))
        ((arguments.extract 3 arguments.size).map rawProblemProjections))
    else none

-- Expose a container by opening exactly one eligible helper along its head.
-- Rebuilding projections/applications lets visit keep the increased depth for
-- the entire field selection, without traversing unused constructor fields.
private partial def unfoldContainer? (expression : Expr) (bounds : Morew.Elab.Expansion.Config)
    (depth : Nat) : ExpandM (Option Expr) := do
  if let some step ← unfoldHead? bounds expression depth then
    return some step.expression
  let head := expression.getAppFn
  let arguments := expression.getAppArgs
  if (head.isConstOf ``Morew.Problem.objective ||
      head.isConstOf ``Morew.Problem.feasible) && arguments.size ≥ 3 then
    return (← unfoldContainer? arguments[2]! bounds depth).map fun container =>
      mkAppN head (arguments.set! 2 container)
  match expression with
  | .fvar _ => return none
  | .proj name index value =>
    return (← unfoldContainer? value bounds depth).map (.proj name index ·)
  | .app function argument =>
    if !expression.getAppFn.isConst then
      return (← unfoldContainer? function bounds depth).map (mkApp · argument)
  | _ => pure ()
  return none

private partial def visit (source : Expr) (reduce : Expr → Bool → MetaM Expr)
    (bounds : Morew.Elab.Expansion.Config) (depth : Nat) : ExpandM Expr := do
  let expression ← reduceChecked source reduce bounds
  match expression with
  | .lam name type body info =>
    return ← withLocalDecl name info type fun binding => do
      let body ← visit (body.instantiate1 binding) reduce bounds depth
      return .lam name type (body.abstract #[binding]) info
  | .forallE name type body info =>
    return ← withLocalDecl name info type fun binding => do
      let body ← visit (body.instantiate1 binding) reduce bounds depth
      return .forallE name type (body.abstract #[binding]) info
  | .letE name type value body nondep =>
    -- Evidence and instances must stay in scope, including unused proof lets.
    -- A container's selected field must be visited inside the depth of the
    -- helper that produces it, even when the container has a local name.
    let isContainer := (← whnf type).isAppOfArity ``Morew.Problem 2
    let value ← if (← isProp type) || (← isClass? type).isSome || isContainer then pure value
      else visit value reduce bounds depth
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let body ← visit (body.instantiate1 binding) reduce bounds depth
      return .letE name type value (body.abstract #[binding]) nondep
  | .proj name index value =>
    let rebuilt := Expr.proj name index (← visit value reduce bounds depth)
    let reduced ← reduceChecked rebuilt reduce bounds
    -- Expanding the tuple can expose a function or another helper at its field.
    if reduced != rebuilt then return ← visit reduced reduce bounds depth
    return rebuilt
  | _ => pure ()
  let head := expression.getAppFn
  let arguments := expression.getAppArgs
  -- Matrix.of and Matrix.reindex are equivalences applied through a canonical
  -- coercion. Preserve that coercion and its fixed parameters, visiting only
  -- the matrix operand; recognition checks the complete typed prefix. Expose
  -- local aliases structurally and named aliases with the same helper budget.
  if head.isConstOf ``DFunLike.coe && arguments.size >= 6 then
    let operation ← reduceChecked arguments[4]! reduce bounds
    if operation.isAppOf ``Matrix.of || operation.isAppOf ``Matrix.reindex then
      let mut expanded := arguments.set! 4 operation
      for i in [5:arguments.size] do
        expanded := expanded.set! i (← visit arguments[i]! reduce bounds depth)
      return mkAppN head expanded
    if let some expanded ← unfoldContainer? operation bounds depth then
      return ← visit (mkAppN head (arguments.set! 4 expanded)) reduce bounds (depth + 1)
  if let some name := head.constName? then
    if name == `Morew.Conic.SymmetricMatrix.ofMatrix && arguments.size >= 3 then
      let mut expanded := arguments
      expanded := expanded.set! 1 (← visit arguments[1]! reduce bounds depth)
      for i in [3:arguments.size] do
        expanded := expanded.set! i (← visit arguments[i]! reduce bounds depth)
      return mkAppN head expanded
    if let some first := operandStart? name arguments.size then
      let mut expanded := arguments
      for i in [first:arguments.size] do
        expanded := expanded.set! i (← visit arguments[i]! reduce bounds depth)
      return mkAppN head expanded
  if (head.isConstOf ``Morew.Problem.objective ||
      head.isConstOf ``Morew.Problem.feasible) && arguments.size ≥ 3 then
    if let some expanded ← unfoldContainer? arguments[2]! bounds depth then
      -- Revisit the whole projection at the increased depth so helpers in the
      -- selected field remain nested under the container's unfolding.
      return ← visit (mkAppN head (arguments.set! 2 expanded)) reduce bounds (depth + 1)
    -- A blocked container can still supply a decision-independent coefficient.
    -- Keep an equivalent raw projection: the downstream structural reducer
    -- must not reopen this named field with an unrestricted container whnf.
    -- Its value arguments remain eligible for bounded helper expansion.
    let mut expanded := arguments
    for i in [3:arguments.size] do
      expanded := expanded.set! i (← visit arguments[i]! reduce bounds depth)
    return rawProblemProjections (mkAppN head expanded)
  if let some step ← unfoldHead? bounds expression depth then
    return ← visit step.expression reduce bounds (depth + 1)
  -- An applied local vector or lambda may contain helper expressions. Unknown
  -- constant heads remain boundaries, including predicates and native atoms.
  if !head.isConst then
    if let .app function argument := expression then
      let rebuilt := mkApp (← visit function reduce bounds depth)
        (← visit argument reduce bounds depth)
      -- Child expansion can expose a beta redex, including through a projection.
      -- Charge its substitution before constructing the result, then visit any
      -- helpers that become applicable only after that substitution.
      let reduced ← reduceChecked rebuilt reduce bounds
      if reduced != rebuilt then return ← visit reduced reduce bounds depth
      return rebuilt
  return expression

/-- Prepare one source expression with one shared budget. The supplied reducer
handles only existing structural reductions; helper unfolding lives here.
Proof and instance lets remain available to evidence collection and reification.
Zero in any option disables all helper expansion. -/
def prepare (source : Expr) (reduce : Expr → Bool → MetaM Expr) : MetaM Result := do
  let bounds ← config
  if !Morew.Elab.Expansion.enabled bounds then
    return { expression := source, expansions := 0 }
  match ← Morew.Elab.Expansion.run (visit source reduce bounds 0) with
  | .ok (expression, state) => return { expression, expansions := state.steps }
  | .error error => throwError error.toMessageData bounds.label

/-- Expand safe helper heads without modifying the source presentation. -/
def expand (source : Expr) (reduce : Expr → Bool → MetaM Expr) : MetaM Expr := do
  return (← prepare source reduce).expression

end Morew.Elab.Affine.Expansion
