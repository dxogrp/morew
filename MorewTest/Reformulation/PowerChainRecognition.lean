/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.PowerChainPrinting
import Morew.Conic.Power.GeometricMean
import MorewTest.Environment
import Lean.Meta.Tactic.AuxLemma

/-!
# Conservative recognition of finite power-chain print rows

The recognizer sees typed rows, independently of labels and source syntax.
Complete native chains receive recipes; near misses keep ordinary printing.
-/

namespace MorewTest.Reformulation.PowerChainRecognition

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command Qq
open Morew Morew.Conic

noncomputable section

private def geometric (n : ℕ) (hn : 0 < n) (x u : Fin n → ℝ) (t : ℝ) : Prop :=
  u ⟨0, hn⟩ = x ⟨0, hn⟩ ∧
  (∀ j : Fin (n - 1),
    (u ⟨j.val, by omega⟩, x ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
      POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) ∧
  0 ≤ u ⟨n - 1, by omega⟩ ∧ t ≤ u ⟨n - 1, by omega⟩

private def geometricTerminal (n : ℕ) (hn : 0 < n) (x u : Fin n → ℝ) (t : ℝ) : Prop :=
  u ⟨0, hn⟩ - x ⟨0, hn⟩ ∈ ({0} : Set ℝ) ∧
  (∀ j : Fin (n - 1),
    (u ⟨j.val, by omega⟩, x ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
      (Cone.power (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
        (Power.prefixExponent_range j.val)).carrier) ∧
  u ⟨n - 1, by omega⟩ ∈ ℝ₊ ∧ (u ⟨n - 1, by omega⟩ - t) ∈ ℝ₊

private def inverse (n : ℕ) (hn : 0 < n) (x u : Fin n → ℝ) (t : ℝ) : Prop :=
  u ⟨0, hn⟩ = x ⟨0, hn⟩ ∧
  (∀ j : Fin (n - 1),
    (u ⟨j.val, by omega⟩, x ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
      POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) ∧
  (t, u ⟨n - 1, by omega⟩, 1) ∈ POW (1 / ((n : ℝ) + 1))

private def inverseTerminal (n : ℕ) (hn : 0 < n) (x u : Fin n → ℝ) (t : ℝ) : Prop :=
  u ⟨0, hn⟩ - x ⟨0, hn⟩ ∈ ({0} : Set ℝ) ∧
  (∀ j : Fin (n - 1),
    (u ⟨j.val, by omega⟩, x ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
      (Cone.power (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
        (Power.prefixExponent_range j.val)).carrier) ∧
  (t, u ⟨n - 1, by omega⟩, 1) ∈
    (Cone.power (1 / ((n : ℝ) + 1)) (Power.invProdExponent_range n hn)).carrier

private def dependentFamily (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (u : (i : Fin n) → Fin (i.val + 1) → ℝ) (t : ℝ) : Prop :=
  u ⟨0, hn⟩ ⟨0, by omega⟩ = x ⟨0, hn⟩ ∧
  (∀ j : Fin (n - 1),
    (u ⟨j.val, by omega⟩ ⟨0, by omega⟩, x ⟨j.val + 1, by omega⟩,
      u ⟨j.val + 1, by omega⟩ ⟨0, by omega⟩) ∈
      POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) ∧
  0 ≤ u ⟨n - 1, by omega⟩ ⟨0, by omega⟩ ∧
    t ≤ u ⟨n - 1, by omega⟩ ⟨0, by omega⟩

private partial def splitRows (body : Expr) : Array Expr :=
  if body.isAppOfArity ``And 2 then
    #[body.getAppArgs[0]!] ++ splitRows body.getAppArgs[1]!
  else #[body]

private def renderLeaf (expression : Expr) : TermElabM Syntax := do
  return (← PrettyPrinter.delab expression).raw

private def role : Option Syntax.PowerChainRow → String
  | none => "ordinary"
  | some (.first _ _ membership) => if membership then "first cone" else "first"
  | some (.step ..) => "step"
  | some (.nonnegative _ _ membership) => if membership then "sign cone" else "sign"
  | some (.bound _ _ _ membership) => if membership then "bound cone" else "bound"
  | some (.inverse ..) => "inverse"

private def checkRows (rows : Array Expr) (expected : Array String)
    (renderer : Expr → TermElabM Syntax := renderLeaf) : TermElabM Unit := do
  let hole ← mkFreshExprMVar (mkConst ``Nat)
  let assigned ← mkFreshExprMVar (mkConst ``Nat)
  assigned.mvarId!.assign (mkNatLit 7)
  let before ← getMCtx
  let environment ← getEnv
  let result ← Morew.Reformulation.Internal.powerChainPrintRows rows renderer
  let after ← getMCtx
  unless result.map role == expected do
    throwError "unexpected power-chain roles: {result.map role}; expected {expected}"
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "power-chain printing changed caller metavariable state"
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "power-chain printing changed a caller assignment"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "power-chain printing assigned a caller hole"
  if ← hole.mvarId!.isAssigned then throwError "power-chain printing assigned a caller hole"
  unless (← instantiateMVars assigned) == mkNatLit 7 do
    throwError "power-chain printing discarded a caller assignment"
  unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "power-chain printing changed declarations"

private def withRows (name : Name)
    (action : Array Expr → Array Expr → TermElabM Unit) : TermElabM Unit := do
  lambdaTelescope (← getConstInfo name).value! fun parameters body =>
    action parameters (splitRows body)

private def geometricRoles := #["first", "step", "sign", "bound"]
private def ordinary (rows : Array Expr) := Array.replicate rows.size "ordinary"

private def wrapMembership (row : Expr) (depth : Nat) : Expr :=
  let identity := mkLambda `proposition .default (mkSort .zero) (mkBVar 0)
  match row with
  | .forallE name type body info =>
      .forallE name type ((List.replicate depth ()).foldl (fun body _ => mkApp identity body) body) info
  | _ => row

run_cmd liftTermElabM do
  for (name, expected) in #[(``geometric, geometricRoles),
      (``geometricTerminal, #["first cone", "step", "sign cone", "bound cone"]),
      (``inverse, #["first", "step", "inverse"]),
      (``inverseTerminal, #["first cone", "step", "inverse"])] do
    withRows name fun _ rows => checkRows rows expected
    -- Concrete dimensions retain the same recognition, including empty steps.
    for n in [1, 3] do
      let dimension := mkNatLit n
      let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, dimension])
      let expression := (← getConstInfo name).value!.beta #[dimension, positive]
      lambdaTelescope expression fun _ body => checkRows (splitRows body) expected
  withRows ``dependentFamily fun _ rows => checkRows rows (ordinary rows)

run_cmd liftTermElabM do
  withRows ``geometric fun parameters rows => do
    let incomplete := rows.pop
    checkRows incomplete (ordinary incomplete)
    for duplicate in [0, 1, 2, 3] do
      let duplicated := rows.push rows[duplicate]!
      checkRows duplicated (ordinary duplicated)
    let unrelated := rows.push (mkConst ``True)
    checkRows unrelated (geometricRoles.push "ordinary")
    -- Planner templates and replay can leave several literal applications.
    checkRows (rows.set! 1 (wrapMembership rows[1]! 2)) geometricRoles
    -- Exhausting the bounded template inspection must preserve ordinary output.
    let deeplyWrapped := rows.set! 1 (wrapMembership rows[1]! 40)
    checkRows deeplyWrapped (ordinary deeplyWrapped)
    checkRows rows geometricRoles
    checkRows #[rows[1]!, rows[3]!, rows[0]!, rows[2]!]
      #["step", "bound", "first", "sign"]
    withLocalDeclD `v (← inferType parameters[3]!) fun auxiliary => do
      let other := rows.map (·.replaceFVars #[parameters[3]!] #[auxiliary])
      checkRows (rows ++ other) (geometricRoles ++ geometricRoles)
      -- An incomplete second chain must not suppress a complete first chain.
      checkRows (rows ++ other.pop) (geometricRoles ++ ordinary other.pop)
    let unresolved ← mkFreshExprMVar q(ℝ)
    let incomplete := rows.map (·.replaceFVars #[parameters[4]!] #[unresolved])
    checkRows incomplete (ordinary incomplete)
    if ← unresolved.mvarId!.isAssigned then
      throwError "recognition assigned an unresolved bound"
    -- A failed renderer is also speculative; a later healthy attempt recovers.
    checkRows rows (ordinary rows) (fun _ => throwError "deliberate renderer failure")
    checkRows rows geometricRoles

-- Rendering callbacks run speculatively as well as shape checks. Neither a
-- successful callback nor an exception may retain declarations or assignments.
run_cmd liftTermElabM do
  withRows ``geometric fun _ rows => do
    let callerHole ← mkFreshExprMVar (mkConst ``Nat)
    let generated ← IO.mkRef (#[] : Array Name)
    for succeeds in [true, false] do
      let renderer := fun expression => do
        callerHole.mvarId!.assign (mkNatLit 19)
        let name ← mkAuxLemma [] (mkConst ``True) (mkConst ``True.intro) (cache := false)
        generated.modify (·.push name)
        unless succeeds do throwError "deliberate callback failure after mutation"
        renderLeaf expression
      checkRows rows (if succeeds then geometricRoles else ordinary rows) renderer
      if ← callerHole.mvarId!.isAssigned then
        throwError "power-chain callback assigned a caller hole"
      for name in ← generated.get do
        if (← getEnv).contains name then
          throwError "power-chain callback leaked declaration {name}"
    if (← generated.get).isEmpty then throwError "callback isolation was not exercised"
    checkRows rows geometricRoles

private def elaborate (source : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm source none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

private def namedDimension : ℕ := 3

run_cmd liftTermElabM do
  for (term, accepted) in #[(← `(namedDimension), true),
      (← `(@OfNat.ofNat Nat 3 ⟨4⟩), false),
      (← `(@HAdd.hAdd Nat Nat Nat ⟨fun _ _ => 3⟩ 1 1), false)] do
    let dimension ← elaborate term
    let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, dimension])
    let expression := (← getConstInfo ``geometric).value!.beta #[dimension, positive]
    lambdaTelescope expression fun _ body => do
      let rows := splitRows body
      checkRows rows (if accepted then geometricRoles else ordinary rows)
  -- The conic planner can already have normalized the final numeric exponent.
  let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit 3])
  let expression := (← getConstInfo ``inverse).value!.beta #[mkNatLit 3, positive]
  lambdaTelescope expression fun _ body => do
    let rows := splitRows body
    let exponent ← elaborate (← `((1 / 4 : ℝ)))
    let membership := rows[2]!
    let normalized := mkAppN membership.getAppFn
      (membership.getAppArgs.set! 3 (mkApp (mkConst ``Cone.powerSet) exponent))
    checkRows (rows.set! 2 normalized) #["first", "step", "inverse"]

run_cmd liftTermElabM do
  let fakeAddition ← elaborate (← `((⟨fun a (_ : ℝ) => a + 1⟩ : HAdd ℝ ℝ ℝ)))
  let fakeIndexAddition ← elaborate (← `((⟨fun a (_ : ℕ) => a + 1⟩ : HAdd ℕ ℕ ℕ)))
  let fakeCast ← elaborate (← `(fun n : ℕ => (⟨fun _ => (n : ℝ)⟩ : NatCast ℝ)))
  let fakeMembership ← elaborate (← `(fun α : ℝ =>
    (⟨fun _ p => p ∈ POW α⟩ : Membership (ℝ × ℝ × ℝ) (Set (ℝ × ℝ × ℝ)))))
  withRows ``geometric fun parameters rows => do
    let alteredAdd ← Meta.transform rows[1]! (post := fun value => do
      unless value.isAppOfArity ``HAdd.hAdd 6 do return .continue
      if (← isDefEq value.getAppArgs[0]! q(ℝ)) &&
          (← isDefEq value.getAppArgs[5]! q((1 : ℝ))) then
        return .done (mkAppN value.getAppFn (value.getAppArgs.set! 3 fakeAddition))
      return .continue)
    unless ← isDefEq alteredAdd rows[1]! do
      throwError "altered addition control no longer agrees on these operands"
    let altered := rows.set! 1 alteredAdd
    checkRows altered (ordinary altered)
    let alteredIndexAddition ← Meta.transform rows[1]! (post := fun value => do
      unless value.isAppOfArity ``HAdd.hAdd 6 do return .continue
      if (← isDefEq value.getAppArgs[0]! q(ℕ)) &&
          (← isDefEq value.getAppArgs[5]! q((1 : ℕ))) then
        return .done (mkAppN value.getAppFn (value.getAppArgs.set! 3 fakeIndexAddition))
      return .continue)
    unless ← isDefEq alteredIndexAddition rows[1]! do
      throwError "altered index operation no longer agrees on these operands"
    let altered := rows.set! 1 alteredIndexAddition
    checkRows altered (ordinary altered)
    let alteredCast ← Meta.transform rows[1]! (post := fun value => do
      unless value.isAppOfArity ``Nat.cast 3 do return .continue
      unless ← isDefEq value.getAppArgs[0]! q(ℝ) do return .continue
      return .done (mkAppN value.getAppFn
        (value.getAppArgs.set! 1 (fakeCast.beta #[value.getAppArgs[2]!]))))
    unless ← isDefEq alteredCast rows[1]! do
      throwError "altered Nat cast no longer agrees on this index"
    let altered := rows.set! 1 alteredCast
    checkRows altered (ordinary altered)
    let alteredMembership ← Meta.transform rows[1]! (post := fun value => do
      if value.isAppOfArity ``Membership.mem 5 &&
          value.getAppArgs[3]!.isAppOfArity ``Cone.powerSet 1 then
        let exponent := value.getAppArgs[3]!.getAppArgs[0]!
        return .done (mkAppN value.getAppFn
          (value.getAppArgs.set! 2 (fakeMembership.beta #[exponent])))
      return .continue)
    unless ← isDefEq alteredMembership rows[1]! do
      throwError "altered membership control no longer agrees on this carrier"
    let altered := rows.set! 1 alteredMembership
    checkRows altered (ordinary altered)
    let alteredExponent ← Meta.transform rows[1]! (post := fun value => do
      if value.isAppOfArity ``HDiv.hDiv 6 then
        let numerator : Q(ℝ) := value.getAppArgs[4]!
        let denominator : Q(ℝ) := value.getAppArgs[5]!
        return .done q($numerator / ($denominator + 1))
      return .continue)
    let altered := rows.set! 1 alteredExponent
    checkRows altered (ordinary altered)
    let zero ← mkAppM ``Fin.mk #[mkNatLit 0, parameters[1]!]
    let source := parameters[2]!
    let alteredIndex ← Meta.transform rows[1]! (post := fun value => do
      if value.isApp && value.appFn! == source then
        return .done (mkApp source zero)
      return .continue)
    let altered := rows.set! 1 alteredIndex
    checkRows altered (ordinary altered)
    -- Failed recognition must not affect the original complete rows.
    checkRows rows geometricRoles

private partial def containsIdentifier (stx : Lean.Syntax) (name : Name) : Bool :=
  (stx.isIdent && stx.getId.eraseMacroScopes == name) ||
    stx.getArgs.any (fun child => containsIdentifier child name)

-- A global reference can print with the same short name as the original finite
-- binder. The new mathematical binder must avoid both vector and dimension names.
namespace GlobalVector

noncomputable def j : Fin 3 → ℝ := fun _ => 1

run_cmd liftTermElabM do
  let dimension := mkNatLit 3
  let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, dimension])
  let expression := (← getConstInfo ``geometric).value!.beta #[dimension, positive]
  lambdaTelescope expression fun parameters body => do
    let rows := (splitRows body).map (·.replaceFVars #[parameters[0]!] #[mkConst ``j])
    checkRows rows geometricRoles
    let recipes ← Morew.Reformulation.Internal.powerChainPrintRows rows renderLeaf
    let some (.step _ source index _) := recipes[1]! | throwError "missing global-vector step"
    unless containsIdentifier source `j do
      throwError "global-vector control no longer prints the short name j"
    if index.eraseMacroScopes == `j then
      throwError "mathematical binder captured the global vector j"

end GlobalVector

namespace GlobalDimension

def j : ℕ := 3

run_cmd liftTermElabM do
  let dimension : Expr := mkConst ``j
  let positive ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, dimension])
  let expression := (← getConstInfo ``geometric).value!.beta #[dimension, positive]
  lambdaTelescope expression fun _ body => do
    let rows := splitRows body
    checkRows rows geometricRoles
    let recipes ← Morew.Reformulation.Internal.powerChainPrintRows rows renderLeaf
    let some (.step _ _ index size) := recipes[1]! | throwError "missing global-dimension step"
    unless containsIdentifier size `j do
      throwError "global-dimension control no longer prints the short name j"
    if index.eraseMacroScopes == `j then
      throwError "mathematical binder captured the global dimension j"

end GlobalDimension

end
end MorewTest.Reformulation.PowerChainRecognition
