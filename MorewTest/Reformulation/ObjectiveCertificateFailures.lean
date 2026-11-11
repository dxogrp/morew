/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Environment
import Lean.Elab.GuardMsgs

/-! Invalid objective certificates fail atomically, without automatic fallback. -/

namespace MorewTest.Reformulation.ObjectiveCertificateFailures

open Morew Lean Lean.Meta Lean.Elab.Term
noncomputable section

elab "assert_objective_rejected% " target:ident " in " nested:command : command => do
  let before ← getEnv
  let targetName := (← Lean.getCurrNamespace) ++ target.getId
  let previous := (← get).messages
  let previousTasks := (← get).snapshotTasks
  modify fun state => { state with snapshotTasks := #[] }
  let messages ← try
    Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages nested
  finally
    modify fun state => { state with messages := previous, snapshotTasks := previousTasks }
  unless messages.toList.any (·.severity == .error) do
    throwError "invalid objective certificate did not report an error"
  let after ← getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    throwError "failed objective certification changed declarations"
  for suffix in #[Name.anonymous, `equiv, `conicForm, `quadConicForm, `isConic, `isQuadConic] do
    let name := targetName ++ suffix
    if after.contains name || (Morew.Syntax.getProblemView? after name).isSome then
      throwError "failed objective certification retained an output or presentation"

-- Bypass ordinary hole diagnostics to exercise certificate validation itself.
elab "objective_missing%" : term <= expected => mkFreshExprMVar expected
elab "objective_synthetic_sorry%" : term <= expected => mkSorry expected true
elab "objective_user_sorry%" : term <= expected => mkSorry expected false

def source := problem (x : ℝ) minimize x

def maximum := problem (x : ℝ) maximize x

def bounded := problem (x : ℝ) minimize x subject to bound : |x| ≤ 2

assert_objective_rejected% wrongAffine in
reformulation wrongAffine : source := by
  conic using Affine.Certified.const ℝ (0 : ℝ)

assert_objective_rejected% wrongDomain in
reformulation wrongDomain : source := by
  conic using (Affine.Certified.id (ℝ × ℝ)).fst

assert_objective_rejected% wrongQuadratic in
reformulation wrongQuadratic : source := by
  qconic using QuadConic.CertifiedMin.ofAffine (Affine.Certified.const ℝ (0 : ℝ))

-- Zero curvature does not permit supplying the certificate for the other direction.
assert_objective_rejected% wrongMinDirection in
reformulation wrongMinDirection : source := by
  qconic using QuadConic.CertifiedMax.ofAffine (Affine.Certified.id ℝ)

assert_objective_rejected% wrongMaxDirection in
reformulation wrongMaxDirection : maximum := by
  qconic using QuadConic.CertifiedMin.ofAffine (Affine.Certified.id ℝ)

assert_objective_rejected% missingAffine in
reformulation missingAffine : source := by conic using objective_missing%

assert_objective_rejected% missingQuadratic in
reformulation missingQuadratic : source := by qconic using objective_missing%

assert_objective_rejected% syntheticAffine in
reformulation syntheticAffine : source := by conic using objective_synthetic_sorry%

assert_objective_rejected% userAffine in
reformulation userAffine : source := by conic using objective_user_sorry%

assert_objective_rejected% syntheticQuadratic in
reformulation syntheticQuadratic : source := by qconic using objective_synthetic_sorry%

assert_objective_rejected% userQuadratic in
reformulation userQuadratic : source := by qconic using objective_user_sorry%

-- The rejected terminal certificate also rolls back helpers from earlier successful steps.
assert_objective_rejected% lateFailure in
reformulation lateFailure : bounded certificate lateFailureAlias := by
  conic at bound
  conic using Affine.Certified.const ℝ (0 : ℝ)

assert_not_exists lateFailureAlias

-- Certification is for the current objective, after any earlier transformation.
assert_objective_rejected% staleObjective in
reformulation staleObjective : source := by
  epigraph t
  conic using (Affine.Certified.id (ℝ × ℝ)).fst

def zeroSource := problem (_x : ℝ) minimize (0 : ℝ)

section Instances

variable (group : AddCommGroup ℝ)
  (scalarModule : @Module ℝ ℝ inferInstance group.toAddCommMonoid)

def alternateCertificate :
    @Affine.Certified ℝ ℝ group scalarModule Real.instAddCommGroup (inferInstance : Module ℝ ℝ) (fun _ => 0) :=
  @Affine.Certified.const ℝ Real.instAddCommGroup (inferInstance : Module ℝ ℝ)
    ℝ group scalarModule 0

def alternateQuadraticCertificate :
    @QuadConic.CertifiedMin ℝ group scalarModule (fun _ => 0) :=
  @QuadConic.CertifiedMin.ofAffine ℝ group scalarModule _
    (alternateCertificate group scalarModule)

assert_objective_rejected% wrongInstances in
reformulation wrongInstances : zeroSource := by
  conic using alternateCertificate group scalarModule

assert_objective_rejected% wrongQuadraticInstances in
reformulation wrongQuadraticInstances : zeroSource := by
  qconic using alternateQuadraticCertificate group scalarModule

end Instances

def indefinite := problem (x y : ℝ) minimize x ^ 2 - y ^ 2

assert_objective_rejected% indefiniteTarget in
reformulation indefiniteTarget : indefinite := by qconic

-- A failed name remains available for a subsequent checked declaration.
reformulation wrongAffine : source := by conic using Affine.Certified.id ℝ
example : IsConic wrongAffine := wrongAffine.isConic

end
end MorewTest.Reformulation.ObjectiveCertificateFailures
