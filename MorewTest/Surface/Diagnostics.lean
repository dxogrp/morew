/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Surface.Fixtures

/-!
# Surface diagnostics and rollback

Exercise parser rejection, name collisions, certificate errors, and atomic rollback.
-/

namespace MorewTest.Surface

open Morew
noncomputable section

/-! The removed certificate-first slash form no longer parses as a command. -/

run_cmd do
  let obsolete :=
    "reformulation obsoleteCertificate / obsoleteTarget : original := by\n  epigraph t"
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command obsolete with
  | .error _ => pure ()
  | .ok _ => Lean.throwError "obsolete reformulation slash syntax was accepted"

/-! Expected failures are local diagnostics, not claims of non-equivalence. -/

def negativeSource :=
  problem (x : ℝ)
    minimize x
    subject to
      positive : 0 < x

/-- error: no registered substitution rule matches this expression; provide `using` with a `FeasibleSurjection` certificate -/
#guard_msgs in
reformulation noCoverageTarget : negativeSource := by
  substitute x := u ^ 2

/-- error: unknown decision variable `y` -/
#guard_msgs in
reformulation badVariableTarget : negativeSource := by
  substitute y := Real.exp u

/-- error: decision variable `x` already exists -/
#guard_msgs in
reformulation collisionTarget : negativeSource := by
  epigraph x

/-- error: `hypograph` is not valid for a minimization problem -/
#guard_msgs in
reformulation wrongHypographTarget : negativeSource := by
  hypograph t

/-- error: `epigraph` is not valid for a maximization problem -/
#guard_msgs in
reformulation wrongEpigraphTarget : boundedMaximum := by
  epigraph t

def generatedLabelCollision :=
  problem (x : ℝ)
    minimize x
    subject to
      epigraph_t : x ≤ x

/-- error: generated constraint name `epigraph_t` already exists; use `as <label>` to choose a different constraint label -/
#guard_msgs in
reformulation labelCollisionTarget : generatedLabelCollision := by
  epigraph t

/-! Generated declaration names are preflighted before anything is emitted. -/

def occupiedTarget :=
  problem (x : ℝ)
    minimize x

/-- error: `MorewTest.Surface.occupiedTarget` has already been declared -/
#guard_msgs in
reformulation occupiedTarget : identitySource := by
  epigraph t

run_cmd do
  if (← Lean.getEnv).contains `MorewTest.Surface.occupiedTarget.equivalence then
    Lean.throwError "a target-name collision emitted the canonical certificate"

def dottedCollisionTarget.equivalence := 0

/-- error: `MorewTest.Surface.dottedCollisionTarget.equivalence` has already been declared -/
#guard_msgs in
reformulation dottedCollisionTarget : identitySource := by
  epigraph t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MorewTest.Surface.dottedCollisionTarget then
    Lean.throwError "a canonical-certificate collision emitted the target"
  if (Morew.Syntax.getProblemView? env `MorewTest.Surface.dottedCollisionTarget).isSome then
    Lean.throwError "a canonical-certificate collision emitted target metadata"

def occupiedAlias := 0

/-- error: `MorewTest.Surface.occupiedAlias` has already been declared -/
#guard_msgs in
reformulation aliasCollisionTarget : identitySource
    certificate occupiedAlias := by
  epigraph t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MorewTest.Surface.aliasCollisionTarget ||
      env.contains `MorewTest.Surface.aliasCollisionTarget.equivalence then
    Lean.throwError "an alias collision emitted reformulation declarations"
  if (Morew.Syntax.getProblemView? env `MorewTest.Surface.aliasCollisionTarget).isSome then
    Lean.throwError "an alias collision emitted target metadata"

/-- error: certificate alias names the same declaration as the reformulation target -/
#guard_msgs in
reformulation duplicateTargetAlias : identitySource
    certificate duplicateTargetAlias := by
  epigraph t

/-- error: certificate alias names the same declaration as the canonical certificate -/
#guard_msgs in
reformulation duplicateCertificateAlias : identitySource
    certificate duplicateCertificateAlias.equivalence := by
  epigraph t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MorewTest.Surface.duplicateTargetAlias ||
      env.contains `MorewTest.Surface.duplicateTargetAlias.equivalence ||
      env.contains `MorewTest.Surface.duplicateCertificateAlias ||
      env.contains `MorewTest.Surface.duplicateCertificateAlias.equivalence then
    Lean.throwError "duplicate output names emitted reformulation declarations"
  if (Morew.Syntax.getProblemView? env `MorewTest.Surface.duplicateTargetAlias).isSome ||
      (Morew.Syntax.getProblemView? env
        `MorewTest.Surface.duplicateCertificateAlias).isSome then
    Lean.throwError "duplicate output names emitted target metadata"

/-! Failures while checking a generated certificate also roll back the target. -/

/-- error: failed to synthesize instance of type class -/
#guard_msgs (substring := true) in
reformulation invalidCertificateTarget : identitySource := by
  substitute x := u using 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MorewTest.Surface.invalidCertificateTarget ||
      env.contains `MorewTest.Surface.invalidCertificateTarget.equivalence then
    Lean.throwError "a certificate elaboration failure emitted reformulation declarations"
  if (Morew.Syntax.getProblemView? env `MorewTest.Surface.invalidCertificateTarget).isSome then
    Lean.throwError "a certificate elaboration failure emitted target metadata"

reformulation validAfterCertificateFailure : identitySource := by
  epigraph t

example : GlobalEquivalence identitySource validAfterCertificateFailure :=
  validAfterCertificateFailure.equivalence

def notAProblem := 1

/-- error: declaration `MorewTest.Surface.notAProblem` has no registered problem presentation -/
#guard_msgs in
#printp notAProblem

end
end MorewTest.Surface
