import PTran

/-!
# Substitution diagnostics and failed-command rollback

These tests exercise localized failures in typed substitution steps.  Every
failed command requests a certificate alias and is followed by an environment
check, so a regression that commits any part of the command is caught.
-/

namespace PTranTest.Reformulation.SubstitutionFailures

open PTran
noncomputable section

private def assertNoReformulationOutput (target aliasName : Lean.Name) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  let certificateName := target ++ `equivalence
  if env.contains target then
    Lean.throwError "failed reformulation emitted target `{target}`"
  if env.contains certificateName then
    Lean.throwError "failed reformulation emitted certificate `{certificateName}`"
  if env.contains aliasName then
    Lean.throwError "failed reformulation emitted alias `{aliasName}`"
  if (PTran.Syntax.getProblemView? env target).isSome then
    Lean.throwError "failed reformulation registered presentation metadata for `{target}`"

def positiveSource :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      positive : 0 < x

/-! A replacement must introduce exactly one new decision binder. -/

/-- error: unknown decision variable `missing` -/
#guard_msgs in
reformulation unknownBinderTarget : positiveSource
    certificate unknownBinderAlias := by
  substitute missing := Real.exp u

run_cmd do
  assertNoReformulationOutput
    `PTranTest.Reformulation.SubstitutionFailures.unknownBinderTarget
    `PTranTest.Reformulation.SubstitutionFailures.unknownBinderAlias

/-- error: cannot determine the new decision variable; the substitution expression must contain one new identifier -/
#guard_msgs in
reformulation noFreshBinderTarget : positiveSource
    certificate noFreshBinderAlias := by
  substitute x := Real.exp x

run_cmd do
  assertNoReformulationOutput
    `PTranTest.Reformulation.SubstitutionFailures.noFreshBinderTarget
    `PTranTest.Reformulation.SubstitutionFailures.noFreshBinderAlias

/-- error: ambiguous substitution: expected exactly one new decision variable -/
#guard_msgs (substring := true) in
reformulation ambiguousFreshBindersTarget : positiveSource
    certificate ambiguousFreshBindersAlias := by
  substitute x := u + v

run_cmd do
  assertNoReformulationOutput
    `PTranTest.Reformulation.SubstitutionFailures.ambiguousFreshBindersTarget
    `PTranTest.Reformulation.SubstitutionFailures.ambiguousFreshBindersAlias

/-! The automatic exponential rule needs positivity in the typed current
problem, including when an earlier step has already changed that problem. -/

def unrestrictedSource :=
  problem (x : ℝ)
    minimize Real.log x

/-- error: the registered exponential rule requires the current constraint `0 < x`; provide `using` for a more general feasible domain -/
#guard_msgs in
reformulation missingPositivityTarget : unrestrictedSource
    certificate missingPositivityAlias := by
  epigraph t as logarithm_bound
  substitute x := Real.exp u

run_cmd do
  assertNoReformulationOutput
    `PTranTest.Reformulation.SubstitutionFailures.missingPositivityTarget
    `PTranTest.Reformulation.SubstitutionFailures.missingPositivityAlias

/-! Replacement elaboration is checked at the selected coordinate's type. -/

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
reformulation illTypedReplacementTarget : positiveSource
    certificate illTypedReplacementAlias := by
  substitute x := Nat.succ n

run_cmd do
  assertNoReformulationOutput
    `PTranTest.Reformulation.SubstitutionFailures.illTypedReplacementTarget
    `PTranTest.Reformulation.SubstitutionFailures.illTypedReplacementAlias

/-! Automatic rules match elaborated declarations, not a shadowing spelling. -/

namespace ShadowedReal

namespace Real

def exp (value : Nat) : Nat := value

end Real

def source :=
  problem (x : Nat)
    minimize x
    subject to
      positive : 0 < x

/-- error: no registered substitution rule matches this expression; provide `using` with a `FeasibleSurjection` certificate -/
#guard_msgs in
reformulation target : source certificate failedAlias := by
  substitute x := Real.exp u

run_cmd do
  assertNoReformulationOutput
    `PTranTest.Reformulation.SubstitutionFailures.ShadowedReal.target
    `PTranTest.Reformulation.SubstitutionFailures.ShadowedReal.failedAlias

end ShadowedReal

/-! A manual certificate is checked against the semantic problem and map at
its actual script position, rather than against the original source. -/

def quadraticSource :=
  problem (x : ℝ)
    minimize x ^ 2

def sourceIdentityCoverage :
    FeasibleSurjection quadraticSource (fun u : ℝ => u) where
  preimage point := point.1
  rightInverse _ := rfl

def negationCoverage :
    FeasibleSurjection quadraticSource (fun u : ℝ => -u) where
  preimage point := -point.1
  rightInverse point := by simp

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
reformulation staleCertificateTarget : quadraticSource
    certificate staleCertificateAlias := by
  epigraph t as square_bound
  substitute x := u using sourceIdentityCoverage

run_cmd do
  assertNoReformulationOutput
    `PTranTest.Reformulation.SubstitutionFailures.staleCertificateTarget
    `PTranTest.Reformulation.SubstitutionFailures.staleCertificateAlias

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
reformulation wrongMapCertificateTarget : quadraticSource
    certificate wrongMapCertificateAlias := by
  substitute x := u using negationCoverage

run_cmd do
  assertNoReformulationOutput
    `PTranTest.Reformulation.SubstitutionFailures.wrongMapCertificateTarget
    `PTranTest.Reformulation.SubstitutionFailures.wrongMapCertificateAlias

end
end PTranTest.Reformulation.SubstitutionFailures
