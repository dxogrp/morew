import PTran

/-!
# End-to-end surface tests

These declarations exercise the public DSL, mathematical printer metadata, and
proof-producing reformulation command.
-/

namespace PTranTest.Surface

open PTran
noncomputable section

def original :=
  problem (x : ℝ)
    minimize (Real.log x)^2
    subject to
      positive : 0 < x

/--
info: problem (x : ℝ)
  minimize (Real.log x) ^ 2
  subject to
    positive : 0 < x
-/
#guard_msgs in
#printp original

/--
info: def PTranTest.Surface.original : Problem ℝ ℝ :=
{ objective := fun x => Real.log x ^ 2, feasible := fun x => 0 < x }
-/
#guard_msgs in
#print original

reformulation transformed : original := by
  substitute x := Real.exp u
  epigraph t

/-- info: PTranTest.Surface.transformed.equivalence : GlobalEquivalence original transformed -/
#guard_msgs in
#check transformed.equivalence

example : GlobalEquivalence original transformed := transformed.equivalence

example (u t : ℝ) : transformed.objective (u, t) = t := rfl

example (u t : ℝ) : transformed.feasible (u, t) ↔ u ^ 2 ≤ t := Iff.rfl

/--
info: problem (u t : ℝ)
  minimize t
  subject to
    epigraph_t : u ^ 2 ≤ t
-/
#guard_msgs in
#printp transformed

/-! Grouped binders, multiple constraints, and maximization. -/

def boundedMaximum :=
  problem (x y : ℝ)
    maximize x^2 - y^2
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

/--
info: problem (x y : ℝ)
  maximize x ^ 2 - y ^ 2
  subject to
    lower : -1 ≤ x
    upper : x ≤ 1
-/
#guard_msgs in
#printp boundedMaximum

reformulation boundedHypograph : boundedMaximum
    certificate maximumCertified := by
  hypograph t

example : GlobalEquivalence boundedMaximum boundedHypograph := maximumCertified

example : GlobalEquivalence boundedMaximum boundedHypograph :=
  boundedHypograph.equivalence

example : maximumCertified = boundedHypograph.equivalence := rfl

example (x y t : ℝ) :
    boundedHypograph.feasible ((x, y), t) ↔
      -1 ≤ x ∧ x ≤ 1 ∧ t ≤ x ^ 2 - y ^ 2 := Iff.rfl

/--
info: problem (x y t : ℝ)
  maximize t
  subject to
    lower : -1 ≤ x
    upper : x ≤ 1
    hypograph_t : t ≤ x ^ 2 - y ^ 2
-/
#guard_msgs in
#printp boundedHypograph

/-! Multi-step substitution and hypograph scripts compose for maximization. -/

def logarithmicMaximum :=
  problem (x : ℝ)
    maximize (Real.log x)^2
    subject to
      positive : 0 < x

reformulation transformedMaximum : logarithmicMaximum := by
  substitute x := Real.exp u
  hypograph t

example : GlobalEquivalence logarithmicMaximum transformedMaximum :=
  transformedMaximum.equivalence

example (u t : ℝ) : transformedMaximum.objective (u, t) = t := rfl

example (u t : ℝ) : transformedMaximum.feasible (u, t) ↔ t ≤ u ^ 2 := Iff.rfl

/--
info: problem (u t : ℝ)
  maximize t
  subject to
    hypograph_t : t ≤ u ^ 2
-/
#guard_msgs in
#printp transformedMaximum

/-! Unconstrained and nonconvex problems need no special treatment. -/

def unconstrained :=
  problem (x : ℝ)
    minimize x

/--
info: problem (x : ℝ)
  minimize x
-/
#guard_msgs in
#printp unconstrained

def mixedBinders :=
  problem (n : Nat) (x y : ℝ)
    minimize n + x + y

/--
info: problem (n : Nat) (x y : ℝ)
  minimize n + x + y
-/
#guard_msgs in
#printp mixedBinders

def nonconvex :=
  problem (x : ℝ)
    minimize (x^2 - 1)^2

reformulation nonconvexEpigraph : nonconvex := by
  epigraph t

example : GlobalEquivalence nonconvex nonconvexEpigraph :=
  nonconvexEpigraph.equivalence

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    epigraph_t : (x ^ 2 - 1) ^ 2 ≤ t
-/
#guard_msgs in
#printp nonconvexEpigraph

/-! An unregistered substitution can supply its feasible-coverage witness. -/

def identitySource :=
  problem (x : ℝ)
    minimize x ^ 2

def identityCoverage :
    FeasibleSurjection identitySource (fun u : ℝ => u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation identityTarget : identitySource := by
  substitute x := u using identityCoverage

example : GlobalEquivalence identitySource identityTarget :=
  identityTarget.equivalence

example (u : ℝ) : identityTarget.objective u = u ^ 2 := rfl

/-! Generated targets remain valid sources for chained reformulations. -/

reformulation identityEpigraph : identityTarget := by
  epigraph t

example : GlobalEquivalence identityTarget identityEpigraph :=
  identityEpigraph.equivalence

example : GlobalEquivalence identitySource identityEpigraph :=
  identityTarget.equivalence.trans identityEpigraph.equivalence

/--
info: problem (u : ℝ)
  minimize u ^ 2
-/
#guard_msgs in
#printp identityTarget

/--
info: problem (u t : ℝ)
  minimize t
  subject to
    epigraph_t : u ^ 2 ≤ t
-/
#guard_msgs in
#printp identityEpigraph

/-! Generated declarations retain the reformulation command's name resolution. -/

namespace CertificateNamespaceCapture

def source :=
  problem (x : ℝ)
    minimize x

def target.source :=
  problem (x : ℝ)
    minimize -x

set_option linter.dupNamespace false in
def target.target := PTran.Problem.epigraph source

reformulation target : source := by
  epigraph t

/--
info: PTranTest.Surface.CertificateNamespaceCapture.target.equivalence : GlobalEquivalence source target
-/
#guard_msgs in
#check target.equivalence

example : GlobalEquivalence source target := target.equivalence

end CertificateNamespaceCapture

namespace UsingWitnessCapture

def source :=
  problem (x : ℝ)
    minimize x ^ 2

namespace Witnesses

def coverage :
    FeasibleSurjection source (fun u : ℝ => u) where
  preimage point := point.1
  rightInverse _ := rfl

end Witnesses

open Witnesses

def target.coverage := 0

reformulation target : source := by
  substitute x := u using coverage

example : GlobalEquivalence source target := target.equivalence

end UsingWitnessCapture

namespace DuplicatedPrefixCapture

def source :=
  problem (x : ℝ)
    minimize x ^ 2

namespace Witnesses

def coverage :
    FeasibleSurjection source (fun u : ℝ => u) where
  preimage point := point.1
  rightInverse _ := rfl

end Witnesses

open Witnesses

set_option linter.dupNamespace false in
def PTranTest.Surface.DuplicatedPrefixCapture.Witnesses.coverage := 0

reformulation target : source := by
  substitute x := u using coverage

example : GlobalEquivalence source target := target.equivalence

end DuplicatedPrefixCapture

namespace QualifiedOutputCapture

def f (x : ℝ) : ℝ := x + 1

def source :=
  problem (x : ℝ)
    minimize f x

def Nested.f (x : ℝ) : ℝ := x - 1

reformulation Nested.target : source := by
  epigraph t

example : GlobalEquivalence source Nested.target :=
  Nested.target.equivalence

example (x t : ℝ) :
    Nested.target.feasible (x, t) ↔ f x ≤ t := Iff.rfl

end QualifiedOutputCapture

namespace CrossNamespacePresentation

namespace SourceNS

abbrev Domain := ℝ

namespace Functions

def f (x : Domain) : ℝ := x + 1

end Functions


open Functions

def source :=
  problem (x : Domain)
    minimize f x

end SourceNS

namespace ConsumerNS

abbrev Domain := Nat

def f (_ : Domain) : ℝ := 0

reformulation target : SourceNS.source := by
  epigraph t

example : GlobalEquivalence SourceNS.source target := target.equivalence

example (x : SourceNS.Domain) (t : ℝ) :
    target.feasible (x, t) ↔ SourceNS.Functions.f x ≤ t := Iff.rfl

end ConsumerNS

end CrossNamespacePresentation

namespace LocalBinderResolution

def x : ℝ := 37

def source :=
  problem (x : ℝ)
    minimize x

reformulation target : source := by
  epigraph t

example (x t : ℝ) : target.feasible (x, t) ↔ x ≤ t := Iff.rfl

end LocalBinderResolution

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

/-- error: generated constraint name `epigraph_t` already exists -/
#guard_msgs in
reformulation labelCollisionTarget : generatedLabelCollision := by
  epigraph t

/-! Generated declaration names are preflighted before anything is emitted. -/

def occupiedTarget :=
  problem (x : ℝ)
    minimize x

/-- error: `PTranTest.Surface.occupiedTarget` has already been declared -/
#guard_msgs in
reformulation occupiedTarget : identitySource := by
  epigraph t

run_cmd do
  if (← Lean.getEnv).contains `PTranTest.Surface.occupiedTarget.equivalence then
    Lean.throwError "a target-name collision emitted the canonical certificate"

def dottedCollisionTarget.equivalence := 0

/-- error: `PTranTest.Surface.dottedCollisionTarget.equivalence` has already been declared -/
#guard_msgs in
reformulation dottedCollisionTarget : identitySource := by
  epigraph t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PTranTest.Surface.dottedCollisionTarget then
    Lean.throwError "a canonical-certificate collision emitted the target"
  if (PTran.Syntax.getProblemView? env `PTranTest.Surface.dottedCollisionTarget).isSome then
    Lean.throwError "a canonical-certificate collision emitted target metadata"

def occupiedAlias := 0

/-- error: `PTranTest.Surface.occupiedAlias` has already been declared -/
#guard_msgs in
reformulation aliasCollisionTarget : identitySource
    certificate occupiedAlias := by
  epigraph t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PTranTest.Surface.aliasCollisionTarget ||
      env.contains `PTranTest.Surface.aliasCollisionTarget.equivalence then
    Lean.throwError "an alias collision emitted reformulation declarations"
  if (PTran.Syntax.getProblemView? env `PTranTest.Surface.aliasCollisionTarget).isSome then
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
  if env.contains `PTranTest.Surface.duplicateTargetAlias ||
      env.contains `PTranTest.Surface.duplicateTargetAlias.equivalence ||
      env.contains `PTranTest.Surface.duplicateCertificateAlias ||
      env.contains `PTranTest.Surface.duplicateCertificateAlias.equivalence then
    Lean.throwError "duplicate output names emitted reformulation declarations"
  if (PTran.Syntax.getProblemView? env `PTranTest.Surface.duplicateTargetAlias).isSome ||
      (PTran.Syntax.getProblemView? env
        `PTranTest.Surface.duplicateCertificateAlias).isSome then
    Lean.throwError "duplicate output names emitted target metadata"

/-! Failures while checking a generated certificate also roll back the target. -/

/-- error: failed to synthesize instance of type class -/
#guard_msgs (substring := true) in
reformulation invalidCertificateTarget : identitySource := by
  substitute x := u using 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PTranTest.Surface.invalidCertificateTarget ||
      env.contains `PTranTest.Surface.invalidCertificateTarget.equivalence then
    Lean.throwError "a certificate elaboration failure emitted reformulation declarations"
  if (PTran.Syntax.getProblemView? env `PTranTest.Surface.invalidCertificateTarget).isSome then
    Lean.throwError "a certificate elaboration failure emitted target metadata"

reformulation validAfterCertificateFailure : identitySource := by
  epigraph t

example : GlobalEquivalence identitySource validAfterCertificateFailure :=
  validAfterCertificateFailure.equivalence

def notAProblem := 1

/-- error: declaration `PTranTest.Surface.notAProblem` has no registered problem presentation -/
#guard_msgs in
#printp notAProblem

end
end PTranTest.Surface
