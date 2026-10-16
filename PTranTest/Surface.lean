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
info: minimize (Real.log x) ^ 2
over (x : ℝ)
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

reformulation certified / transformed : original := by
  substitute x := Real.exp u
  epigraph t

/-- info: PTranTest.Surface.certified : GlobalEquivalence original transformed -/
#guard_msgs in
#check certified

example : GlobalEquivalence original transformed := certified

example (u t : ℝ) : transformed.objective (u, t) = t := rfl

example (u t : ℝ) : transformed.feasible (u, t) ↔ u ^ 2 ≤ t := Iff.rfl

/--
info: minimize t
over (u t : ℝ)
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
info: maximize x ^ 2 - y ^ 2
over (x y : ℝ)
subject to
  lower : -1 ≤ x
  upper : x ≤ 1
-/
#guard_msgs in
#printp boundedMaximum

reformulation maximumCertified / boundedHypograph : boundedMaximum := by
  hypograph t

example : GlobalEquivalence boundedMaximum boundedHypograph := maximumCertified

example (x y t : ℝ) :
    boundedHypograph.feasible ((x, y), t) ↔
      -1 ≤ x ∧ x ≤ 1 ∧ t ≤ x ^ 2 - y ^ 2 := Iff.rfl

/--
info: maximize t
over (x y t : ℝ)
subject to
  lower : -1 ≤ x
  upper : x ≤ 1
  hypograph_t : t ≤ x ^ 2 - y ^ 2
-/
#guard_msgs in
#printp boundedHypograph

/-! Unconstrained and nonconvex problems need no special treatment. -/

def unconstrained :=
  problem (x : ℝ)
    minimize x

/--
info: minimize x
over (x : ℝ)
-/
#guard_msgs in
#printp unconstrained

def nonconvex :=
  problem (x : ℝ)
    minimize (x^2 - 1)^2

reformulation nonconvexCertified / nonconvexEpigraph : nonconvex := by
  epigraph t

example : GlobalEquivalence nonconvex nonconvexEpigraph := nonconvexCertified

/--
info: minimize t
over (x t : ℝ)
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

reformulation identityCertified / identityTarget : identitySource := by
  substitute x := u using identityCoverage

example : GlobalEquivalence identitySource identityTarget := identityCertified

example (u : ℝ) : identityTarget.objective u = u ^ 2 := rfl

/-! Expected failures are local diagnostics, not claims of non-equivalence. -/

def negativeSource :=
  problem (x : ℝ)
    minimize x
    subject to
      positive : 0 < x

/-- error: no registered substitution rule matches this expression; provide `using` with a `FeasibleSurjection` certificate -/
#guard_msgs in
reformulation noCoverageCert / noCoverageTarget : negativeSource := by
  substitute x := u ^ 2

/-- error: unknown decision variable `y` -/
#guard_msgs in
reformulation badVariableCert / badVariableTarget : negativeSource := by
  substitute y := Real.exp u

/-- error: decision variable `x` already exists -/
#guard_msgs in
reformulation collisionCert / collisionTarget : negativeSource := by
  epigraph x

/-- error: `hypograph` is not valid for a minimization problem -/
#guard_msgs in
reformulation wrongHypographCert / wrongHypographTarget : negativeSource := by
  hypograph t

/-- error: `epigraph` is not valid for a maximization problem -/
#guard_msgs in
reformulation wrongEpigraphCert / wrongEpigraphTarget : boundedMaximum := by
  epigraph t

def generatedLabelCollision :=
  problem (x : ℝ)
    minimize x
    subject to
      epigraph_t : x ≤ x

/-- error: generated constraint name `epigraph_t` already exists -/
#guard_msgs in
reformulation labelCollisionCert / labelCollisionTarget : generatedLabelCollision := by
  epigraph t

def notAProblem := 1

/-- error: declaration `PTranTest.Surface.notAProblem` has no registered problem presentation -/
#guard_msgs in
#printp notAProblem

end
end PTranTest.Surface
