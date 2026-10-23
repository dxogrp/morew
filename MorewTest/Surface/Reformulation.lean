import MorewTest.Surface.Fixtures

/-!
# Surface reformulation composition

Exercise the public DSL, printer metadata, and successful reformulation composition.
-/

namespace MorewTest.Surface

open Morew
noncomputable section

/--
info: problem (x : ℝ)
  minimize (Real.log x) ^ 2
  subject to
    positive : 0 < x
-/
#guard_msgs in
#printp original

/--
info: def MorewTest.Surface.original : Problem ℝ ℝ :=
{ objective := fun x => Real.log x ^ 2, feasible := fun x => 0 < x }
-/
#guard_msgs in
#print original

reformulation transformed : original := by
  substitute x := Real.exp u
  epigraph t

/-- info: MorewTest.Surface.transformed.equivalence : GlobalEquivalence original transformed -/
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

end
end MorewTest.Surface
