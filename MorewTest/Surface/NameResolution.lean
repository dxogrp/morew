import Morew

/-!
# Surface name resolution

Exercise namespaces, declaration capture, and source-name resolution.
-/

namespace MorewTest.Surface

open Morew
noncomputable section

/-! Generated declarations retain the reformulation command's name resolution. -/

namespace CertificateNamespaceCapture

def source :=
  problem (x : ℝ)
    minimize x

def target.source :=
  problem (x : ℝ)
    minimize -x

set_option linter.dupNamespace false in
def target.target := Morew.Problem.epigraph source

reformulation target : source := by
  epigraph t

/--
info: MorewTest.Surface.CertificateNamespaceCapture.target.equivalence : GlobalEquivalence source target
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
def MorewTest.Surface.DuplicatedPrefixCapture.Witnesses.coverage := 0

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

end
end MorewTest.Surface
