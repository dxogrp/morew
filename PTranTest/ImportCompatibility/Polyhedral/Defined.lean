import PTran.Reformulation

/-!
# Exported targeted-rewrite presentation

The narrow surface entry point supplies the command and stores generated labels
for consumers in a separate module. Symbolic dimensions retain their anonymous
instance parameter in both the semantic declaration and saved presentation.
-/

namespace PTranTest.ImportCompatibility.Polyhedral

open PTran
noncomputable section

def source :=
  problem (x : ℝ)
    minimize x ^ 2
    subject to
      loss : |x| ≤ 3
      remaining : max x (-x) ≤ 5

reformulation lowered : source := by
  conic at loss

example : GlobalEquivalence source lowered := lowered.equivalence

namespace SymbolicDimension

class Dimension where
  size : ℕ

variable [Dimension]

def source :=
  problem (v : Fin Dimension.size → ℝ) (t : ℝ)
    minimize t
    subject to
      infinity : ‖v‖ ≤ t
      one : ‖WithLp.toLp 1 v‖ ≤ t

reformulation lowered : source := by
  conic at infinity

example : GlobalEquivalence source lowered := lowered.equivalence

end SymbolicDimension

end
end PTranTest.ImportCompatibility.Polyhedral
