import VersoManual

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Examples.Models.SecondOrder"

#doc (Manual) "Quick start" =>
%%%
tag := "quick-start"
file := "quick-start"
htmlSplit := .never
%%%

We consider nonnegative least squares in norm form:

$$`\begin{array}{ll}
\text{minimize} & \lVert Ax-b\rVert_2 \\
\text{subject to} & x \succeq 0
\end{array}`

The optimization variable is $`x\in\mathbf{R}^n`, with parameters
$`A\in\mathbf{R}^{m\times n}` and $`b\in\mathbf{R}^m`.
The symbol $`\succeq` means componentwise inequality.

We first import the necessary modules and open the relevant namespaces:

```anchor nonnegLSSetup -defSite
import Morew.Reformulation.Conic
open Morew
open scoped Matrix
```

The following block defines the problem:

```anchor nonnegLS -defSite
noncomputable def nonnegLS (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm2 (A *ᵥ x - b)
    subject to
      nonneg : x ≥ 0
```

To rewrite the problem in conic form, we introduce epigraph variable $`t`
with $`\lVert Ax-b\rVert_2\leq t`, rewrite that bound as a
second-order cone constraint, and certify the complete problem.

```anchor conicNonnegLS -defSite
variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

reformulation conicNonnegLS : (nonnegLS A b) := by
  epigraph t as residualBound
  conic at residualBound
  rename residualBound_conic_1 to residualCone
  conic
```

The reformulation supplies equivalence and conic certificates:

```anchor nonnegLSCertificate -defSite
noncomputable example : GlobalEquivalence (nonnegLS A b) (conicNonnegLS A b) :=
  conicNonnegLS.equivalence A b
example : IsConic (conicNonnegLS A b) := conicNonnegLS.isConic A b
```

To print the conic reformulation, we use the `#printp` command:

```anchor printNonnegLS -defSite
#printp conicNonnegLS
```

```anchorInfo printNonnegLS
problem (x : Fin n → ℝ) (t : ℝ)
  minimize t
  subject to
    nonneg : x ∈ ℝ₊^n
    residualCone : (t, A *ᵥ x - b) ∈ SOC m
```
