/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Affine.Support

/-! # Exact affine real-power endpoints -/

namespace MorewTest.Affine.RealPower

open Lean Lean.Elab.Command
open MorewTest.Affine

run_cmd liftTermElabM do
  assertAffine (← `(fun x : ℝ => Real.rpow x 0))
  assertAffine (← `(fun x : ℝ => Real.rpow (Real.exp x) 0))
  assertAffine (← `(fun x : ℝ => Real.rpow (2 * x - 3) 1))
  assertAffine (← `(fun x : ℝ => x ^ (0 : ℝ)))
  assertAffine (← `(fun x : ℝ => (Real.log x) ^ (0 : ℝ)))
  assertAffine (← `(fun x : ℝ => (-x - 3) ^ (1 : ℝ)))
  assertAffine (← `(fun x : ℝ => let p : ℝ := 1; x ^ p))
  assertAffine (← `(fun x : ℝ => Real.rpow x 0 + x ^ (1 : ℝ)))
  assertUnsupported (← `(fun x : ℝ => Real.rpow (x * x) 1))
  assertUnsupported (← `(fun x : ℝ => (x * x) ^ (1 : ℝ)))
  assertUnsupported (← `(fun x : ℝ => Real.rpow x (3 / 2)))
  assertUnsupported (← `(fun x : ℝ => x ^ (3 / 2 : ℝ)))
  assertUnsupported (← `(fun x : ℝ => Real.rpow x x))
  assertUnsupported (← `(fun (p : ℝ) (_hp : p = 1) => fun x : ℝ => x ^ p)) 2
  assertUnsupported (← `(fun x : ℝ => Real.rpow x (x - x)))

-- A coincident value at zero does not validate a different power instance.
run_cmd liftTermElabM do
  assertUnsupported (← `(fun x : ℝ =>
    @HPow.hPow ℝ ℝ ℝ ⟨fun _ _ => 1⟩ x 0))
  assertUnsupported (← `(fun x : ℝ =>
    @HPow.hPow ℝ ℝ ℝ ⟨fun a _ => a⟩ x 1))
  assertUnsupported (← `(fun x : ℝ =>
    @HPow.hPow ℝ ℝ ℝ ⟨fun a _ => a * a⟩ x 0))
  assertUnsupported (← `(fun x : ℝ =>
    @HPow.hPow ℝ ℝ ℝ ⟨fun a _ => a * a⟩ x 1))

end MorewTest.Affine.RealPower
