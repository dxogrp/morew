/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.ObjectiveCertificates

/-! Imported opaque objective certificates and generated forms remain usable. -/

namespace MorewTest.ImportCompatibility.ObjectiveCertificates

open Morew MorewTest.Reformulation.ObjectiveCertificates
noncomputable section

variable (f : ℝ → ℝ) (affine : Affine.Certified f)
  (convex : QuadConic.CertifiedMin f) (concave : QuadConic.CertifiedMax f)

reformulation importedAffine : (minimum f) := by
  conic using affineCertificate f affine

reformulation importedMin : (quadraticMin f) := by
  qconic using minCertificate f convex

reformulation importedMax : (maximum f) := by
  qconic using maxCertificate f concave

example : Conic.Form (importedAffine f) := importedAffine.conicForm f affine
example : QuadConic.Form (importedMin f) := importedMin.quadConicForm f convex
example : QuadConic.Form (importedMax f) := importedMax.quadConicForm f concave
example : GlobalEquiv (minimum f) (importedMin f) :=
  (quadraticMin.equiv f).trans (importedMin.equiv f)
example : (importedMin.quadConicForm f convex).data.sense = .minimize := rfl
example : (importedMax.quadConicForm f concave).data.sense = .maximize := rfl
example (x : ℝ) : (importedMax f).objective x = f x := rfl

end
end MorewTest.ImportCompatibility.ObjectiveCertificates
