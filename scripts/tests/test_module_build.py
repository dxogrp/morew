"""Integration tests for aggregate modules and downstream imports."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[2]
PACKAGES = ROOT / ".lake/packages"
MK_ALL = PACKAGES / "mathlib/.lake/build/bin/mk_all"


@unittest.skipUnless(shutil.which("lake") and MK_ALL.is_file(),
                     "requires the pinned Lean toolchain and built mk_all executable")
class ModuleBuildTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="morew-module-build-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name in ("Makefile", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(ROOT / name, self.root / name)
        (self.root / ".lake").mkdir()
        (self.root / ".lake/packages").symlink_to(PACKAGES, target_is_directory=True)
        self.write("Morew/Leaf.lean", "module\n\n@[expose] public def fixtureValue : Nat := 3\n")
        self.write("MorewTest/Leaf.lean", (
            "module\n\nimport Morew.Leaf\n\nexample : fixtureValue = 3 := rfl\n"
        ))
        self.write("Examples/Leaf.lean", (
            "module\n\nimport Morew.Leaf\n\nexample : fixtureValue + 1 = 4 := rfl\n"
        ))
        self.write("scripts/KernelCheck.lean", (ROOT / "scripts/KernelCheck.lean").read_text())
        self.env = dict(os.environ, LAKE_ARTIFACT_CACHE="false")

    def write(self, path, contents):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(contents, encoding="utf-8")

    def run_tool(self, *args, input=None):
        result = subprocess.run(args, cwd=self.root, env=self.env, input=input,
                                text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_missing_aggregates_regenerate_as_importable_modules(self):
        self.run_tool("make", "imports")
        self.run_tool("make", "check-imports")
        self.run_tool("lake", "build", "--wfail", "Morew", "MorewTest", "Examples")
        self.run_tool("lake", "env", "lean", "-DwarningAsError=true", "--stdin", input=(
            "module\n\nimport Morew\nimport MorewTest\nimport Examples\n\n"
            "example : fixtureValue = 3 := rfl\n"
        ))
        self.assertFalse((self.root / "KernelCheck.lean").exists())


@unittest.skipUnless(shutil.which("lake") and
                     (ROOT / ".lake/build/lib/lean/Morew/Reformulation/Conic.olean").is_file(),
                     "requires the pinned Lean toolchain and built Morew library")
class ReformulationImportTests(unittest.TestCase):
    def test_non_module_declarations_follow_native_visibility(self):
        # Real compilation/import tests the serialized declarations and metadata.
        producer = """\
            import Morew.Reformulation.Conic
            open Morew
            namespace Downstream

            def source := problem (x : Nat) minimize x subject to lower : 0 ≤ x
            reformulation renamed : source certificate renamedCertificate := by
              rename lower to nonnegative

            noncomputable def realSource (offset : ℝ) :=
              problem (x : ℝ) minimize x subject to lower : offset ≤ x
            variable (offset : ℝ)
            reformulation conicTarget : (realSource offset) certificate conicCertificate := by
              conic
            end Downstream
            """
        consumer = """\
            import Producer
            open Morew Downstream
            noncomputable section

            example : GlobalEquiv source renamed := renamed.equiv
            example : GlobalEquiv source renamed := renamedCertificate
            example : renamed.objective 2 = 2 := rfl

            variable (offset : ℝ)
            example : GlobalEquiv (realSource offset) (conicTarget offset) := conicCertificate offset
            example : Conic.Form (conicTarget offset) := conicTarget.conicForm offset
            example : IsConic (conicTarget offset) := conicTarget.isConic offset
            example (point : FeasiblePoint (realSource offset)) :
                ((conicTarget.equiv offset).forward.map point).val = point.val := rfl
            example (point : FeasiblePoint (conicTarget offset)) :
                ((conicTarget.equiv offset).backward.map point).val = point.val := rfl

            reformulation continued : renamed := by
              rename nonnegative to lower
            example : GlobalEquiv source continued := renamedCertificate.trans continued.equiv
            end
            """
        with tempfile.TemporaryDirectory(prefix="morew-consumer-") as directory:
            root = Path(directory)
            lean_path = os.pathsep.join(filter(None, (directory, os.environ.get("LEAN_PATH"))))
            env = dict(os.environ, LEAN_PATH=lean_path)
            for name, source in (("Producer", producer), ("Consumer", consumer)):
                path = root / f"{name}.lean"
                path.write_text(textwrap.dedent(source), encoding="utf-8")
                result = subprocess.run(
                    ["lake", "env", "lean", "-DwarningAsError=true", "--root", directory,
                     "-o", str(root / f"{name}.olean"), str(path)],
                    cwd=ROOT, env=env, text=True, capture_output=True, timeout=120,
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
