"""Integration tests for module aggregates and the validation library."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
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

    def run_tool(self, *args, input=None, succeeds=True):
        result = subprocess.run(args, cwd=self.root, env=self.env, input=input,
                                text=True, capture_output=True, timeout=120)
        if succeeds:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def check_consumer(self):
        self.run_tool("lake", "build", "--wfail", "Morew")
        self.run_tool("lake", "env", "lean", "-DwarningAsError=true", "--stdin", input=(
            "module\n\nimport Morew\n\nexample : fixtureValue = 3 := rfl\n"
        ))

    def test_missing_aggregates_regenerate_as_importable_modules(self):
        self.run_tool("make", "imports")
        self.run_tool("make", "check-imports")
        self.check_consumer()
        self.assertFalse((self.root / "KernelCheck.lean").exists())

    def test_legacy_aggregate_fails_verification_and_is_repaired_by_generation(self):
        self.run_tool("make", "imports")
        self.write("Morew.lean", "import Morew.Leaf\n")
        self.run_tool("make", "check-imports", succeeds=False)
        self.run_tool("make", "imports")
        self.run_tool("make", "check-imports")
        self.check_consumer()

    def test_validation_library_has_normal_build_and_clean_lifecycle(self):
        self.run_tool("make", "imports")
        artifact = self.root / ".lake/build/lib/lean/KernelCheck.olean"
        self.run_tool("lake", "build", "--wfail")
        self.assertFalse(artifact.exists())
        self.run_tool("lake", "build", "--wfail", "KernelCheck")
        self.assertTrue(artifact.is_file())
        self.run_tool("lake", "clean", "morew")
        self.assertFalse(artifact.exists())
        self.run_tool("lake", "build", "--wfail", "KernelCheck")
        self.run_tool("lake", "env", "lean", "-DwarningAsError=true", "--stdin", input=(
            "module\n\nimport KernelCheck\n\nexample : True := True.intro\n"
        ))


if __name__ == "__main__":
    unittest.main()
