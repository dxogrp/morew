import Lake
open Lake DSL

package morewDocs where
  reservoir := false
  packagesDir := "../.lake/packages"

require morew from ".."
require verso from git "https://github.com/leanprover/verso" @ "v4.33.0"
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.33.0"

lean_lib MorewManual

@[default_target]
lean_exe morewManual where
  root := `MorewManualMain
  supportInterpreter := true
