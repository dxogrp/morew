import Lake
open Lake DSL

package morewDocs where
  reservoir := false
  packagesDir := "../.lake/packages"

require morew from ".."
require verso from git "https://github.com/leanprover/verso" @ "v4.33.0"
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.33.0"

-- Resolve source URLs before module documentation jobs request them.
target apiDocs : Unit := do
  let ws ← getWorkspace
  for pkg in ws.packages do
    let _ ← (← (pkg.facetCore (Package.facetKind ++ `srcUri)).fetch).await
  let some lib := ws.findLeanLib? `Morew
    | error "Morew library not found"
  let job ← (lib.facetCore (LeanLib.facetKind ++ `docs)).fetch
  return job.map fun _ => ()

lean_lib MorewManual

@[default_target]
lean_exe morewManual where
  root := `MorewManualMain
  supportInterpreter := true
