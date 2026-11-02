# Checks and releases

Morew builds with the Lean version in `lean-toolchain` and the dependencies pinned
in `lake-manifest.json`. The default Lake targets are `Morew`, `MorewTest`, and
`Examples`: a normal build compiles the library, regression tests, and every
example. The test suite consists of Lean modules checked during compilation;
there is no separate `lake test` driver.

## Local checks

| Command | Checks |
| --- | --- |
| `make imports` | Regenerate the root import files and check that they are current. |
| `make check-imports` | Check the root import files without changing them. |
| `make build` | Regenerate imports and build all three libraries with warnings treated as errors. |
| `make lint` | Build, validate the lint driver, and lint the shipped `Morew` library. |
| `make check-kernel` | Build and recheck `Morew`, `MorewTest`, and `Examples` with one checker thread. |
| `make check` | Run the full build, lint, and kernel verification sequence. |

When adding a module, run `make imports` and commit the resulting changes to
`Morew.lean`, `MorewTest.lean`, or `Examples.lean`. CI uses the read-only import
check, so an omitted module fails CI instead of being silently added there.
`make update` updates dependencies; `make clean` removes this package's build
artifacts while retaining dependency builds.

## Automatic CI and main protection

CI runs on pull requests targeting `main` and pushes to `main`, and can also be
dispatched manually. Both Linux and macOS build all three libraries with warnings
treated as errors. Linux additionally checks aggregate imports, runs the `Morew`
linters, and tests the release verification script. Ordinary CI does not repeat
kernel rechecking; the manual release candidate workflow performs that check.
There are no scheduled workflows.

Each CI job allows 60 minutes for cold builds on slower hosted runners. A
compatible project cache lets Lake reuse unchanged compiled modules.

The `main` branch requires a pull request and these successful checks:

- `Build (ubuntu-latest)`
- `Build (macos-latest)`

The pull request must be up to date with `main` before merging. No approving
reviews are required. These protections also apply to administrators, and force
pushes and branch deletion are disabled. This protection applies only to `main`.

## Release procedure

Releases contain source code identified by a Git tag. The workflows do not bump
versions, create tags, publish a GitHub Release, or upload release assets.

1. Prepare a pull request setting `version` in `lakefile.toml` to the intended
   stable `X.Y.Z` version, with any accompanying release documentation. Merge it
   through the normal checks.
2. Choose the current `main` commit for the release. Wait for both Linux and macOS
   CI checks to succeed for that exact commit. A successful run for an earlier
   commit is insufficient.
3. Open **Actions → Release candidate → Run workflow**, select `main`, and
   dispatch while it points to the chosen commit. The workflow has no SHA input;
   it checks out the commit selected at dispatch. It verifies the source identity,
   removes the project's cached build artifacts, builds the library, tests, and
   examples again, checks imports and lint, tests release verification, and runs
   the full kernel check with `LEAN_NUM_THREADS=1`:

   ```sh
   LEAN_NUM_THREADS=1 lake env leanchecker Morew MorewTest Examples
   ```

   Record the verified version and exact source SHA from the successful run. If
   `main` advances before dispatch, verify the commit actually selected by the
   workflow and wait for its CI checks before proceeding.
4. Create the tag `vX.Y.Z` at exactly that verified SHA. Publish a stable GitHub
   Release using that tag and describe the changes in its release notes. Do not
   mark it as a prerelease or create the tag at a newer commit by accident.
5. Wait for the **Release** workflow to succeed. It checks the published tag's
   version, the tagged commit's membership in `main`, and the identity and success
   of the latest matching release candidate. This is a validation step after
   GitHub publication; it does not rerun the kernel check or publish assets.

Publishing a release is always a manual action after candidate verification.
Creating or merging the workflows does not publish a release.

## Recovery

For a transient CI, candidate, or release-workflow failure, fix the underlying
service problem and rerun the affected workflow for the same unchanged commit
and version. Check that the latest required run succeeds before continuing.

A failed Release workflow does not retract an already published GitHub Release.
If the tag or version is wrong, correct the version through a new pull request,
verify a new candidate, and publish a new version. Do not move or reuse an
existing release tag. If source changes are needed after candidate verification,
run candidate verification again for the new commit before publishing it.
