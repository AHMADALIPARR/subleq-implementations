import Lake
open Lake DSL
open System (FilePath)

-- Isolated formal project for checked 16-bit integer formatting.
-- This lakefile is self-contained and must not be used to build
-- the repository's existing lean/ or lean-fault/ trees.

package «intfmt» where
  extraDepTargets := #[`checkArtifact]

/-- SHA-256 + byte-identity check of the official `intfmt.dec` artifact,
the embedded copy, `Image.lean`, and the generated chunk / bind modules.
A change to the `.dec` file or the expected digest fails `lake build`.
This is a script check (not `native_decide` / `#eval`). -/
target checkArtifact pkg : FilePath := Job.async do
  let sh := pkg.dir / "check-image.sh"
  let log := pkg.buildDir / "check-artifact.log"
  let out ← IO.Process.output {
    cmd := "bash"
    args := #[sh.toString]
    cwd := pkg.dir
  }
  IO.FS.createDirAll pkg.buildDir
  IO.FS.writeFile log (out.stdout ++ out.stderr)
  if out.exitCode != 0 then
    IO.eprint out.stderr
    error "check-image.sh failed: artifact hash, Image.lean, DecChunks, or DecBindData mismatch"
  return log

lean_lib «IntFmt» where
  globs := #[.andSubmodules `IntFmt, .one `IntFmt]
  extraDepTargets := #[`checkArtifact]

@[default_target]
lean_exe «intfmt» where
  root := `Main
  supportInterpreter := true
  extraDepTargets := #[`checkArtifact]
