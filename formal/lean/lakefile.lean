import Lake
open Lake DSL

-- Isolated formal project for checked 16-bit integer formatting.
-- This lakefile is self-contained and must not be used to build
-- the repository's existing lean/ or lean-fault/ trees.

package «intfmt» where
  -- no dependencies on the rest of the repository

lean_lib «IntFmt» where
  globs := #[.andSubmodules `IntFmt, .one `IntFmt]

@[default_target]
lean_exe «intfmt» where
  root := `Main
  supportInterpreter := true
