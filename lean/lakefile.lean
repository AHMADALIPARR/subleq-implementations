-- Copyright (C) Ahmad <ahmedparr93@gmail.com>
-- SPDX-License-Identifier: AGPL-3.0-only

import Lake
open Lake DSL

package «subleq» where

lean_lib «Subleq» where

lean_lib «Theorems» where

@[default_target]
lean_exe «subleq» where
  root := `Main
