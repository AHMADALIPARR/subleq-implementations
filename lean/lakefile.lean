-- Copyright (C) Ahmad <ahmedparr93@gmail.com>
-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lake
open Lake DSL

package subleq where

@[default_target]
lean_lib Subleq where

@[default_target]
lean_exe «subleq-lean» where
  root := `Main
