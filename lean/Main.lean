-- Copyright (C) Ahmad <ahmedparr93@gmail.com>
-- SPDX-License-Identifier: AGPL-3.0-only

import Subleq.Machine
open Subleq

/-- Parse `N m0..mN-1 K i0..iK-1 FUEL` (semantics/subleq-spec.md §6). -/
def parseInput (s : String) : Except String (List Int × List Int × Nat) := do
  let norm := s.map (fun c => if c.isWhitespace then ' ' else c)
  let toks := (norm.splitOn " ").filter (fun t => t != "")
  let nums : List Int ← toks.mapM fun t =>
    match t.toInt? with
    | some v => pure v
    | none => throw s!"non-integer token: {t}"
  match nums with
  | [] => throw "empty input"
  | n :: rest =>
    if n < 0 then throw "negative N" else
    let image := rest.take n.toNat
    let rest := rest.drop n.toNat
    if image.length ≠ n.toNat then throw "short image" else
    match rest with
    | [] => throw "missing K"
    | k :: rest =>
      if k < 0 then throw "negative K" else
      let input := rest.take k.toNat
      let rest := rest.drop k.toNat
      if input.length ≠ k.toNat then throw "short input" else
      match rest with
      | [fuel] => if fuel < 0 then throw "negative FUEL" else pure (image, input, fuel.toNat)
      | _ => throw "expected exactly one FUEL value"

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match parseInput text with
    | .ok (image, input, fuel) =>
      IO.print (render (run fuel (init image input)))
      pure 0
    | .error e =>
      IO.eprintln s!"subleq-lean: {e}"
      pure 1
  | _ =>
    IO.eprintln "usage: subleq-lean INPUT-FILE"
    pure 2
