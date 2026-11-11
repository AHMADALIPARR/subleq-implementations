#!/usr/bin/env python3
# Copyright (C) Ahmad <ahmedparr93@gmail.com>
# SPDX-License-Identifier: AGPL-3.0-only

"""
Cross-Language Differential Testing Suite for SUBLEQ
Validates bit-exact observational equivalence across:
  - Racket (racket/subleq.rkt)
  - Factor (factor/subleq.factor)
  - Forth (forth/subleq.fs)
  - Lean 4 (lean/Subleq.lean)
"""

import subprocess
import json
import sys
import os

TEST_CASES = [
    {
        "name": "Countdown loop",
        "program": [3, 1, 0,  1, 0, 12,  2, 2, 3,  0, 0, 0,  -1, -1, -1],
        "input": [],
        "fuel": 50,
        "init_pc": 3,
    },
    {
        "name": "Positive subtraction (res > 0, untaken)",
        "program": [3, 4, 6,  3, 10, 0],
        "input": [],
        "fuel": 1,
        "init_pc": 0,
    },
    {
        "name": "Negative subtraction (res < 0, taken branch)",
        "program": [3, 4, 6,  5, 2, 0],
        "input": [],
        "fuel": 1,
        "init_pc": 0,
    },
    {
        "name": "Aliasing a = b (zero store)",
        "program": [3, 3, 6,  42, 0, 0],
        "input": [],
        "fuel": 1,
        "init_pc": 0,
    },
    {
        "name": "I/O stream round-trip",
        "program": [-1, 3, 3,  3, -1, 6,  -1, -1, -1],
        "input": [77],
        "fuel": 10,
        "init_pc": 0,
    },
]

app_dir = os.path.abspath(os.path.dirname(__file__))

def run_racket(tc):
    prog = " ".join(map(str, tc["program"]))
    inp = " ".join(map(str, tc["input"]))
    code = f'''#lang racket
(require (file "{app_dir}/racket/subleq.rkt"))
(define s (machine-init '({prog}) '({inp})))
(define s1 (struct-copy machine-state s [pc {tc["init_pc"]}]))
(define s-fin (machine-run s1 {tc["fuel"]}))
(displayln (vector->list (machine-state-memory s-fin)))
(displayln (machine-state-pc s-fin))
(displayln (machine-state-output s-fin))
(displayln (if (machine-state-halted s-fin) 1 0))
'''
    with open('/tmp/rkt_test.rkt', 'w') as f:
        f.write(code)
    p = subprocess.run(['racket', '/tmp/rkt_test.rkt'], capture_output=True, text=True, check=True)
    lines = p.stdout.strip().splitlines()
    mem = [int(x) for x in lines[0].strip('()').split()]
    pc = int(lines[1])
    out = [int(x) for x in lines[2].strip('()').split()] if lines[2].strip('()') else []
    halted = int(lines[3]) == 1
    return {'memory': mem, 'pc': pc, 'output': out, 'halted': halted}

def run_factor(tc):
    prog = " ".join(map(str, tc["program"]))
    inp = " ".join(map(str, tc["input"]))
    code = f'''USING: kernel sequences prettyprint accessors subleq io arrays ;
{{ {prog} }} {{ {inp} }} subleq-init
{tc["init_pc"]} >>pc
{tc["fuel"]} subleq-run
dup memory>> >array .
dup pc>> .
dup output>> >array .
halted>> .
'''
    with open('/tmp/fct_test.factor', 'w') as f:
        f.write(code)
    p = subprocess.run(['/opt/factor/factor', '/tmp/fct_test.factor'], capture_output=True, text=True, check=True)
    lines = p.stdout.strip().splitlines()
    mem = [int(x) for x in lines[0].strip('{ }').split()]
    pc = int(lines[1])
    out = [int(x) for x in lines[2].strip('{ }').split()] if lines[2].strip('{ }') else []
    halted = lines[3].strip() == 't'
    return {'memory': mem, 'pc': pc, 'output': out, 'halted': halted}

def run_forth(tc):
    prog_cells = " , ".join(map(str, tc["program"])) + " ,"
    in_cells = (" , ".join(map(str, tc["input"])) + " ,") if tc["input"] else ""
    in_load = f'IN-DIFF {len(tc["input"])} SUBLEQ-LOAD-IN' if tc["input"] else ""
    code = f'''
create PROG-DIFF {prog_cells}
create IN-DIFF {in_cells}
SUBLEQ-INIT
PROG-DIFF {len(tc["program"])} SUBLEQ-LOAD-MEM
{in_load}
{tc["init_pc"]} SUBLEQ-IP !
{tc["fuel"]} SUBLEQ-RUN
: PRINT-MEM {len(tc['program'])} 0 ?do SUBLEQ-MEM i cells + @ . loop cr ;
: PRINT-OUT SUBLEQ-OUT-COUNT @ 0 ?do SUBLEQ-OUT i cells + @ . loop cr ;
PRINT-MEM
SUBLEQ-IP @ . cr
PRINT-OUT
SUBLEQ-HALTED @ . cr
bye
'''
    with open('/tmp/fth_test.fs', 'w') as f:
        f.write(code)
    p = subprocess.run(['gforth', f'{app_dir}/forth/subleq.fs', '/tmp/fth_test.fs'], capture_output=True, text=True, check=True)
    lines = [l for l in p.stdout.strip().splitlines() if l.strip()]
    mem = [int(x) for x in lines[0].split()]
    pc = int(lines[1].strip())
    out = [int(x) for x in lines[2].split()] if len(lines) > 3 and lines[2].strip() else []
    halted = int(lines[-1].strip()) == 1
    return {'memory': mem, 'pc': pc, 'output': out, 'halted': halted}

def run_lean(tc):
    prog = "[" + ", ".join(map(str, tc["program"])) + "]"
    inp = "[" + ", ".join(map(str, tc["input"])) + "]"
    code = f'''import Subleq
open Subleq

def main : IO Unit := do
  let s : MachineState := {{
    memory := {prog},
    pc := {tc["init_pc"]},
    input := {inp},
    output := [],
    halted := false,
    fault := none
  }}
  let sFin := run s {tc["fuel"]}
  IO.println (toString sFin.memory)
  IO.println (toString sFin.pc)
  IO.println (toString sFin.output)
  IO.println (if sFin.halted then "1" else "0")
'''
    eval_file = os.path.join(app_dir, "lean", "Eval.lean")
    with open(eval_file, "w") as f:
        f.write(code)
    env = dict(os.environ, PATH=f"{os.path.expanduser('~')}/.elan/bin:" + os.environ.get("PATH", ""))
    p = subprocess.run(["lake", "env", "lean", "--run", "Eval.lean"],
                       cwd=os.path.join(app_dir, "lean"),
                       capture_output=True, text=True, check=True, env=env)
    os.remove(eval_file)
    lines = p.stdout.strip().splitlines()
    mem = json.loads(lines[0])
    pc = int(lines[1])
    out = json.loads(lines[2])
    halted = int(lines[3]) == 1
    return {'memory': mem, 'pc': pc, 'output': out, 'halted': halted}

def main():
    print("=== Running Bit-Exact Cross-Language Differential Tests ===")
    all_ok = True
    for tc in TEST_CASES:
        name = tc["name"]
        print(f"\nEvaluating test fixture: {name}")
        r = run_racket(tc)
        f = run_factor(tc)
        forth = run_forth(tc)
        l = run_lean(tc)

        print(f"  Racket: memory={r['memory']}, pc={r['pc']}, out={r['output']}, halted={r['halted']}")
        print(f"  Factor: memory={f['memory']}, pc={f['pc']}, out={f['output']}, halted={f['halted']}")
        print(f"  Forth:  memory={forth['memory']}, pc={forth['pc']}, out={forth['output']}, halted={forth['halted']}")
        print(f"  Lean 4: memory={l['memory']}, pc={l['pc']}, out={l['output']}, halted={l['halted']}")

        if r == f == forth == l:
            print(f"  => MATCH (Bit-exact observational equivalence verified across Racket, Factor, Forth, and Lean 4)")
        else:
            print(f"  => MISMATCH DETECTED!")
            all_ok = False

    if all_ok:
        print("\nALL DIFFERENTIAL TESTS PASSED BIT-EXACTLY ACROSS ALL 4 ENGINES (Racket, Factor, Forth, Lean 4)!")
        sys.exit(0)
    else:
        print("\nDifferential tests failed!")
        sys.exit(1)

if __name__ == "__main__":
    main()
