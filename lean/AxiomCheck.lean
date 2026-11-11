-- Copyright (C) Ahmad <ahmedparr93@gmail.com>
-- SPDX-License-Identifier: AGPL-3.0-only

-- Prints the axioms each theorem depends on (checked by scripts/check-lean-axioms.sh).
import Subleq
open Subleq
#print axioms wrap32_bounds
#print axioms wrap32_of_bounds
#print axioms wrap32_congr
#print axioms rd_oob
#print axioms wr_oob
#print axioms rd_wr_same
#print axioms wr_size
#print axioms step_size
#print axioms step_stopped
#print axioms step_badpc
#print axioms step_trap
#print axioms step_input_empty
#print axioms step_input
#print axioms step_output
#print axioms step_ordinary
#print axioms haltOn_neg_one
#print axioms haltOn_other
#print axioms step_steps
#print axioms wrap32_idem
#print axioms wr_cells32
#print axioms step_cells32
#print axioms init_cells32
#print axioms run_stops
#print axioms run_stopped
#print axioms run_succ
#print axioms run_cells32
