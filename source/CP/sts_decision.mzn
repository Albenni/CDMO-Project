% --- Feasibility model (no objective) ----------------------
include "sts_core.mzn";

solve
  :: seq_search([
       int_search([ H[p, w] | p in Periods, w in Weeks ], first_fail, indomain_min, complete),
       int_search([ A[p, w] | p in Periods, w in Weeks ], first_fail, indomain_min, complete)
     ])
  satisfy;

output [
  "H=\n", show(H), "\nA=\n", show(A), "\n"
];
