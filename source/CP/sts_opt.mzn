% --- Optimization model: balance home vs away (with tight bounds) ----
include "sts_core.mzn";

/*
  With n even, (n-1) is odd.
  Each team plays (n-1) matches, hence |home_count - away_count| >= 1 for every team.
  Therefore sum(dev) >= n. We expose these bounds to help the solver prove optimality.
*/

% dev[t] in 1..(n-1) (never 0 because n-1 is odd)
array[Teams] of var 1..(n - 1): dev =
  [ abs(home_count(t) - away_count(t)) | t in Teams ];

% objective in [n .. n*(n-1)]
var n..(n * (n - 1)): obj = sum(t in Teams)(dev[t]);

solve
  :: seq_search([
       int_search([ H[p, w] | p in Periods, w in Weeks ], first_fail, indomain_min, complete),
       int_search([ A[p, w] | p in Periods, w in Weeks ], first_fail, indomain_min, complete)
     ])
  minimize obj;

output [
  "obj=", show(obj), "\n",
  "H=\n", show(H), "\nA=\n", show(A), "\n"
];
