% --- Sports Timetabling (decision-only, free search) --------
include "globals.mzn";
include "sts_core.mzn";

/* Safe symmetry breaking: fix Week 1 to the canonical pairing
   (1,2), (3,4), ..., (n-1,n). This removes a lot of symmetry
   without biasing later weeks. */
constraint forall(p in Periods) (
  H[p,1] = 2*p - 1 /\ A[p,1] = 2*p
);

/* Let the solver choose the search (free search) */
solve satisfy;

output [
  "H=\n", show(H), "\nA=\n", show(A), "\n"
];
