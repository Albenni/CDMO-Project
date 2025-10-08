% --- Sports Timetabling (core constraints) ------------------
include "globals.mzn";

int: n;                  % number of teams (even)
constraint n mod 2 = 0;

set of int: Teams   = 1..n;
set of int: Weeks   = 1..(n - 1);
set of int: Periods = 1..(n div 2);

% home / away team scheduled in slot (period p, week w)
array[Periods, Weeks] of var Teams: H;
array[Periods, Weeks] of var Teams: A;

% 1) no team plays itself
constraint forall(p in Periods, w in Weeks) ( H[p, w] != A[p, w] );

% 2) weekly participation: each team appears exactly once per week
constraint forall(w in Weeks) (
  alldifferent([ H[p, w] | p in Periods ] ++ [ A[p, w] | p in Periods ])
);

% 3) each unordered pair {i,j} plays exactly once over the season
constraint forall(i in Teams, j in Teams where i < j) (
  sum(p in Periods, w in Weeks) (
    bool2int(H[p, w] = i /\ A[p, w] = j) +
    bool2int(H[p, w] = j /\ A[p, w] = i)
  ) = 1
);

% 4) period load: any team occurs in the same period at most twice
constraint forall(p in Periods, t in Teams) (
  sum(w in Weeks) ( bool2int(H[p, w] = t) + bool2int(A[p, w] = t) ) <= 2
);

% mild symmetry breaking: anchor the very first slot
constraint H[1,1] = 1 /\ A[1,1] = 2;

% helpers (used by the objective in the optimization model)
function var int: home_count(int: t) =
  sum(p in Periods, w in Weeks) ( bool2int(H[p, w] = t) );

function var int: away_count(int: t) =
  sum(p in Periods, w in Weeks) ( bool2int(A[p, w] = t) );
