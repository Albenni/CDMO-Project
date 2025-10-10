% --- Sports Timetabling (core constraints, strengthened) ----
include "globals.mzn";

int: n;                  % number of teams (even)
constraint n mod 2 = 0;

set of int: Teams   = 1..n;
set of int: Weeks   = 1..(n - 1);
set of int: Periods = 1..(n div 2);

% Decision variables: home/away team scheduled in slot (period p, week w)
array[Periods, Weeks] of var Teams: H;
array[Periods, Weeks] of var Teams: A;

% 1) no team plays itself
constraint forall(p in Periods, w in Weeks) ( H[p, w] != A[p, w] );

% 2) weekly participation: each team appears exactly once per week
constraint forall(w in Weeks) (
  alldifferent([ H[p, w] | p in Periods ] ++ [ A[p, w] | p in Periods ])
);

% ---- Unordered pair view (redundant vars) -------------------
% For each slot, define the unordered pair (LO, HI).
array[Periods, Weeks] of var Teams: LO =
  array2d(Periods, Weeks, [ min(H[p,w], A[p,w]) | p in Periods, w in Weeks ]);
array[Periods, Weeks] of var Teams: HI =
  array2d(Periods, Weeks, [ max(H[p,w], A[p,w]) | p in Periods, w in Weeks ]);

% Encode each unordered pair as a single integer code.
% Using LO*n + HI is enough to make different unordered pairs have different codes.
array[Periods, Weeks] of var int: PAIR =
  array2d(Periods, Weeks, [ LO[p,w]*n + HI[p,w] | p in Periods, w in Weeks ]);

% 3) each unordered pair {i,j} appears exactly once in the whole season
% There are exactly |Weeks|*|Periods| = (n-1)*(n/2) = C(n,2) slots.
% 'alldifferent' on PAIR forces all unordered pairs to be distinct, hence a permutation
% of the C(n,2) possible pairs (coverage + uniqueness).
constraint alldifferent([ PAIR[p,w] | p in Periods, w in Weeks ]);

% Also helpful locally (tighter propagation): pairs inside the same week are distinct.
constraint forall(w in Weeks) (
  alldifferent([ PAIR[p,w] | p in Periods ])
);

% 4) period load: any team occurs in the same period at most twice
% Use a GCC on the (H ∪ A) of each period across all weeks — typically stronger.
constraint forall(p in Periods) (
  let {
    array[1..2*(n-1)] of var Teams: Xp = [ H[p,w] | w in Weeks ] ++ [ A[p,w] | w in Weeks ],
    array[Teams] of int: VALS = [ t | t in Teams ],
    array[Teams] of int: LOWS = [ 0 | t in Teams ],
    array[Teams] of int: UPS  = [ 2 | t in Teams ]
  } in
    global_cardinality_low_up(Xp, VALS, LOWS, UPS)
);

% ----------------- Implied constraints (redundant but helpful) ------------
% (I1) In every week, the n values in H∪A form a permutation of Teams.
% Sum equality is redundant with alldifferent but cheap and sometimes prunes early.
constraint forall(w in Weeks) (
  sum(p in Periods)(H[p,w] + A[p,w]) = n * (n + 1) div 2
);

% (I2) Each team appears exactly (n-1) times over the season (one per week).
% Redundant w.r.t. (2), but connects across weeks and may help propagation in practice.
constraint forall(t in Teams) (
  sum(p in Periods, w in Weeks) ( bool2int(H[p,w] = t) + bool2int(A[p,w] = t) ) = (n - 1)
);

% --------------- Helpers (used by the optimization model) -----------------
function var int: home_count(int: t) =
  sum(p in Periods, w in Weeks) ( bool2int(H[p, w] = t) );

function var int: away_count(int: t) =
  sum(p in Periods, w in Weeks) ( bool2int(A[p, w] = t) );
