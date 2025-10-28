% --- Sports Timetabling (OPT) — compact & strong, no obj=n, no fixed split ----
% Variables & modeling ideas:
%   - Z[w,p,i,j]  : unordered match {i,j} (i<j) scheduled in slot (w,p)
%   - B[i,j]      : orientation for {i,j} (i<j): true => i is HOME, false => j is HOME
%   - W[i,j]      : week index in which {i,j} is played (dual viewpoint)
%   - U[w,p,t]    : team t occupies period p in week w (either side)
%   - C[t,p]      : period-usage count for team t on period p (exact profile 1..2; one single-usage)
%   - H[p,w],A[p,w]: (period × week) output matrices for the checker

include "globals.mzn";

int: n;  constraint n mod 2 = 0;

set of int: Teams   = 1..n;
set of int: Weeks   = 1..(n - 1);
set of int: Periods = 1..(n div 2);

% ------------------------ Decision / output variables ---------------------
array[Weeks, Periods, Teams, Teams] of var bool: Z;     % unordered pairs (i<j)
array[Teams, Teams] of var bool: B;                      % orientation for pairs (i<j)
array[Teams, Teams] of var Weeks: W;                     % week of each pair (i<j)
array[Weeks, Periods, Teams] of var bool: U;             % occupancy (per team, per slot)
array[Teams, Periods] of var 1..2: C;                    % exact period-usage profile (1 or 2)
array[Periods, Weeks] of var Teams: H;                   % home team id (output)
array[Periods, Weeks] of var Teams: A;                   % away team id (output)

% ------------------------ Index cleanup & harmless fixing -----------------
% Keep arrays rectangular; forbid i>=j entries in Z; disable B/W outside i<j.
constraint forall(w in Weeks, p in Periods, i in Teams, j in Teams where i >= j)(
  Z[w,p,i,j] = false
);
constraint forall(i in Teams, j in Teams where i >= j)(
  B[i,j] = false /\ W[i,j] = 1
);

% ------------------------ Core round-robin structure ---------------------
% (1) Exactly one match per slot (w,p)
constraint forall(w in Weeks, p in Periods)(
  sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) ) = 1
);

% (2) Each unordered pair {i,j} exactly once in the whole season
constraint forall(i in Teams, j in Teams where i < j)(
  sum(w in Weeks, p in Periods)( bool2int(Z[w,p,i,j]) ) = 1
);

% (3) Channeling U <-> Z (who occupies a slot)
constraint forall(w in Weeks, p in Periods, t in Teams)(
  bool2int(U[w,p,t]) =
    sum(j in Teams where t < j)( bool2int(Z[w,p,t,j]) ) +
    sum(i in Teams where i < t)( bool2int(Z[w,p,i,t]) )
);

% (4) Weekly participation: each team plays exactly once per week
constraint forall(w in Weeks, t in Teams)(
  sum(p in Periods)( bool2int(U[w,p,t]) ) = 1
);

% ------------------------ Exact period-usage profile (implied, explicit) --
% C[t,p] counts how many weeks team t uses period p; the exact profile is (2,...,2,1).
constraint forall(t in Teams, p in Periods)(
  C[t,p] = sum(w in Weeks)( bool2int(U[w,p,t]) )
);
constraint forall(t in Teams)(
  sum(p in Periods)( C[t,p] ) = n - 1 /\
  sum(p in Periods)( bool2int(C[t,p] = 1) ) = 1
);

% (Light SB on periods): fix the single-usage period for team 1 to be Period 1.
constraint C[1,1] = 1;

% ------------------------ Dual viewpoint: weeks per pair ------------------
% W[i,j] = w  <->  the pair {i,j} is materialized in week w (on some period).
constraint forall(i in Teams, j in Teams where i < j)(
  % choose exactly one week
  sum(w in Weeks)( bool2int(W[i,j] = w) ) = 1 /\
  % coherence with Z inside that week
  forall(w in Weeks)(
    bool2int(W[i,j] = w) = sum(p in Periods)( bool2int(Z[w,p,i,j]) )
  )
);

% Strong global: a team's weeks must be all different
constraint forall(t in Teams)(
  alldifferent([ W[min(t,j), max(t,j)] | j in Teams where j != t ])
);

% ------------------------ Symmetry breaking on Week 1 ---------------------
% Fix Week 1 to the canonical perfect matching: (1,2), (3,4), ..., (n-1,n)
constraint forall(p in Periods)(
  Z[1, p, 2*p - 1, 2*p] = true
);
% Deterministic orientation for those pairs (odd at home vs even)
constraint forall(p in Periods)(
  B[2*p - 1, 2*p] = true
);

% ------------------------ Home/Away balance & objective -------------------
% Home-count per team, computed purely from B
array[Teams] of var 0..(n - 1): Hc;
constraint forall(t in Teams)(
  Hc[t] =
    sum(j in Teams where t < j)( bool2int(B[t,j]) ) +
    sum(i in Teams where i < t)( 1 - bool2int(B[i,t]) )
);

% Redundant but helpful: total homes equals total matches
constraint sum(t in Teams)( Hc[t] ) = n * (n - 1) div 2;

% Deviation from the ideal split (absolute value via two inequalities)
array[Teams] of var 1..(n - 1): dev;
constraint forall(t in Teams)(
  dev[t] >=  2*Hc[t] - (n - 1) /\
  dev[t] >= -(2*Hc[t] - (n - 1))
);

% Objective: minimize total deviation (no obj = n; solver will find the optimum)
var 0..(n * (n - 1)): obj = sum(t in Teams)(dev[t]);

% ------------------------ Output construction ----------------------------
% Build H/A from Z and B without disjunctions
constraint forall(w in Weeks, p in Periods)(
  H[p,w] = sum(i in Teams, j in Teams where i < j)(
             bool2int(Z[w,p,i,j]) *
             ( i * bool2int(B[i,j]) + j * (1 - bool2int(B[i,j])) )
           ) /\
  A[p,w] = sum(i in Teams, j in Teams where i < j)(
             bool2int(Z[w,p,i,j]) *
             ( j * bool2int(B[i,j]) + i * (1 - bool2int(B[i,j])) )
           )
);

output [
  "obj=", show(obj), "\n",
  "H=\n", show(H), "\nA=\n", show(A), "\n"
];

% ------------------------ Search strategy --------------------------------
% 1) choose weeks (dual view W) with dom/wdeg
% 2) then assign pairs to slots Z
% 3) finally orient matches B
solve :: seq_search([
  int_search([ W[i,j] | i in Teams, j in Teams where i < j ],
             dom_w_deg, indomain_min, complete),
  bool_search([ Z[w,p,i,j] | w in Weeks, p in Periods, i in Teams, j in Teams where i < j ],
              first_fail, indomain_max, complete),
  bool_search([ B[i,j] | i in Teams, j in Teams where i < j ],
              first_fail, indomain_max, complete)
]) minimize obj;
