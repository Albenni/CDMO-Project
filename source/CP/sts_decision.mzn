% --- Sports Timetabling (decision-only, 0-1 lean + channeling) ---
int: n;                 % even
constraint n mod 2 = 0;

set of int: Teams   = 1..n;
set of int: Weeks   = 1..(n - 1);
set of int: Periods = 1..(n div 2);

% Output (period x week) required by the checker
array[Periods, Weeks] of var Teams: H;  % home
array[Periods, Weeks] of var Teams: A;  % away

% Z[w,p,i,j] = true  <=> in week w, period p the match (i,j) with i<j is scheduled
array[Weeks, Periods, Teams, Teams] of var bool: Z;

% Channel variables: U[w,p,t] = true <=> team t occupies period p in week w
array[Weeks, Periods, Teams] of var bool: U;

% Forbid invalid indices (keep the array rectangular, but kill i>=j)
constraint forall(w in Weeks, p in Periods, i in Teams, j in Teams where i >= j)(
  Z[w,p,i,j] = false
);

% (SB) Week-1 canonical 1-factor: (1,2), (3,4), ..., (n-1,n)
constraint forall(p in Periods)(
  Z[1, p, 2*p - 1, 2*p] = true
);

% 1) Exactly one match per slot (w,p)
constraint forall(w in Weeks, p in Periods)(
  sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) ) = 1
);

% 2) Weekly participation: each team plays exactly once per week (via U)
constraint forall(w in Weeks, t in Teams)(
  sum(p in Periods)( bool2int(U[w,p,t]) ) = 1
);

% 3) Each unordered pair (i,j) exactly once over the season
constraint forall(i in Teams, j in Teams where i < j)(
  sum(w in Weeks, p in Periods)( bool2int(Z[w,p,i,j]) ) = 1
);

% 4) Period load: any team uses the same period at most twice over all weeks
constraint forall(t in Teams, p in Periods)(
  sum(w in Weeks)( bool2int(U[w,p,t]) ) <= 2
);

% Channeling U <-> Z (exact equality, very helpful for CP-SAT presolve)
constraint forall(w in Weeks, p in Periods, t in Teams)(
  bool2int(U[w,p,t]) =
    sum(j in Teams where t < j)( bool2int(Z[w,p,t,j]) ) +
    sum(i in Teams where i < t)( bool2int(Z[w,p,i,t]) )
);

% Derive H/A canonically from Z (DEC only): H = smaller id, A = larger id
constraint forall(w in Weeks, p in Periods)(
  H[p,w] = sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) * i ) /\
  A[p,w] = sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) * j )
);

solve satisfy;

output [ "H=\n", show(H), "\nA=\n", show(A), "\n" ];
