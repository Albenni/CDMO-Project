int: n;  % number of teams

% n must be even AND (n == 2 OR n > 5)
constraint n mod 2 = 0 /\ (n = 2 \/ n > 5);

set of int: Teams   = 1..n;
set of int: Weeks   = 1..(n - 1);
set of int: Periods = 1..(n div 2);

% Output for the checker (period x week):
% H[p,w] = home team id, A[p,w] = away team id
% We define home/away canonically from the unordered pair:
% home = smaller id, away = larger id (kills home/away symmetry)
array[Periods, Weeks] of var Teams: H;  % home
array[Periods, Weeks] of var Teams: A;  % away

% Z[w,p,i,j] = true iff in week w, period p the match {i,j} is scheduled with i<j
% We encode each unordered pair once only, so we only allow i<j
% We still keep a rectangular array and forbid i>=j below
array[Weeks, Periods, Teams, Teams] of var bool: Z;

% Channel variables: U[w,p,t] = true iff team t occupies slot (w,p)
% This ties the "pair view" (Z) to the "slot-occupancy view" (U)
array[Weeks, Periods, Teams] of var bool: U;

% Forbid invalid Z indices to keep the array rectangular but remove i>=j
constraint forall(w in Weeks, p in Periods, i in Teams, j in Teams where i >= j)(
  Z[w,p,i,j] = false
);

% Symmetry breaking: week 1 is the canonical 1-factor (1,2), (3,4), ..., (n-1,n)
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

% 3) Each unordered pair (i,j) appears exactly once in the season
constraint forall(i in Teams, j in Teams where i < j)(
  sum(w in Weeks, p in Periods)( bool2int(Z[w,p,i,j]) ) = 1
);

% 4) Period load cap: any team uses the same period at most twice
constraint forall(t in Teams, p in Periods)(
  sum(w in Weeks)( bool2int(U[w,p,t]) ) <= 2
);

% Channelling U <-> Z:
% U[w,p,t] is 1 iff t shows up in Z[w,p,*,*] as either the left (t<j) or right (i<t) element
% Strong propagation since it links the two views tightly
constraint forall(w in Weeks, p in Periods, t in Teams)(
  bool2int(U[w,p,t]) =
    sum(j in Teams where t < j)( bool2int(Z[w,p,t,j]) ) +
    sum(i in Teams where i < t)( bool2int(Z[w,p,i,t]) )
);

% Derive H/A canonically from Z: home = smaller id, away = larger id
constraint forall(w in Weeks, p in Periods)(
  H[p,w] = sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) * i ) /\
  A[p,w] = sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) * j )
);

solve satisfy;

output [ "H=\n", show(H), "\nA=\n", show(A), "\n" ];
