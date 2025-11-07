% ---- Switches
bool: SB;        % Symmetry breaking on/off
bool: IMPLIED;   % Implied constraints on/off

% ---- Parameters and index sets
int: n;  % number of teams
constraint n mod 2 = 0 /\ (n = 2 \/ n > 5);

set of int: Teams   = 1..n;
set of int: Weeks   = 1..(n - 1);
set of int: Periods = 1..(n div 2);

% ---- Output for the checker (period x week)
array[Periods, Weeks] of var Teams: H;  % home
array[Periods, Weeks] of var Teams: A;  % away

% ---- Pair placement and occupancy
array[Weeks, Periods, Teams, Teams] of var bool: Z;  % {i,j} in slot, i<j
array[Weeks, Periods, Teams] of var bool: U;        % occupancy
array[Teams, Periods] of var 1..2: C;               % period-usage count (for implied profile / SB anchor)

% ---- Pair-index cleanup (self-matches and duplicates)
constraint forall(w in Weeks, p in Periods, i in Teams, j in Teams where i >= j)(
  Z[w,p,i,j] = false
);

% ---- Symmetry breaking (enable with SB)
% Week 1 canonical pairing
constraint SB -> forall(p in Periods)(
  Z[1, p, 2*p - 1, 2*p] = true
);
% Optional period-label anchor (works with implied C): team 1 single-use = Period 1
constraint SB -> (IMPLIED -> (C[1,1] = 1));

% ---- Core constraints
% One match per slot
constraint forall(w in Weeks, p in Periods)(
  sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) ) = 1
);

% Weekly participation
constraint forall(w in Weeks, t in Teams)(
  sum(p in Periods)( bool2int(U[w,p,t]) ) = 1
);

% Each unordered pair exactly once
constraint forall(i in Teams, j in Teams where i < j)(
  sum(w in Weeks, p in Periods)( bool2int(Z[w,p,i,j]) ) = 1
);

% Period load cap
constraint forall(t in Teams, p in Periods)(
  sum(w in Weeks)( bool2int(U[w,p,t]) ) <= 2
);

% Channeling U <-> Z
constraint forall(w in Weeks, p in Periods, t in Teams)(
  bool2int(U[w,p,t]) =
    sum(j in Teams where t < j)( bool2int(Z[w,p,t,j]) ) +
    sum(i in Teams where i < t)( bool2int(Z[w,p,i,t]) )
);

% ---- Implied: exact per-team period profile (enable with IMPLIED)
constraint IMPLIED -> forall(t in Teams, p in Periods)(
  C[t,p] = sum(w in Weeks)( bool2int(U[w,p,t]) )
);
constraint IMPLIED ->
  forall(t in Teams)(
    sum(p in Periods)( C[t,p] ) = n - 1 /\
    sum(p in Periods)( bool2int(C[t,p] = 1) ) = 1
  );

% ---- Output construction for the checker (canonical orientation)
constraint forall(w in Weeks, p in Periods)(
  H[p,w] = sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) * i ) /\
  A[p,w] = sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) * j )
);

solve satisfy;

output [ "H=\n", show(H), "\nA=\n", show(A), "\n" ];
