include "globals.mzn";

% Switches
bool: SB;        % Symmetry breaking on/off
bool: IMPLIED;   % Implied constraints on/off

% Parameters and index sets
int: n;
constraint n mod 2 = 0;

set of int: Teams   = 1..n;
set of int: Weeks   = 1..(n - 1);
set of int: Periods = 1..(n div 2);

% Decision variables
array[Weeks, Periods, Teams, Teams] of var bool: Z;       % pair in slot (i<j)
array[Teams, Teams] of var bool: B;                       % orientation for pairs (i<j)
array[Teams, Teams] of var Weeks: W;                      % week of each pair (i<j)
array[Weeks, Periods, Teams] of var bool: U;              % occupancy per slot
array[Teams, Periods] of var 1..2: C;                     % period-usage count (1..2)
array[Periods, Weeks] of var Teams: H;                    % output home
array[Periods, Weeks] of var Teams: A;                    % output away

array[Teams] of var 0..(n - 1): Hc;                       % home-count per team
array[Teams] of var 1..(n - 1): dev;                      % deviation per team


% Pair-index cleanup (self-matches and duplicates)
constraint forall(w in Weeks, p in Periods, i in Teams, j in Teams where i >= j)(
  Z[w,p,i,j] = false
);
constraint forall(i in Teams, j in Teams where i >= j)(
  B[i,j] = false /\ W[i,j] = 1 % defaults for invalid pairs
);

% Core constraints
% One match per slot
constraint forall(w in Weeks, p in Periods)(
  sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) ) = 1
);

% Each unordered pair exactly once
constraint forall(i in Teams, j in Teams where i < j)(
  sum(w in Weeks, p in Periods)( bool2int(Z[w,p,i,j]) ) = 1
);

% Weekly participation
constraint forall(w in Weeks, t in Teams)(
  sum(p in Periods)( bool2int(U[w,p,t]) ) = 1
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

% Dual viewpoint: W <-> Z 
constraint forall(i in Teams, j in Teams where i < j)(
  sum(w in Weeks)( bool2int(W[i,j] = w) ) = 1 /\ % redundant
  forall(w in Weeks)(
    bool2int(W[i,j] = w) = sum(p in Periods)( bool2int(Z[w,p,i,j]) ) % channeling W <-> Z
  )
);


% Symmetry breaking 
% Week 1 canonical pairing
constraint SB -> forall(p in Periods)(
  Z[1, p, 2*p - 1, 2*p] = true
);
% Week 1 orientation (odd home vs even)
constraint SB -> forall(p in Periods)(
  B[2*p - 1, 2*p] = true
);
% Period-label anchor: team 1's single-use period is Period 1
constraint SB -> (IMPLIED -> (C[1,1] = 1));


% implied constraints
%exact per-team period profile 
constraint IMPLIED -> forall(t in Teams, p in Periods)(
  C[t,p] = sum(w in Weeks)( bool2int(U[w,p,t]) ) % channeling C <-> U
);
constraint IMPLIED ->
  forall(t in Teams)(
    sum(p in Periods)( C[t,p] ) = n - 1 /\
    sum(p in Periods)( bool2int(C[t,p] = 1) ) = 1
  );

% alldifferent on weeks per team (stronger propagation)
constraint IMPLIED ->
  forall(t in Teams)(
    alldifferent([ W[min(t,j), max(t,j)] | j in Teams where j != t ])
  );

% global home-count balance and objective LB 
constraint IMPLIED -> (sum(t in Teams)(Hc[t]) = (n*(n-1)) div 2);


% Home counts and fairness objective
constraint forall(t in Teams)(
  Hc[t] =
    sum(j in Teams where t < j)( bool2int(B[t,j]) ) +
    sum(i in Teams where i < t)( 1 - bool2int(B[i,t]) )
);

% Objective: minimize total deviation

constraint forall(t in Teams)(
  dev[t] >=  2*Hc[t] - (n - 1) /\
  dev[t] >= -(2*Hc[t] - (n - 1))
);
var 0..(n * (n - 1)): obj = sum(t in Teams)(dev[t]);

% pruning for obj
constraint obj >= n;
constraint obj <= 2*n;

% Output construction from Z and B
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

% Output
output [
  "obj=", show(obj), "\n",
  "H=\n", show(H), "\nA=\n", show(A), "\n"
];

% Search strategy (W -> Z -> B)
solve :: seq_search([
  int_search([ W[i,j] | i in Teams, j in Teams where i < j ],
             dom_w_deg, indomain_min, complete),
  bool_search([ Z[w,p,i,j] | w in Weeks, p in Periods, i in Teams, j in Teams where i < j ],
              first_fail, indomain_max, complete),
  bool_search([ B[i,j] | i in Teams, j in Teams where i < j ],
              first_fail, indomain_max, complete)
]) minimize obj;
