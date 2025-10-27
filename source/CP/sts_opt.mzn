% --- Sports Timetabling (OPT) ---
% Modello compatto e forte:
% - Z[w,p,i,j] booleana per la coppia non orientata {i,j} con i<j
% - B[i,j] orientamento (i<j): true => i in casa, false => j in casa
% - W[i,j] settimana in cui si gioca la coppia {i,j} (vista duale)
% - U[w,p,t] presenza di t nello slot (w,p)
% - C[t,p] conteggio d’uso del periodo p per t (esattamente 1 o 2; un solo "1")

include "globals.mzn";

int: n;  constraint n mod 2 = 0;

set of int: Teams   = 1..n;
set of int: Weeks   = 1..(n - 1);
set of int: Periods = 1..(n div 2);

% ------------------------ Variabili --------------------------------------

% Match non orientati: Z[w,p,i,j] = true  <=> in (w,p) si gioca {i,j} con i<j
array[Weeks, Periods, Teams, Teams] of var bool: Z;

% Orientamento per coppia {i,j} con i<j: true => i è in casa (home), false => j è in casa
array[Teams, Teams] of var bool: B;

% Settimana in cui cade la coppia {i,j} (i<j): dominio 1..n-1
array[Teams, Teams] of var Weeks: W;

% Presenza del team t nel periodo p della settimana w (uno solo per set.)
array[Weeks, Periods, Teams] of var bool: U;

% Conteggio d’uso per periodo (profilo esatto 1..2 e un solo "1" per squadra)
array[Teams, Periods] of var 1..2: C;

% Output richiesto (period x week)
array[Periods, Weeks] of var Teams: H;  % home
array[Periods, Weeks] of var Teams: A;  % away

% --------------------- Pulizia indici e canali base ----------------------

% Forbid invalid indices per mantenere l'array rettangolare
constraint forall(w in Weeks, p in Periods, i in Teams, j in Teams where i >= j)(
  Z[w,p,i,j] = false
);

% Disattiva le B non valide e fissa le W non usate (i>=j) ad una costante
constraint forall(i in Teams, j in Teams where i >= j)(
  B[i,j] = false /\ W[i,j] = 1
);

% 1) Esattamente un match per slot (w,p)
constraint forall(w in Weeks, p in Periods)(
  sum(i in Teams, j in Teams where i < j)( bool2int(Z[w,p,i,j]) ) = 1
);

% 2) Ogni coppia {i,j} esattamente una volta in tutta la stagione
constraint forall(i in Teams, j in Teams where i < j)(
  sum(w in Weeks, p in Periods)( bool2int(Z[w,p,i,j]) ) = 1
);

% 3) Channeling U <-> Z (occupazione slot da parte del team)
constraint forall(w in Weeks, p in Periods, t in Teams)(
  bool2int(U[w,p,t]) =
    sum(j in Teams where t < j)( bool2int(Z[w,p,t,j]) ) +
    sum(i in Teams where i < t)( bool2int(Z[w,p,i,t]) )
);

% 4) Partecipazione settimanale: ogni squadra gioca esattamente una volta
constraint forall(w in Weeks, t in Teams)(
  sum(p in Periods)( bool2int(U[w,p,t]) ) = 1
);

% 5) Profilo periodi esatto: ogni C[t,p] è 1 o 2, somma = n-1, un solo "1"
constraint forall(t in Teams, p in Periods)(
  C[t,p] = sum(w in Weeks)( bool2int(U[w,p,t]) )
);
constraint forall(t in Teams)(
  sum(p in Periods)( C[t,p] ) = n - 1 /\
  sum(p in Periods)( bool2int(C[t,p] = 1) ) = 1
);

% (SB su periodi) Il "periodo singolo" della squadra 1 è il Periodo 1
constraint C[1,1] = 1;

% -------------------- Vista duale sulle settimane ------------------------

% Channeling: W[i,j] = w  <->  {i,j} si gioca nella settimana w
constraint forall(i in Teams, j in Teams where i < j)(
  % Esattamente una settimana per coppia
  sum(w in Weeks)( bool2int(W[i,j] = w) ) = 1 /\
  % Coerenza con Z
  forall(w in Weeks)(
    bool2int(W[i,j] = w) = sum(p in Periods)( bool2int(Z[w,p,i,j]) )
  )
);

% (globale forte) Ogni squadra gioca in settimane tutte diverse
constraint forall(t in Teams)(
  alldifferent([ W[min(t,j), max(t,j)] | j in Teams where j != t ])
);

% --------------------- Symmetry breaking (etichetta/settimane) -----------

% Settimana 1 canonica: perfetta abbinata (1,2),(3,4),... nel periodo corrispondente
constraint forall(p in Periods)(
  Z[1, p, 2*p - 1, 2*p] = true
);

% Orientazione deterministica per quelle coppie: dispari in casa vs pari
constraint forall(p in Periods)(
  B[2*p - 1, 2*p] = true
);

% --------------------- Bilanciamento Home/Away e Obiettivo ---------------

% Conteggio "home" per squadra, espresso solo tramite B (senza X)
array[Teams] of var 0..(n - 1): Hc;
constraint forall(t in Teams)(
  Hc[t] =
    sum(j in Teams where t < j)( bool2int(B[t,j]) ) +
    sum(i in Teams where i < t)( 1 - bool2int(B[i,t]) )
);

% Uguaglianza implicita (ridondante ma utile a propagazione)
constraint sum(t in Teams)( Hc[t] ) = n * (n - 1) div 2;

% Split ottimo noto per n pari: odd -> H_hi, even -> H_lo
int: H_hi = n div 2;
int: H_lo = H_hi - 1;

constraint forall(t in Teams)(
  if t mod 2 = 1 then Hc[t] = H_hi else Hc[t] = H_lo endif
);

% Deviazione e obiettivo (feasibility-at-optimum: obj = n)
array[Teams] of var 1..(n - 1): dev;
constraint forall(t in Teams)(
  dev[t] >=  2*Hc[t] - (n - 1) /\
  dev[t] >= -(2*Hc[t] - (n - 1))
);

var n..(n * (n - 1)): obj = sum(t in Teams)(dev[t]);
constraint obj = n;

% --------------------------- Output --------------------------------------

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

% --------------------------- Ricerca -------------------------------------
% 1) assegna prima le settimane (vista duale) con dom/wdeg
% 2) poi gli slot Z
% 3) infine le orientazioni B
solve :: seq_search([
  int_search([ W[i,j] | i in Teams, j in Teams where i < j ],
             dom_w_deg, indomain_min, complete),
  bool_search([ Z[w,p,i,j] | w in Weeks, p in Periods, i in Teams, j in Teams where i < j ],
              first_fail, indomain_max, complete),
  bool_search([ B[i,j] | i in Teams, j in Teams where i < j ],
              first_fail, indomain_max, complete)
]) minimize obj;
