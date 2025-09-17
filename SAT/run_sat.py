import argparse, os, importlib, sys
from solve import solve_instance
from export_json import write_result

def main():
    parser = argparse.ArgumentParser(description="STS — SAT (Z3) runner")
    parser.add_argument("--n", type=int, required=True, help="Numero di team (>=2). Se dispari, verrà aggiunta una squadra fittizia.")
    parser.add_argument("--approach", type=str, default="basic", choices=["basic","symbreak"],
                        help="Nome approccio (chiave JSON)")
    parser.add_argument("--timeout", type=int, default=300, help="Timeout in secondi (default: 300)")
    parser.add_argument("--resdir", type=str, default="../res/SAT", help="Directory risultati JSON")
    parser.add_argument("--fail-on-timeout", action="store_true",
                        help="Esce con codice 124 se il tempo ≥ timeout")
    args = parser.parse_args()

    approach_name = args.approach

    # Import dinamico dell'approccio
    try:
        approach = importlib.import_module(f"approaches.{approach_name}")
    except Exception as e:
        print(f"[ERRORE] Approccio '{approach_name}' non trovato: {e}", file=sys.stderr)
        sys.exit(2)

    # Gestione n dispari: padding con squadra fittizia (bye)
    orig_n = args.n
    if orig_n < 2:
        print(f"[ERRORE] n deve essere >= 2 (dato: {orig_n})", file=sys.stderr)
        sys.exit(2)

    n_eff = orig_n if (orig_n % 2 == 0) else orig_n + 1
    if n_eff != orig_n:
        # Nota: le partite che coinvolgono la squadra fittizia (id = n_eff)
        # rappresentano turni di riposo. L'output resta nel file <orig_n>.json.
        print(f"[INFO] n={orig_n} è dispari → aggiungo squadra fittizia {n_eff} per gestire i bye.", file=sys.stderr)

    # Solve
    status, runtime_s, sol_matrix = solve_instance(n=n_eff, approach=approach, timeout_s=args.timeout)

    # Mappatura campi per export + normalizzazione runtime in caso di UNKNOWN
    if status == "SAT":
        optimal = True
        obj = None
    elif status == "UNSAT":
        optimal = True   # decision problem risolto
        obj = None
        sol_matrix = []  # nessuna soluzione
    else:  # UNKNOWN o errore
        optimal = False
        obj = None
        # se terminazione inaspettata senza risolvere, forza time=timeout per coerenza con la consegna
        runtime_s = max(runtime_s, args.timeout)

    # Stampa tempo sempre
    rt_ms = int(round(runtime_s * 1000))
    print(f"[TIME] solver={runtime_s:.3f}s ({rt_ms} ms)  timeout={args.timeout}s")
    if runtime_s >= args.timeout:
        print(f"[WARN] tempo raggiunto/superato il timeout ({args.timeout}s)", file=sys.stderr)
        # Esci con errore in CI se richiesto
        if args.fail_on_timeout:
            sys.exit(124)

    # Scrivi risultato su JSON
    # NOTA: usiamo orig_n per il nome file (es. 15.json), anche se la matrice può includere la squadra fittizia n_eff.
    outpath = write_result(n=orig_n, res_dir=args.resdir, approach=approach_name,
                           time_s=runtime_s, optimal=optimal, obj=obj, sol=sol_matrix)

    print(f"[OK] Stato={status}, runtime={int(runtime_s)}s → {outpath}")
    if n_eff != orig_n:
        print(f"[NOTE] Output include la squadra fittizia {n_eff}. Le partite con {n_eff} corrispondono a BYE (riposi).", file=sys.stderr)

if __name__ == "__main__":
    main()
