from encoder import indices

def model_to_matrix(model, M, n):
    """Converte il modello in matrice (n/2) x (n-1) di [home, away].
       Se non assegnato, ignora. Presuppone encod. con exactly-one per (p,w).
    """
    periods, weeks, teams = indices(n)
    matrix = [[None for _ in range(weeks)] for __ in range(periods)]
    for p in range(periods):
        for w in range(weeks):
            found = None
            for i in teams:
                for j in teams:
                    if i == j: continue
                    if model.evaluate(M[(p,w,i,j)], model_completion=True):
                        found = [i, j]
                        break
                if found: break
            matrix[p][w] = found if found else [0, 0]
    return matrix
