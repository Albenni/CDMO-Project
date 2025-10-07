import json, os, math

def write_result(n, res_dir, approach, time_s, optimal, obj, sol):

    # Creates results directory if not existent
    os.makedirs(res_dir, exist_ok=True)

    outpath = os.path.join(res_dir, f"{n}.json")

    data = {}

    if os.path.exists(outpath):
        with open(outpath, "r", encoding="utf-8") as f:
            try:
                data = json.load(f)
            except Exception:
                data = {}
    
    # floor del tempo, ma se il chiamante ha deciso di forzare a 300, non lo cambiamo
    t = int(math.floor(time_s))
    data[approach] = {
        "time": t,
        "optimal": bool(optimal),
        "obj": obj,
        "sol": sol
    }
    with open(outpath, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
    return outpath
