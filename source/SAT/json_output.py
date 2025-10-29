import os
import json

def merge_and_dump(out_dir: str, n: int, key: str, entry: dict):
    """Append/overwrite in res/SAT/<n>.json an entry <key> with the result.
    If <key> already exists, generate suffixes _2, _3, ...
    Returns (final_key, full_data_dict).
    """
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, f"{n}.json")
    data = {}
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                loaded = json.load(f)
                if isinstance(loaded, dict):
                    data = loaded
        except Exception:
            data = {}

    final_key = key
    k = 2
    while final_key in data:
        final_key = f"{key}_{k}"
        k += 1

    data[final_key] = entry
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False)
    return final_key, data
