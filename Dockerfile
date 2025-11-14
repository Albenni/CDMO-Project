FROM python:3.11-slim
ENV PYTHONUNBUFFERED=1 PIP_NO_CACHE_DIR=1
WORKDIR /app

# (opzionale ma utile se qualche wheel deve compilare)
RUN apt-get update && apt-get install -y --no-install-recommends \
    bash build-essential cmake patch zlib1g-dev \
 && rm -rf /var/lib/apt/lists/*

# 1) dipendenze
COPY source/SAT/requirements.txt /tmp/requirements.txt
RUN python -m pip install --upgrade pip \
 && pip install --no-cache-dir -r /tmp/requirements.txt

# 2) codice + script
COPY source/SAT/ /app/source/SAT/
COPY script/ /app/script/
RUN chmod +x /app/script/run_sat_dec.sh

# 3) cartelle output
RUN mkdir -p /app/res/SAT/dimacs

# 4) entrypoint: usa lo script; CMD imposta il parametro di default (18)
ENTRYPOINT ["/bin/bash", "/app/script/run_sat_dec.sh"]
CMD ["18"]
