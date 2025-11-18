FROM python:3.11-slim

ENV PYTHONUNBUFFERED=1 \
    PIP_NO_CACHE_DIR=1

WORKDIR /app

# 1) dipendenze di sistema (per compilare eventuali wheel di python-sat, ecc.)
RUN apt-get update && apt-get install -y --no-install-recommends \
        bash \
        build-essential \
        cmake \
        patch \
        zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

# 2) dipendenze Python
#    -> metti requirements.txt nella stessa cartella del Dockerfile
COPY requirements.txt /tmp/requirements.txt
RUN python -m pip install --upgrade pip \
    && pip install --no-cache-dir -r /tmp/requirements.txt

# 3) copia di tutto il progetto (codice + script + checker + ecc.)
COPY . /app

# 4) cartelle di output per i DIMACS
RUN mkdir -p /app/res/SAT/dimacs

# 5) rendi eseguibile lo script di lancio
RUN chmod +x /app/script/run_sat.sh

# 6) entrypoint:
#    - di default lancia N=18
#    - per N=16 puoi fare "docker run ... 16"
ENTRYPOINT ["bash", "-lc", "for N in 16 18; do /app/script/run_sat.sh \"$N\"; done"]
CMD ["18"]
