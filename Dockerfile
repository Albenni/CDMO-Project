FROM minizinc/minizinc:latest

# 0) System dependencies
#    - python3 + venv + pip for SAT/CP scripts
#    - build tools for Python wheels (e.g. python-sat)
#    - bash + time for scripts / benchmarking
RUN apt-get update && apt-get install -y --no-install-recommends \
        python3 \
        python3-venv \
        python3-pip \
        bash \
        time \
        build-essential \
        cmake \
        patch \
        zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# 1) Create a virtual environment to avoid PEP 668
RUN python3 -m venv /opt/venv

# 2) Use the venv's Python/pip by default
ENV VIRTUAL_ENV=/opt/venv \
    PATH="/opt/venv/bin:${PATH}" \
    PYTHONUNBUFFERED=1 \
    PIP_NO_CACHE_DIR=1 \
    PIP_DISABLE_PIP_VERSION_CHECK=1 \
    PYTHONDONTWRITEBYTECODE=1

# 3) Python dependencies
#    - SAT: from root-level requirements.txt 
#    - CP: minizinc (Python binding) and ortools
COPY requirements.txt /tmp/requirements.txt
RUN python -m pip install --upgrade pip \
    && pip install --no-cache-dir -r /tmp/requirements.txt \
    && pip install --no-cache-dir minizinc ortools

# 4) Copy the whole project (code + scripts + checkers + etc.)
COPY . /app

# 5) Output folders
#    - SAT DIMACS (original)
#    - CP results (used by run_cp.py)
RUN mkdir -p /app/res/SAT/dimacs \
    && mkdir -p /app/res/CP

# 6) Make the SAT launch script executable 
RUN chmod +x /app/script/run_sat.sh

# 7) Entrypoint:
#    - by default runs SAT for N = 16 and 18 
ENTRYPOINT ["bash", "-lc", "for N in 16 18; do /app/script/run_sat.sh \"$N\"; done"]
CMD ["18"]
