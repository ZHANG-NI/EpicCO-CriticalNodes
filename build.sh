#!/bin/bash
# Build recipe of this solver, as used for every build of the paper's runs.
# Run it from this directory:  bash build.sh <output directory>   ->  <output directory>/solver
set -e
set -o pipefail
CXX=${CXX:-g++}
command -v "$CXX" > /dev/null || { echo "no C++ compiler ($CXX) on PATH"; exit 1; }
[ -f host_main.cpp ] || { echo "host_main.cpp is missing"; exit 1; }
[ -f solver.cpp ] || { echo "solver.cpp is missing"; exit 1; }
if [ "$2" = check ]; then                   # compile errors only, no binary
  "$CXX" -std=gnu++17 -O1 -w -fsyntax-only host_main.cpp 2>&1 | tail -n 150
  exit 0
fi
"$CXX" -std=gnu++17 -O3 -march=native -w host_main.cpp -o "$1/prog" 2>&1 | tail -n 150
cat > "$1/solver" <<'LAUNCHER'
#!/usr/bin/env python3
"""solver <instance> <solution> -t <seconds> -seed <int>: one run of the program on one thread."""
import os
import sys
here = os.path.dirname(os.path.abspath(__file__))
a = sys.argv[1:]
inst, sol = a[0], a[1]
T = a[a.index("-t") + 1]
seed = a[a.index("-seed") + 1]
cmd = [os.path.join(here, "prog"), inst, T, seed, sol]
os.execv(cmd[0], cmd)
LAUNCHER
chmod +x "$1/solver"
