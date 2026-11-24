"""Compare |E|+tau-1 against the exact minimum for ALL graphs on 6 vertices (n=6 closure to k=8)."""
import itertools, json, os
from exact_ref import target_mask, tau, has_4cycle
cost = {}
import sys
src = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser("~/pnp_loop/data/closure_n6.txt")
for line in open(src):
    parts = line.split()
    if len(parts) != 2:
        continue
    cost[int(parts[0], 16)] = int(parts[1])
print("masks loaded:", len(cost), "from", os.path.basename(src))
print("max cost in dump:", max(cost.values()))
n = 6
pairs = list(itertools.combinations(range(n), 2))
rows, unknown, tight, below, above = 0, 0, 0, 0, 0
mismatch_4cyc = mismatch_free = 0
free_total = 0
for bits in range(1, 1 << len(pairs)):
    E = [e for i, e in enumerate(pairs) if (bits >> i) & 1]
    t = target_mask(n, E)
    c = cost.get(t)
    f = len(E) + tau(n, E) - 1
    four = has_4cycle(n, E)
    rows += 1
    if not four:
        free_total += 1
    if c is None:
        unknown += 1
        continue
    if c == f:
        tight += 1
        continue
    if c < f:
        below += 1
        if four: mismatch_4cyc += 1
        else: mismatch_free += 1
    else:
        above += 1
print(f"graphs={rows} unknown={unknown} tight={tight} exact_below_formula={below} exact_above={above}")
print(f"4cycle-free graphs={free_total} of which mismatch={mismatch_free}; mismatches with 4cycle={mismatch_4cyc}")
