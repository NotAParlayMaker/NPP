"""Cross-check sat-sweep/synth2.py (both modes) against exact_edge_fn.py.
For every connected graph on 2..MAXN vertices (networkx atlas), compute the least k for which
each solver says SAT, and report any disagreement. Usage: python3 cross_check_synth2.py MAXN"""
import sys, time
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
sys.path.insert(0, 'sat-sweep')
import exact_edge_fn as A
import synth2 as B

def least(sat, hi):
    for k in range(1, hi + 1):
        if sat(k): return k
    return None

maxn = int(sys.argv[1]); bad = 0; cnt = 0
for G in graph_atlas_g():
    n = G.number_of_nodes()
    if n < 2 or n > maxn or not nx.is_connected(G): continue
    T = A.target(G); hi = G.number_of_edges() + A.tau(G) + 1
    t = time.time()
    a = A.min_size(G, 1, hi, verbose=False)
    b = least(lambda k: B.solve(n, T, k)[0], hi)
    c = least(lambda k: B.solve_cegar(n, T, k)[0], hi)
    cnt += 1; ok = a == b == c; bad += not ok
    print(f"{nx.to_graph6_bytes(G, header=False).decode().strip()}\tn={n}\tm={G.number_of_edges()}\t"
          f"pred={hi-2}\texact={a}\tsynth2={b}\tcegar2={c}\t{'OK' if ok else 'MISMATCH'}\t{time.time()-t:.1f}s", flush=True)
print(f"graphs={cnt} mismatches={bad}")
