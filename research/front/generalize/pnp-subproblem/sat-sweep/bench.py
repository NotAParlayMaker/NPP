import sys, time, networkx as nx
from synth2 import *
g6, k = sys.argv[1], int(sys.argv[2]); maxw = int(sys.argv[3]) if len(sys.argv)>3 else 2
solver = sys.argv[4] if len(sys.argv)>4 else 'cadical153'
G = nx.from_graph6_bytes(g6.encode()); n = G.number_of_nodes(); T = target(G)
t = time.time(); ok, circ, it, nr = solve_cegar(n, T, k, solver, maxw)
print('SAT' if ok else 'UNSAT', f'{time.time()-t:.2f}s iters={it} rows={nr}', circ,
      (all(evaluate(circ,n,r)==T[r] for r in range(1<<n)) if ok else ''))
