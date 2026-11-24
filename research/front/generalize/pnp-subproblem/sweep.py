import networkx as nx, sys, time
from networkx.generators.atlas import graph_atlas_g
from exact_edge_fn import *
def girth(G):
    try: return nx.girth(G)
    except Exception:
        return float('inf')
nmax=int(sys.argv[1]); nmin=int(sys.argv[2]); gmin=int(sys.argv[3])
for G in graph_atlas_g():
    n=G.number_of_nodes()
    if n<nmin or n>nmax or G.number_of_edges()==0 or not nx.is_connected(G): continue
    g=girth(G)
    if g<gmin: continue
    pred=G.number_of_edges()+tau(G)-1
    t=time.time()
    # check UNSAT below pred, SAT at pred, SAT/UNSAT at pred-1 first (cheap violation test)
    mn=None
    for k in range(1,pred):          # every size below the prediction, not just pred-1
        if synth(n,target(G),k): mn=k;break
    below=mn is not None
    at=synth(n,target(G),pred) if not below else None
    print(f"n={n} E={sorted(G.edges)} girth={g} pred={pred} "
          f"{'VIOLATION min=%d'%mn if below else ('holds, size pred achievable' if at else 'pred-1 UNSAT, pred UNSAT (>pred)')} [{time.time()-t:.1f}s]",flush=True)
