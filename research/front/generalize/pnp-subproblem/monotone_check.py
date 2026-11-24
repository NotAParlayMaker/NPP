"""For each connected girth>=5 graph on <=6 vertices: is |E|+tau-1 achievable with NO NOT gate,
and is |E|+tau-2 impossible even WITH NOT gates? (exact_edge_fn.synth, NOT forbidden by an extra unit clause)"""
import networkx as nx, time
from networkx.generators.atlas import graph_atlas_g
import exact_edge_fn as E
from pysat.solvers import Cadical153
orig=E.Cadical153
def synth_mono(n,T,k):
    # monkeypatch: wrap solver to add unit clauses -tNOT[g]; tNOT vars are created as the 3rd var per gate
    # simpler: re-encode by intercepting clause list
    class S(orig):
        def __init__(self, bootstrap_with):
            super().__init__(bootstrap_with=bootstrap_with+[[-v] for v in nots])
    nots=[]
    # reproduce variable numbering: V vars first (k*R), then tAND(k), tOR(k), tNOT(k)
    R=1<<n; base=k*R+2*k
    nots=[base+i+1 for i in range(k)]
    E.Cadical153=S
    try: return E.synth(n,T,k)
    finally: E.Cadical153=orig
for G in graph_atlas_g():
    n=G.number_of_nodes()
    if n<2 or n>6 or G.number_of_edges()==0 or not nx.is_connected(G): continue
    try: g=nx.girth(G)
    except Exception: g=float('inf')
    if g<5: continue
    T=E.target(G); pred=G.number_of_edges()+E.tau(G)-1
    lower=not any(E.synth(n,T,k) for k in range(1,pred))
    mono=synth_mono(n,T,pred); mono_below=any(synth_mono(n,T,k) for k in range(1,pred))
    print(f"n={n} E={sorted(G.edges)} girth={g} pred={pred} general_min={'pred' if lower else '<pred'} monotone_at_pred={mono} monotone_below={mono_below}",flush=True)
