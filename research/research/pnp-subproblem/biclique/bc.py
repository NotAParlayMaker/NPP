"""bc(G): biclique-cover circuit cost. no-sharing exact via weighted MaxSAT (RC2).
bicliques: (A,B) disjoint nonempty vertex sets, all A x B pairs are edges. cost |A|+|B|-1, plus 1 per extra biclique."""
import itertools, sys
import networkx as nx
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF

def tau(G):
    V=list(G.nodes)
    for k in range(len(V)+1):
        for T in itertools.combinations(V,k):
            S=set(T)
            if all(u in S or v in S for u,v in G.edges): return k

def bicliques(G):
    V=sorted(G.nodes); n=len(V)
    adj={v:set(G[v]) for v in V}
    out=[]
    # A subset, B subset of common neighbourhood of A, disjoint automatically (no loops); unordered pairs
    for r in range(1,n):
        for A in itertools.combinations(V,r):
            C=set.intersection(*[adj[a] for a in A])
            C=sorted(C-set(A))
            for s in range(1,len(C)+1):
                for B in itertools.combinations(C,s):
                    if (min(A)<min(B)) : out.append((A,B))
    return out

def bc(G, only_stars=False, want_cover=False):
    E=[frozenset(e) for e in G.edges]
    if not E: return 0,[]
    Bs=bicliques(G)
    if only_stars: Bs=[b for b in Bs if len(b[0])==1 or len(b[1])==1]
    w=WCNF()
    for i,(A,B) in enumerate(Bs):
        w.append([-(i+1)], weight=len(A)+len(B))   # cost |A|+|B|-1 +1
    for e in E:
        u,v=tuple(e)
        w.append([i+1 for i,(A,B) in enumerate(Bs) if (u in A and v in B) or (v in A and u in B)])
    with RC2(w) as r:
        m=r.compute(); c=r.cost
    cover=[Bs[i-1] for i in m if i>0]
    return c-1, cover

if __name__=="__main__":
    for g in sys.argv[1:]:
        G=nx.from_graph6_bytes(g.encode()); print(g,len(G.edges),tau(G),bc(G))
