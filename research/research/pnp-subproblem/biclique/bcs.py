"""bcs(G): biclique cover with SHARED OR-subterms (exact, MaxSAT).
cost = |S| + 2k - 1 where S = set of non-singleton OR-gates (each the union of two earlier sets / singletons), k = #bicliques."""
import itertools, sys
import networkx as nx
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF
from bc import bicliques, tau

def bcs(G, cover=False):
    V=sorted(G.nodes); n=len(V); idx={v:i for i,v in enumerate(V)}
    adj=[0]*n
    for u,v in G.edges: adj[idx[u]]|=1<<idx[v]; adj[idx[v]]|=1<<idx[u]
    if not G.number_of_edges(): return 0
    Bs=[(sum(1<<idx[a] for a in A),sum(1<<idx[b] for b in B)) for A,B in bicliques(G)]
    def cn(U):
        r=(1<<n)-1; 
        for i in range(n):
            if U>>i&1: r&=adj[i]
        return r
    Us=[U for U in range(1,1<<n) if bin(U).count('1')>=2 and cn(U)]
    Uset=set(Us)
    cnt=[0]
    def nv(): cnt[0]+=1; return cnt[0]
    bv=[nv() for _ in Bs]; sv={U:nv() for U in Us}
    w=WCNF()
    for b in bv: w.append([-b],weight=2)
    for U in Us: w.append([-sv[U]],weight=1)
    def side(U): return None if bin(U).count('1')==1 else sv[U]
    for b,(A,B) in zip(bv,Bs):
        for S in (A,B):
            x=side(S)
            if x: w.append([-b,x])
    for e in G.edges:
        u,v=1<<idx[e[0]],1<<idx[e[1]]
        w.append([b for b,(A,B) in zip(bv,Bs) if (A&u and B&v) or (A&v and B&u)])
    for U in Us:
        ds=[]
        # unordered pairs P<Q proper subsets, P|Q==U, each singleton or in Uset
        sub=[P for P in range(1,U) if P&U==P and (P in Uset or bin(P).count('1')==1)]
        for P in sub:
            for Q in sub:
                if P<Q and P|Q==U:
                    d=nv(); ds.append(d)
                    w.append([-d,-0] if False else [-d])  if False else None
                    for X in (P,Q):
                        x=side(X)
                        if x: w.append([-d,x])
        w.append([-sv[U]]+ds)
    with RC2(w) as r:
        m=r.compute(); c=r.cost
    if cover:
        return c-1,[Bs[i] for i,b in enumerate(bv) if m[b-1]>0],[U for U in Us if m[sv[U]-1]>0]
    return c-1
if __name__=="__main__":
    for g in sys.argv[1:]:
        G=nx.from_graph6_bytes(g.encode()); print(g,bcs(G,True))
