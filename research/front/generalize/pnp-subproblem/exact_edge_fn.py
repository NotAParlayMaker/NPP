"""Exact circuit size of the edge function f_G(x) = OR_{uv in E} (x_u AND x_v).
Basis: fan-in-2 AND, OR, and NOT; every gate counted, inputs free.
Method: SAT exact synthesis over the full truth table (pysat / cadical).
Compares the least size with |E| + tau(G) - 1 (Note 1 of this repo)."""
import itertools, sys, time
import networkx as nx
from pysat.solvers import Cadical153
from pysat.card import CardEnc

def tau(G):
    V = list(G.nodes)
    for k in range(len(V)+1):
        for S in itertools.combinations(V, k):
            s = set(S)
            if all(u in s or v in s for u, v in G.edges): return k
def target(G):
    n = G.number_of_nodes(); idx = {v:i for i,v in enumerate(G.nodes)}
    return [int(any(((r>>idx[u])&1) and ((r>>idx[v])&1) for u,v in G.edges)) for r in range(1<<n)]

def synth(n, T, k, timeout=None):
    """Is there a circuit with exactly k gates (last gate is output) for truth table T?"""
    R = 1<<n; cnt=[0]
    def nv(): cnt[0]+=1; return cnt[0]
    cl=[]
    m = n+k
    val = {}
    for i in range(n):
        for r in range(R): val[i,r] = None  # constants, handled below
    V = {}
    for g in range(n, m):
        for r in range(R): V[g,r]=nv()
    def lit(i,r):  # returns (True/False const) or var
        if i<n: return bool((r>>i)&1)
        return V[i,r]
    tAND={g:nv() for g in range(n,m)}; tOR={g:nv() for g in range(n,m)}; tNOT={g:nv() for g in range(n,m)}
    s1={}; s2={}
    for g in range(n,m):
        cl.append([tAND[g],tOR[g],tNOT[g]])
        cl += [[-tAND[g],-tOR[g]],[-tAND[g],-tNOT[g]],[-tOR[g],-tNOT[g]]]
        for i in range(g): s1[g,i]=nv(); s2[g,i]=nv()
        cl.append([s1[g,i] for i in range(g)])
        for i,j in itertools.combinations(range(g),2): cl += [[-s1[g,i],-s1[g,j]],[-s2[g,i],-s2[g,j]]]
        if g==0: pass
        cl.append([tNOT[g]] + [s2[g,i] for i in range(g)])  # binary gates need second input
        for i in range(g): cl.append([-tNOT[g], -s2[g,i]])
        for i in range(g):          # first input index < second index for binary gates
            for j in range(i+1): cl.append([-tAND[g],-s1[g,i],-s2[g,j]]); cl.append([-tOR[g],-s1[g,i],-s2[g,j]])
        # semantics
        for r in range(R):
            o=V[g,r]
            for i in range(g):
                a=lit(i,r)
                # NOT
                pre=[-tNOT[g],-s1[g,i]]
                if a is True: cl.append(pre+[-o])
                elif a is False: cl.append(pre+[o])
                else: cl += [pre+[-a,-o], pre+[a,o]]
                for j in range(i+1,g):
                    b=lit(j,r)
                    for T_,isand in ((tAND[g],True),(tOR[g],False)):
                        pre=[-T_,-s1[g,i],-s2[g,j]]
                        def val_of(x): return x
                        # compute o <-> a op b
                        av,bv=a,b
                        # build with case analysis on constants
                        def add(c): cl.append(pre+c)
                        if isinstance(av,bool) and isinstance(bv,bool):
                            res = (av and bv) if isand else (av or bv)
                            add([o] if res else [-o])
                        elif isinstance(av,bool) or isinstance(bv,bool):
                            c,x=(av,bv) if isinstance(av,bool) else (bv,av)
                            if isand:
                                if c: add([-x,o]); add([x,-o])
                                else: add([-o])
                            else:
                                if c: add([o])
                                else: add([-x,o]); add([x,-o])
                        else:
                            if isand: add([-av,-bv,o]); add([av,-o]); add([bv,-o])
                            else: add([av,bv,-o]); add([-av,o]); add([-bv,o])
    for r in range(R): cl.append([V[m-1,r] if T[r] else -V[m-1,r]])
    # every non-output gate must be used (WLOG for exact size)
    for i in range(n,m-1):
        cl.append([s1[g,i] for g in range(i+1,m)]+[s2[g,i] for g in range(i+1,m)])
    S=Cadical153(bootstrap_with=cl)
    ok=S.solve()
    S.delete(); return ok

def min_size(G, lo, hi, verbose=True):
    n=G.number_of_nodes(); T=target(G)
    for k in range(lo,hi+1):
        t=time.time(); ok=synth(n,T,k)
        if verbose: print(f"   k={k}: {'SAT' if ok else 'UNSAT'} ({time.time()-t:.1f}s)",flush=True)
        if ok: return k
    return None

if __name__=="__main__":
    tests={"P3":nx.path_graph(3),"P4":nx.path_graph(4),"P5":nx.path_graph(5),"C3":nx.cycle_graph(3),"C4":nx.cycle_graph(4),"C5":nx.cycle_graph(5)}
    for name,G in tests.items():
        n=G.number_of_nodes(); pred=G.number_of_edges()+tau(G)-1
        print(name,"pred |E|+tau-1 =",pred,flush=True)
        print("  min =",min_size(G,1,pred+1),flush=True)
