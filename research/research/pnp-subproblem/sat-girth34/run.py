import sys, subprocess, csv, re, time, itertools, os
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from concurrent.futures import ThreadPoolExecutor
TO=int(os.environ.get('TO',600))
def girth(G):
    best=10**9
    for s in G:
        d={s:0};par={s:None};q=[s]
        for u in q:
            for w in G[u]:
                if w not in d: d[w]=d[u]+1;par[w]=u;q.append(w)
                elif par[u]!=w: best=min(best,d[u]+d[w]+1)
    return best
def tau(G):
    n=G.number_of_nodes()
    for t in range(n+1):
        for S in itertools.combinations(G.nodes,t):
            s=set(S)
            if all(u in s or v in s for u,v in G.edges): return t
def g6(G):
    return nx.to_graph6_bytes(nx.convert_node_labels_to_integers(G),header=False).decode().strip()
def run(g,k):
    t=time.time()
    try:
        o=subprocess.run(['python3','synth2.py',g,str(k)],capture_output=True,text=True,timeout=TO).stdout
    except subprocess.TimeoutExpired: return 'TIMEOUT',None,time.time()-t
    if o.startswith('SAT'):
        assert 'verified=True' in o
        return 'SAT',o.split('circuit=')[1].strip(),time.time()-t
    return 'UNSAT',None,time.time()-t
def work(G):
    g=g6(G);n=G.number_of_nodes();m=G.number_of_edges();ge=girth(G);ta=tau(G);P=m+ta-1
    log=[];k=n-1
    while k<=P+2:
        st,c,dt=run(g,k);log.append(f"{g} k={k} {st} {dt:.1f}s");print(log[-1],flush=True)
        if st=='SAT': return [g,n,m,ge,ta,P,k,'EXACT',c]
        if st=='TIMEOUT': return [g,n,m,ge,ta,P,f">={k}",'TIMEOUT','']
        k+=1
    return [g,n,m,ge,ta,P,f">{P+2}",'ABOVE','']
if __name__=='__main__':
    ns=[int(x) for x in sys.argv[1:]]
    gs=[G for G in graph_atlas_g() if G.number_of_nodes() in ns and nx.is_connected(G) and G.number_of_edges()>=G.number_of_nodes() and girth(G)<=4]
    gs.sort(key=lambda G:(G.number_of_nodes(),G.number_of_edges()))
    print(len(gs),'graphs',flush=True)
    new=not os.path.exists('results.csv')
    with ThreadPoolExecutor(2) as ex, open('results.csv','a',newline='') as f:
        w=csv.writer(f)
        if new: w.writerow('graph6,n,m,girth,tau,P,s,status,circuit'.split(','))
        for r in ex.map(work,gs): w.writerow(r);f.flush()
