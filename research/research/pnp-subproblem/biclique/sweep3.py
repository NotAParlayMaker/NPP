import networkx as nx, sys, time, multiprocessing as mp
from networkx.generators.atlas import graph_atlas_g
from bcs import *
def job(g,q):
    q.put(bcs(nx.from_graph6_bytes(g.encode())))
TO=float(sys.argv[2])
done=set(l.split()[0] for l in open('sweep2.out'))
for G in graph_atlas_g():
    n=G.number_of_nodes()
    if n!=int(sys.argv[1]) or not nx.is_connected(G): continue
    g6=nx.to_graph6_bytes(G,header=False).decode().strip()
    if g6 in done: continue
    q=mp.Queue(); p=mp.Process(target=job,args=(g6,q)); t=time.time(); p.start(); p.join(TO)
    if p.is_alive(): p.kill(); print(g6,'TIMEOUT',flush=True); continue
    print(g6,q.get(),round(time.time()-t,2),flush=True)
