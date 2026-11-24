import networkx as nx, sys, time
from networkx.generators.atlas import graph_atlas_g
from bcs import *
nmax=int(sys.argv[1])
for G in graph_atlas_g():
    n=G.number_of_nodes()
    if n<2 or n>nmax or not nx.is_connected(G): continue
    g6=nx.to_graph6_bytes(G,header=False).decode().strip()
    t=time.time(); c=bcs(G)
    print(g6,c,round(time.time()-t,2),flush=True)
