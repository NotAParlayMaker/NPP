import networkx as nx, sys
from networkx.generators.atlas import graph_atlas_g
from bc import *
rows=[]
for G in graph_atlas_g():
    n=G.number_of_nodes()
    if n<2 or not nx.is_connected(G) or G.number_of_edges()==0: continue
    g6=nx.to_graph6_bytes(G,header=False).decode().strip()
    m=G.number_of_edges(); t=tau(G)
    c,cov=bc(G); cs,_=bc(G,only_stars=True)
    try: girth=nx.girth(G)
    except Exception: girth=0
    print(g6,n,m,girth,t,m+t-1,cs,c,cov,flush=True)
