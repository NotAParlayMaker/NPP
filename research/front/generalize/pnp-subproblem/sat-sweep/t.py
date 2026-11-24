import networkx as nx,sys
for name,G in [("C4",nx.cycle_graph(4)),("P4",nx.path_graph(4)),("C5",nx.cycle_graph(5)),("C6",nx.cycle_graph(6)),("P6",nx.path_graph(6))]:
    print(name, nx.to_graph6_bytes(G,header=False).decode().strip())
