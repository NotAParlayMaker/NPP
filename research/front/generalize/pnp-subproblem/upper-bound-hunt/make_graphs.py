"""Write the test graphs as JSON (graphs/NAME.json) with n, |E|, girth, tau, predicted |E|+tau-1."""
import itertools, json, os, random
import networkx as nx

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'graphs')
os.makedirs(D, exist_ok=True)


def tau(G):
    V = list(G.nodes)
    for k in range(len(V) + 1):
        for S in itertools.combinations(V, k):
            s = set(S)
            if all(u in s or v in s for u, v in G.edges): return k


def girth(G):
    g = nx.girth(G)
    return None if g == float('inf') else int(g)


def save(name, G):
    G = nx.convert_node_labels_to_integers(G)
    t = tau(G); g = girth(G)
    d = dict(name=name, n=G.number_of_nodes(), edges=sorted(map(list, map(sorted, G.edges))),
             m=G.number_of_edges(), tau=t, girth=g, pred=G.number_of_edges() + t - 1)
    json.dump(d, open(os.path.join(D, name + '.json'), 'w'))
    print(name, d['n'], d['m'], 'girth', g, 'tau', t, 'pred', d['pred'])


def pendant(G, v, L):
    G = G.copy(); prev = v
    for _ in range(L):
        w = max(G.nodes) + 1; G.add_edge(prev, w); prev = w
    return G


if __name__ == '__main__':
    save('C4_sanity', nx.cycle_graph(4))
    save('C5', nx.cycle_graph(5))
    save('petersen', nx.petersen_graph())
    save('heawood', nx.heawood_graph())
    save('GP7_2', nx.generalized_petersen_graph(7, 2) if hasattr(nx, 'generalized_petersen_graph') else None)
