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


def gp(n, k):
    G = nx.Graph()
    for i in range(n):
        G.add_edge(i, (i + 1) % n); G.add_edge(i, n + i); G.add_edge(n + i, n + (i + k) % n)
    return G


def random_girth5(n, rng, extra_tries=400):
    """Random connected graph with girth >= 5: random spanning tree, then random edges kept
    when they create no cycle shorter than 5 (i.e. endpoints at distance >= 4)."""
    G = nx.Graph(); G.add_nodes_from(range(n))
    order = list(range(n)); rng.shuffle(order)
    for i in range(1, n): G.add_edge(order[i], order[rng.randrange(i)])
    target = rng.randint(n, n + n // 2)
    pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
    rng.shuffle(pairs)
    for u, v in pairs:
        if G.number_of_edges() >= target: break
        if G.has_edge(u, v): continue
        if nx.shortest_path_length(G, u, v) >= 4: G.add_edge(u, v)
    return G


if __name__ == '__main__':
    save('C4_control', nx.cycle_graph(4))
    save('C5', nx.cycle_graph(5))
    save('C7', nx.cycle_graph(7))
    C5 = nx.cycle_graph(5)
    save('C5_pend1', pendant(C5, 0, 1))
    save('C5_pendpath2', pendant(C5, 0, 2))
    save('C5_pend_adj', pendant(pendant(C5, 0, 1), 1, 1))
    save('C5_pend_nonadj', pendant(pendant(C5, 0, 1), 2, 1))
    G = C5
    for v in range(5): G = pendant(G, v, 1)
    save('C5_sun', G)  # pendant leaf at every cycle vertex
    G = C5
    for v in range(5): G = pendant(G, v, 2)
    save('C5_pendpath2_all', G)
    G = C5
    for v in (0, 2): G = pendant(G, v, 2)
    save('C5_pendpath2_x2', G)
    # two 5-cycles sharing a vertex / an edge; theta graph with three paths of length 3
    save('C5_C5_vertex', nx.compose(nx.cycle_graph(5), nx.relabel_nodes(nx.cycle_graph(5), {0: 0, 1: 5, 2: 6, 3: 7, 4: 8})))
    save('C5_C5_edge', nx.compose(nx.cycle_graph(5), nx.relabel_nodes(nx.cycle_graph(5), {0: 0, 1: 1, 2: 5, 3: 6, 4: 7})))
    th = nx.Graph([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 1), (0, 6), (6, 7), (7, 1)])
    save('theta_3_3_3', th)
    save('petersen', nx.petersen_graph())
    P = nx.petersen_graph(); P.remove_node(0); save('petersen_minus_v', P)
    P = nx.petersen_graph(); P.remove_edge(0, 1); save('petersen_minus_e', P)
    P = nx.petersen_graph(); P.remove_edge(0, 1); P.add_edge(0, 10); P.add_edge(10, 1); save('petersen_subdiv1', P)
    save('heawood', nx.heawood_graph())
    save('GP7_2', gp(7, 2))
    save('GP8_3_mobius_kantor', gp(8, 3))
    save('dodecahedron_GP10_2', nx.dodecahedral_graph())
    # control with a 4-cycle: C5 with vertex 0 duplicated (blow-up), girth 4
    B = nx.cycle_graph(5); B.add_edge(5, 1); B.add_edge(5, 4); save('C5_blowup1_control', B)
    rng = random.Random(2026)
    seen = []
    for n in (8, 8, 9, 9, 10, 10, 10, 11, 11, 12, 12, 12):
        for _ in range(200):
            G = random_girth5(n, rng)
            if nx.girth(G) >= 5 and nx.is_connected(G) and not any(nx.is_isomorphic(G, H) for H in seen):
                break
        seen.append(G)
        save(f'rand_n{n}_{len(seen):02d}', G)
