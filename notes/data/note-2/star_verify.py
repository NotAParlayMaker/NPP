"""Exhaustively verify the star construction for every graph on n<=6 vertices.

Construction: pick a minimum vertex cover C. For each c in C build star(c) = OR over neighbours b
with {c,b} not covered by an earlier cover vertex of (x_c AND x_b), then OR the stars and the
covered-by-two leaves. Cost: one AND per edge, one OR per star, and ORs to join stars.
The point here is not the cost formula but that the built circuit is *checked*, on every input,
for every graph: a wrong builder would show up as a mismatch.
"""
import itertools

def edge_fn(E):
    def f(x):
        return any(x[u] and x[v] for u, v in E)
    return f

def build(E, cover, n):
    """Return (gate list, output wire index). Wires 0..n-1 are inputs."""
    gates = []
    def new(op, ins):
        gates.append((op, ins))
        return n + len(gates) - 1   # wire index, not gate number
    # single-edge gates for edges with both ends in C are handled by stars too; keep it simple:
    star_outs = []
    covered = set()
    for c in sorted(cover):
        terms = []
        for u, v in E:
            if c in (u, v) and frozenset((u, v)) not in covered:
                b = v if u == c else u
                terms.append(new("and", [c, b]))
                covered.add(frozenset((u, v)))
        if terms:
            w = terms[0]
            for t in terms[1:]:
                w = new("or", [w, t])
            star_outs.append(w)
    # edges not covered by any star (both ends in C) were included above; if none, add them
    for u, v in E:
        if frozenset((u, v)) not in covered:
            star_outs.append(new("and", [u, v]))
            covered.add(frozenset((u, v)))
    w = star_outs[0]
    for t in star_outs[1:]:
        w = new("or", [w, t])
    return gates, w

def eval_circuit(gates, out, n, x):
    vals = list(x)
    for op, ins in gates:
        a, b = vals[ins[0]], vals[ins[1]]
        vals.append(a and b if op == "and" else a or b)
    return vals[out]

def tau(n, E):
    for k in range(n + 1):
        for S in itertools.combinations(range(n), k):
            S = set(S)
            if all(u in S or v in S for u, v in E):
                return S
    return set(range(n))

def check_all(n):
    pairs = list(itertools.combinations(range(n), 2))
    bad = 0
    worst = 0
    total = 0
    for bits in range(1, 1 << len(pairs)):
        E = [e for i, e in enumerate(pairs) if (bits >> i) & 1]
        C = tau(n, E)
        gates, out = build(E, C, n)
        f = edge_fn(E)
        total += 1
        for x in itertools.product([False, True], repeat=n):
            if eval_circuit(gates, out, n, x) != f(x):
                bad += 1
                break
        worst = max(worst, len(gates))
    return total, bad, worst

if __name__ == "__main__":
    for n in (4, 5, 6):
        t, b, w = check_all(n)
        print(f"n={n}: graphs={t} wrong_circuits={b} max_gates={w}")
