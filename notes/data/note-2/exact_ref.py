"""Sound exhaustive fan-in-two AND/OR circuit search.

A wire's value is a mask over the 2^n inputs. Input literal i is the mask of inputs where
x_i is true; AND is bitwise AND, OR is bitwise OR. Any circuit is reachable by repeated
AND/OR, so a BFS on masks with cost(mask) = fewest gates is exact: when the target's cost
is settled at k, no circuit uses fewer than k gates.
"""
import itertools, sys, time

G = {"c4":(4,[(0,1),(0,3),(1,2),(2,3)]),
     "c6":(6,[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]),
     "pendant6":(7,[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6)]),
     "c5":(5,[(0,1),(1,2),(2,3),(3,4),(4,0)]),
     # bowtie: two triangles sharing vertex 0
     "bowtie":(5,[(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),
     # two triangles joined by an edge c-d: 4-cycle-free
     "twin_tri":(6,[(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(2,3)])}

def target_mask(n, edges):
    m = 0
    for idx in range(1 << n):
        if any((idx >> u) & 1 and (idx >> v) & 1 for u, v in edges):
            m |= 1 << idx
    return m

def run(name, kmax, cap=3_000_000, tmax=180.0):
    n, edges = G[name]
    tgt = target_mask(n, edges)
    lit = [sum(1 << idx for idx in range(1 << n) if (idx >> i) & 1) for i in range(n)]
    seen = {m: 0 for m in lit}
    seen[0] = 1          # constant false costs one gate (x AND NOT x), avoid it anyway
    if tgt in seen:
        return 0, len(seen), True
    t0 = time.time()
    for k in range(1, kmax + 1):
        new = {}
        items = list(seen.items())
        for i in range(len(items)):
            a, ca = items[i]
            for j in range(i, len(items)):
                b, cb = items[j]
                if ca + cb + 1 != k and not (ca + cb < k):
                    continue
                for m in (a & b, a | b):
                    if m not in seen and m not in new:
                        new[m] = k
        # masks built here cost k unless an earlier level already holds them
        new = {m: k for m in new}
        seen.update(new)
        if tgt in seen:
            return seen[tgt], len(seen), True
        if len(seen) > cap or time.time() - t0 > tmax:
            return None, len(seen), False
        if not new:
            return None, len(seen), True
    return None, len(seen), True

def tau(n, edges):
    """Brute-force minimum vertex cover."""
    import itertools
    E = [(u, v) for u, v in edges]
    for k in range(n + 1):
        for S in itertools.combinations(range(n), k):
            S = set(S)
            if all(u in S or v in S for u, v in E):
                return k
    return n

def has_4cycle(n, edges):
    """True iff the graph contains a 4-cycle.

    A 4-cycle on distinct a,b,c,d means two disjoint edges {a,b},{c,d} plus the two
    cross edges {a,c},{b,d} (or the other pairing). Checking disjoint edge pairs is
    complete and avoids the canonical-form shortcuts that silently miss relabellings.
    """
    A = set(frozenset(e) for e in edges)
    for a, b in edges:
        for c, d in edges:
            if len({a, b, c, d}) < 4:
                continue
            if frozenset((a, c)) in A and frozenset((b, d)) in A:
                return True
            if frozenset((a, d)) in A and frozenset((b, c)) in A:
                return True
    return False

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "table":
    name = sys.argv[1] if len(sys.argv) > 1 else "c4"
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    c, nseen, done = run(name, kmax)
    print(f"{name}: min_gates={c} masks_seen={nseen} level_search_finished={done}")

def table(names):
    print(f"{'graph':9} {'n':>2} {'|E|':>3} {'tau':>3} {'formula':>7} {'4cyc':>5}")
    for nm in names:
        n, E = G[nm]
        t = tau(n, E)
        print(f"{nm:9} {n:>2} {len(E):>3} {t:>3} {len(E)+t-1:>7} {str(has_4cycle(n,E)):>5}")
