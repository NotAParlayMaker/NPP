"""The formula's construction, built and checked: `|E| + tau - 1` gates, exactly.

For a minimum cover C and each c in C: gate A_c = x_c AND (OR of x_b over the edges assigned to
c), then OR the A_c together. Edges are assigned to the smaller-indexed cover endpoint so the
assignment is a partition: sum of star degrees = |E|. Gate count
  sum_c (d_c - 1)  ORs inside stars
+ |C|              ANDs
+ |C| - 1          ORs joining stars
= |E| - tau + tau + tau - 1 = |E| + tau - 1.
Checked on every input for every graph on n <= 6 vertices.
"""
import itertools
from star_verify import edge_fn, eval_circuit, tau

def build_formula(E, C, n):
    C = sorted(C)
    assign = {c: [] for c in C}
    for u, v in E:
        cu = u if u in assign else None
        cv = v if v in assign else None
        if cu is None:
            owner, other = cv, u
        elif cv is None:
            owner, other = cu, v
        else:
            owner, other = min(cu, cv), (v if min(cu, cv) == cu else u)
        assign[owner].append(other)
    gates = []
    def new(op, ins):
        gates.append((op, ins))
        return n + len(gates) - 1
    stars = []
    for c in C:
        bs = assign[c]
        if not bs:
            continue
        w = bs[0]                    # literal wire
        for b in bs[1:]:
            w = new("or", [w, b])
        stars.append(new("and", [c, w]))
    w = stars[0]
    for t in stars[1:]:
        w = new("or", [w, t])
    return gates, w

def check(n):
    pairs = list(itertools.combinations(range(n), 2))
    bad = size_bad = 0
    for bits in range(1, 1 << len(pairs)):
        E = [e for i, e in enumerate(pairs) if (bits >> i) & 1]
        C = tau(n, E)
        gates, out = build_formula(E, C, n)
        f = edge_fn(E)
        want = len(E) + len(C) - 1
        if len(gates) != want:
            size_bad += 1
        for x in itertools.product([False, True], repeat=n):
            if eval_circuit(gates, out, n, x) != f(x):
                bad += 1
                break
    return bad, size_bad

if __name__ == "__main__":
    for n in (4, 5, 6):
        b, s = check(n)
        print(f"n={n}: wrong={b} size_mismatch={s}")
