"""Exact minimum AND/OR fan-in-two circuit size for EVERY graph on 5 vertices.

The mask closure with cost(mask) = fewest gates depends only on n, not on the graph, so one
levelled closure answers all 1024 targets. cost lookup is exact (see exact_ref.py).
"""
import itertools, json, os
from exact_ref import G, target_mask, tau, has_4cycle

def closure(n, kmax, tmax=600.0):
    import time
    t0 = time.time()
    lit = [sum(1 << idx for idx in range(1 << n) if (idx >> i) & 1) for i in range(n)]
    cost = {m: 0 for m in lit}
    cost[0] = 1
    for k in range(1, kmax + 1):
        new = {}
        items = list(cost.items())
        for i in range(len(items)):
            a, ca = items[i]
            for j in range(i, len(items)):
                b, cb = items[j]
                if ca + cb + 1 != k:
                    continue
                for m in (a & b, a | b):
                    if m not in cost:
                        new.setdefault(m, k)
        cost.update(new)
        if not new:
            break
        if time.time() - t0 > tmax:
            return cost, False
    return cost, True

if __name__ == "__main__":
    n = 5
    cost, done = closure(n, 9)
    print(f"closure n={n}: masks={len(cost)} finished={done} maxcost={max(cost.values())}")
    pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
    rows = []
    for bits in range(1, 1 << len(pairs)):
        E = [e for i, e in enumerate(pairs) if (bits >> i) & 1]
        t = target_mask(n, E)
        c = cost.get(t)
        f = len(E) + tau(n, E) - 1
        rows.append({"edges": len(E), "tau": tau(n, E), "formula": f, "exact": c,
                     "fourcycle": has_4cycle(n, E)})
    unknown = sum(1 for r in rows if r["exact"] is None)
    tight = sum(1 for r in rows if r["exact"] == r["formula"])
    below = sum(1 for r in rows if r["exact"] is not None and r["exact"] < r["formula"])
    above = sum(1 for r in rows if r["exact"] is not None and r["exact"] > r["formula"])
    print(f"graphs={len(rows)} exact_known={len(rows)-unknown} formula_tight={tight} "
          f"formula_above_exact={below} formula_below_exact={above}")
    fails = [r for r in rows if r["exact"] is not None and r["exact"] != r["formula"]]
    print("mismatches with a 4-cycle:", sum(1 for r in fails if r["fourcycle"]),
          "without:", sum(1 for r in fails if not r["fourcycle"]))
    json.dump(rows, open(os.path.expanduser("~/pnp_loop/data/all5_exact.json"), "w"))
