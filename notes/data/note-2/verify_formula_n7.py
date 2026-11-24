"""Verify the formula's construction on graphs with 7 vertices, exhaustively over a designed class.

The full 2^21 graph space is too large to check input-by-input in Python for every graph, so this
checks (a) every graph on 7 vertices with at most 5 edges -- all 26,637 of them -- and (b) a fixed
list of named 7-vertex graphs. Each circuit is evaluated on all 128 inputs and its size compared
with |E| + tau - 1.
"""
import itertools, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from formula_build import build_formula
from star_verify import edge_fn, eval_circuit, tau

def check(E, n):
    C = tau(n, E)
    gates, out = build_formula(E, C, n)
    f = edge_fn(E)
    ok = all(eval_circuit(gates, out, n, x) == f(x)
             for x in itertools.product([False, True], repeat=n))
    return ok, len(gates), len(E) + len(C) - 1

if __name__ == "__main__":
    n = 7
    pairs = list(itertools.combinations(range(n), 2))
    checked = bad = size_bad = 0
    for m in range(1, 6):
        for combo in itertools.combinations(pairs, m):
            ok, size, want = check(list(combo), n)
            checked += 1
            if not ok:
                bad += 1
            if size != want:
                size_bad += 1
    named = {
        "c7": [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,0)],
        "pendant6": [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6)],
        "heel7": [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6),(6,1)],
        "star7": [(0,i) for i in range(1,7)],
        "K33plus": [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(6,0)],
    }
    print(f"7-vertex graphs with <=5 edges: checked={checked} wrong={bad} size_mismatch={size_bad}")
    for name, E in named.items():
        ok, size, want = check(E, n)
        print(f"  {name:9} |E|={len(E):2} gates={size:2} formula={want:2} correct={ok}")
