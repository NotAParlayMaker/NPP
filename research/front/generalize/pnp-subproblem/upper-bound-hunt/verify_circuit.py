"""Independent brute-force checker for a circuit claimed to compute f_G.

Reads circuit JSON {"graph": {"n":..,"edges":[..]}, "gates": [["AND",i,j] | ["OR",i,j] | ["NOT",i], ...]}
(inputs are wires 0..n-1, gate t is wire n+t, output is the last gate). Shares no code with
the synthesizer. Prints gate count and whether the circuit equals f_G on all 2^n inputs.
"""
import json, sys
from itertools import product


def check(path):
    d = json.load(open(path))
    n = d['graph']['n']; E = [tuple(e) for e in d['graph']['edges']]; gates = d['gates']
    for t, g in enumerate(gates):
        assert g[0] in ('AND', 'OR', 'NOT'), g
        assert len(g) == (2 if g[0] == 'NOT' else 3), g
        assert all(0 <= w < n + t for w in g[1:]), ('not topological', t, g)
    for bits in product((0, 1), repeat=n):
        x = list(bits)
        w = x[:]
        for g in gates:
            if g[0] == 'NOT': w.append(not w[g[1]])
            elif g[0] == 'AND': w.append(w[g[1]] and w[g[2]])
            else: w.append(w[g[1]] or w[g[2]])
        want = any(x[u] and x[v] for u, v in E)
        if bool(w[-1]) != want:
            return len(gates), False, bits
    return len(gates), True, None


if __name__ == '__main__':
    for p in sys.argv[1:]:
        size, ok, bad = check(p)
        print(f"{p}: gates={size} correct_on_all_inputs={ok}" + ("" if ok else f" first_mismatch={bad}"))
