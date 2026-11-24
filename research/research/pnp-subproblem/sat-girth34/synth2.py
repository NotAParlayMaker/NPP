"""Exact synthesis (SAT) for the edge function f_G, basis: fan-in-2 AND, OR; NOT; every gate counted.

Second encoding (compared with ../exact_edge_fn.py):
  * per gate: one-hot first-input selector s1[g,i], at-most-one second-input selector s2[g,j]
    (i < j), and per-row "input value" variables A[g,r], B[g,r]  -> O(k*(n+k)*2^n) clauses
    instead of O(k*(n+k)^2*2^n);
  * symmetry breaking, each valid for EVERY minimum-size circuit of exactly k gates after a
    re-ordering (argument in README.md):
      - every non-output gate is used; every input that f_G depends on is used;
      - no gate computes a constant, an input variable, or the same function as another gate;
      - gate keys key(g) = (largest input index, smaller input index or -1 for NOT, op) are
        non-decreasing along the gate order (greedy topological order);
  * all 2^n rows of the truth table are encoded (no row sampling), so UNSAT is a proof that no
    circuit with exactly k gates exists.
Run as a script:  python3 synth2.py <graph6> <k>   ->  prints SAT + circuit, or UNSAT.
"""
import itertools, sys, time
import networkx as nx
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


def target(G):
    nodes = sorted(G.nodes); idx = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    return [int(any(((r >> idx[u]) & 1) and ((r >> idx[v]) & 1) for u, v in G.edges)) for r in range(1 << n)]


def encode(n, T, k, relevant=None):
    R = 1 << n
    m = n + k
    top = [0]
    def nv():
        top[0] += 1; return top[0]
    cl = []
    X = {}       # X[g,r] value of gate g in row r
    for g in range(n, m):
        for r in range(R): X[g, r] = nv()
    def val(i, r):
        return bool((r >> i) & 1) if i < n else X[i, r]
    s1, s2, isnot, isand = {}, {}, {}, {}
    A, B = {}, {}
    for g in range(n, m):
        isnot[g] = nv(); isand[g] = nv()       # binary gate: isand true -> AND, false -> OR
        cl.append([-isnot[g], -isand[g]])     # canonical: NOT gates have isand false
        for i in range(g): s1[g, i] = nv()
        for j in range(1, g): s2[g, j] = nv()
        lits1 = [s1[g, i] for i in range(g)]
        lits2 = [s2[g, j] for j in range(1, g)]
        enc = CardEnc.equals(lits=lits1, bound=1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], enc.nv); cl += enc.clauses
        enc = CardEnc.atmost(lits=lits2, bound=1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], enc.nv); cl += enc.clauses
        # binary <-> some s2
        cl.append([isnot[g]] + lits2)
        for l in lits2: cl.append([-isnot[g], -l])
        # i < j
        for i in range(g):
            for j in range(1, i + 1): cl.append([-s1[g, i], -s2[g, j]])
        for r in range(R):
            A[g, r] = nv(); B[g, r] = nv()
            for i in range(g):
                v = val(i, r)
                if isinstance(v, bool): cl.append([-s1[g, i], A[g, r] if v else -A[g, r]])
                else: cl += [[-s1[g, i], -v, A[g, r]], [-s1[g, i], v, -A[g, r]]]
            for j in range(1, g):
                v = val(j, r)
                if isinstance(v, bool): cl.append([-s2[g, j], B[g, r] if v else -B[g, r]])
                else: cl += [[-s2[g, j], -v, B[g, r]], [-s2[g, j], v, -B[g, r]]]
            a, b, o = A[g, r], B[g, r], X[g, r]
            # NOT
            cl += [[-isnot[g], a, o], [-isnot[g], -a, -o]]
            # AND
            cl += [[isnot[g], -isand[g], -a, -b, o], [isnot[g], -isand[g], a, -o], [isnot[g], -isand[g], b, -o]]
            # OR
            cl += [[isnot[g], isand[g], a, b, -o], [isnot[g], isand[g], -a, o], [isnot[g], isand[g], -b, o]]
    # output
    for r in range(R): cl.append([X[m - 1, r] if T[r] else -X[m - 1, r]])
    # every non-output gate used
    for i in range(n, m - 1):
        cl.append([s1[g, i] for g in range(i + 1, m)] + [s2[g, i] for g in range(i + 1, m)])
    # every relevant input used
    if relevant is None: relevant = range(n)
    for i in relevant:
        cl.append([s1[g, i] for g in range(n, m)] + [s2[g, i] for g in range(max(n, i + 1), m) if (g, i) in s2])
    # distinct functions: not constant, not an input, pairwise distinct (gate g < output)
    for g in range(n, m):
        cl.append([X[g, r] for r in range(R)])
        cl.append([-X[g, r] for r in range(R)])
        for i in range(n):
            cl.append([(-X[g, r] if (r >> i) & 1 else X[g, r]) for r in range(R)])
    for g, h in itertools.combinations(range(n, m), 2):
        ds = []
        for r in range(R):
            d = nv(); ds.append(d)
            cl += [[-d, X[g, r], X[h, r]], [-d, -X[g, r], -X[h, r]]]
        cl.append(ds)
    # key ordering: key(g) = (J, I, op) with J = max input, I = min input (-1 for NOT),
    # op: NOT < OR < AND.  key(g) <= key(g+1).
    J, I = {}, {}
    for g in range(n, m):
        for j in range(g):
            J[g, j] = nv()
            # J[g,j] <-> (isnot & s1[g,j]) | s2[g,j]
            t = [s2[g, j]] if (g, j) in s2 else []
            # J -> isnot&s1  or s2
            cl.append([-J[g, j], s1[g, j]] + t)
            cl.append([-J[g, j], isnot[g]] + t)
            cl.append([J[g, j], -isnot[g], -s1[g, j]])
            if t: cl.append([J[g, j], -t[0]])
    for g in range(n, m - 1):
        h = g + 1
        for j in range(g):
            for j2 in range(j):
                cl.append([-J[g, j], -J[h, j2]])
            # tie on J
            # g binary with min input i ; h NOT  -> forbidden
            cl.append([-J[g, j], -J[h, j], isnot[g], -isnot[h]])
            # both binary, I(h) < I(g) forbidden
            for i in range(j):
                for i2 in range(i):
                    cl.append([-J[g, j], -J[h, j], isnot[g], isnot[h], -s1[g, i], -s1[h, i2]])
                # full tie: op(g) <= op(h): forbid g AND, h OR
                cl.append([-J[g, j], -J[h, j], isnot[g], isnot[h], -s1[g, i], -s1[h, i], -isand[g], isand[h]])
    import os
    if os.environ.get('MONO'):
        for g in range(n, m): cl.append([-isnot[g]])
    info = dict(s1=s1, s2=s2, isnot=isnot, isand=isand, n=n, m=m)
    return cl, info


def decode(model, info):
    ms = set(l for l in model if l > 0)
    n, m = info['n'], info['m']
    circ = []
    for g in range(n, m):
        i = [i for i in range(g) if info['s1'][g, i] in ms][0]
        if info['isnot'][g] in ms:
            circ.append(('NOT', i))
        else:
            j = [j for j in range(1, g) if info['s2'][g, j] in ms][0]
            circ.append(('AND' if info['isand'][g] in ms else 'OR', i, j))
    return circ


def evaluate(circ, n, r):
    """Independent brute-force evaluation of a circuit (list of gates, node ids: inputs 0..n-1,
    gate t has id n+t) on input row r. Returns the value of the last gate."""
    vals = [(r >> i) & 1 for i in range(n)]
    for gate in circ:
        if gate[0] == 'NOT': vals.append(1 - vals[gate[1]])
        elif gate[0] == 'AND': vals.append(vals[gate[1]] & vals[gate[2]])
        elif gate[0] == 'OR': vals.append(vals[gate[1]] | vals[gate[2]])
        else: raise ValueError(gate)
    return vals[-1]


def solve(n, T, k, solver='cadical153'):
    cl, info = encode(n, T, k)
    with Solver(name=solver, bootstrap_with=cl) as S:
        ok = S.solve()
        model = S.get_model() if ok else None
    if ok:
        return True, decode(model, info), len(cl)
    return False, None, len(cl)


if __name__ == '__main__':
    G = nx.from_graph6_bytes(sys.argv[1].encode())
    k = int(sys.argv[2])
    solver = sys.argv[3] if len(sys.argv) > 3 else 'cadical153'
    n = G.number_of_nodes(); T = target(G)
    t = time.time()
    ok, circ, ncl = solve(n, T, k, solver)
    dt = time.time() - t
    if ok:
        good = all(evaluate(circ, n, r) == T[r] for r in range(1 << n))
        print(f"SAT {dt:.2f} clauses={ncl} verified={good} circuit={circ}")
    else:
        print(f"UNSAT {dt:.2f} clauses={ncl}")
