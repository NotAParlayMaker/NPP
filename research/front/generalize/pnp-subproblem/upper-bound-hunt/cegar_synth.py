"""Counterexample-guided SAT exact synthesis for the edge function f_G.

Question asked of the solver: is there a circuit with AT MOST k gates (fan-in-2 AND, OR,
fan-in-1 NOT, every gate counted, inputs free) computing f_G(x) = OR_{uv in E} x_u x_v ?

Encoding (independent of ../exact_edge_fn.py):
  * gates g = n .. n+k-1 in topological order, output = last gate;
  * one-hot first-input selector s1[g,i] and second-input selector s2[g,i], i < g;
    binary gates need s1-index < s2-index, NOT gates have s2 = s1 (s2 ignored);
  * one-hot type tAND/tOR/tNOT;
  * per row r: value v[g,r], helper values in1[g,r], in2[g,r] tied to the selected inputs.
  * Unused gates are allowed, so SAT at k means "some circuit of size <= k exists".
  * Sound pruning: no NOT gate whose input is a NOT gate (such a circuit can be shortened).
  * Optional --monotone: forbid NOT gates.

CEGAR: the truth-table constraints are imposed on a growing subset of rows. If the solver says
UNSAT on a subset, no circuit of size <= k exists (on all rows a fortiori). If SAT, the circuit is
extracted and evaluated on all 2^n rows; mismatching rows are added and the loop repeats. A
returned circuit agrees with f_G on all rows by construction of the loop, and is re-checked by
verify_circuit.py (separate code) before anything is reported.

Usage: python cegar_synth.py GRAPHFILE k [--monotone] [--out circuit.json] [--seed s]
GRAPHFILE: JSON {"name":..., "n":..., "edges":[[u,v],...]}.
Wall-clock limits are imposed from outside (`timeout`).
"""
import itertools, json, random, sys, time
from pysat.solvers import Solver


def f_rows(n, edges):
    return [int(any((r >> u) & 1 and (r >> v) & 1 for u, v in edges)) for r in range(1 << n)]


def maximal_independent_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    out = []
    def bk(R, P, X):  # Bron-Kerbosch on the complement
        if not P and not X:
            out.append(R); return
        for v in list(P):
            nonadj = P - adj[v] - {v}
            bk(R | {v}, {w for w in P if w != v and w not in adj[v]}, {w for w in X if w not in adj[v]})
            P = P - {v}; X = X | {v}
    bk(set(), set(range(n)), set())
    return [sum(1 << v for v in S) for S in out]


class Synth:
    def __init__(self, n, k, monotone=False, solver='cadical153'):
        self.n, self.k, self.mono = n, k, monotone
        self.cnt = 0
        self.S = Solver(name=solver)
        m = n + k
        self.m = m
        nv = self.nv
        self.s1 = {}; self.s2 = {}
        self.tA = {}; self.tO = {}; self.tN = {}
        for g in range(n, m):
            self.tA[g], self.tO[g], self.tN[g] = nv(), nv(), nv()
            A, O, N = self.tA[g], self.tO[g], self.tN[g]
            self.add([A, O, N]); self.add([-A, -O]); self.add([-A, -N]); self.add([-O, -N])
            if monotone:
                self.add([-N])
            for i in range(g):
                self.s1[g, i] = nv(); self.s2[g, i] = nv()
            self.exactly_one([self.s1[g, i] for i in range(g)])
            self.exactly_one([self.s2[g, i] for i in range(g)])
            for i in range(g):
                # NOT: s2 = s1
                self.add([-N, -self.s1[g, i], self.s2[g, i]])
                # binary: s1 index < s2 index  <=> forbid s1=i, s2=j with j<=i
                for j in range(i + 1):
                    self.add([N, -self.s1[g, i], -self.s2[g, j]])
                # no NOT of NOT
                if i >= n:
                    self.add([-N, -self.s1[g, i], -self.tN[i]])
        self.rows = []

    def nv(self):
        self.cnt += 1; return self.cnt

    def add(self, c):
        self.S.add_clause(c)

    def exactly_one(self, lits):
        self.add(lits)
        if len(lits) <= 6:
            for a, b in itertools.combinations(lits, 2):
                self.add([-a, -b])
        else:  # sequential counter (at most one)
            prev = None
            for idx, l in enumerate(lits):
                if idx == len(lits) - 1:
                    if prev is not None: self.add([-prev, -l])
                    break
                s = self.nv()
                self.add([-l, s])
                if prev is not None:
                    self.add([-prev, s]); self.add([-prev, -l])
                prev = s

    def add_row(self, r, val):
        n, m = self.n, self.m
        v = {}
        for g in range(n, m):
            v[g] = self.nv()
        def lit(i):
            return bool((r >> i) & 1) if i < n else v[i]
        for g in range(n, m):
            a, b = self.nv(), self.nv()
            for sel, x in ((self.s1, a), (self.s2, b)):
                for i in range(g):
                    s = sel[g, i]; L = lit(i)
                    if L is True: self.add([-s, x])
                    elif L is False: self.add([-s, -x])
                    else: self.add([-s, -L, x]); self.add([-s, L, -x])
            o = v[g]; A, O, N = self.tA[g], self.tO[g], self.tN[g]
            self.add([-A, -a, -b, o]); self.add([-A, a, -o]); self.add([-A, b, -o])
            self.add([-O, a, b, -o]); self.add([-O, -a, o]); self.add([-O, -b, o])
            if not self.mono:
                self.add([-N, a, o]); self.add([-N, -a, -o])
        out = v[m - 1]
        self.add([out] if val else [-out])
        self.rows.append(r)

    def extract(self):
        M = set(l for l in self.S.get_model() if l > 0)
        gates = []
        for g in range(self.n, self.m):
            t = 'AND' if self.tA[g] in M else 'OR' if self.tO[g] in M else 'NOT'
            i = next(i for i in range(g) if self.s1[g, i] in M)
            j = next(i for i in range(g) if self.s2[g, i] in M)
            gates.append([t, i] if t == 'NOT' else [t, i, j])
        return gates


def evaluate(n, gates, r):
    val = [(r >> i) & 1 for i in range(n)]
    for gt in gates:
        if gt[0] == 'NOT': val.append(1 - val[gt[1]])
        elif gt[0] == 'AND': val.append(val[gt[1]] & val[gt[2]])
        else: val.append(val[gt[1]] | val[gt[2]])
    return val[-1]


def prune(n, gates):
    """Drop gates not reachable from the output; renumber."""
    m = n + len(gates)
    need = {m - 1}; stack = [m - 1]
    while stack:
        g = stack.pop()
        if g < n: continue
        for i in gates[g - n][1:]:
            if i not in need: need.add(i); stack.append(i)
    keep = [g for g in range(n, m) if g in need]
    ren = {i: i for i in range(n)}
    out = []
    for g in keep:
        ren[g] = n + len(out)
        gt = gates[g - n]
        out.append([gt[0]] + [ren[i] for i in gt[1:]])
    return out


def run(n, edges, k, monotone=False, seed=0, log=print, solver='cadical153'):
    rng = random.Random(seed)
    T = f_rows(n, edges)
    t0 = time.time()
    syn = Synth(n, k, monotone, solver)
    init = set()
    for w in range(2):
        for S in itertools.combinations(range(n), w): init.add(sum(1 << i for i in S))
    for S in itertools.combinations(range(n), 2): init.add(sum(1 << i for i in S))
    for r in maximal_independent_sets(n, edges): init.add(r)
    for _ in range(4 * n): init.add(rng.randrange(1 << n))
    for r in sorted(init): syn.add_row(r, T[r])
    it = 0
    while True:
        it += 1
        ok = syn.S.solve()
        if not ok:
            log(f"UNSAT on {len(syn.rows)} rows after {it} iterations, {time.time()-t0:.1f}s")
            return None
        gates = syn.extract()
        bad = [r for r in range(1 << n) if evaluate(n, gates, r) != T[r]]
        log(f"  iter {it}: rows={len(syn.rows)} candidate wrong on {len(bad)} rows ({time.time()-t0:.1f}s)")
        if not bad:
            return prune(n, gates)
        rng.shuffle(bad)
        # add a few, preferring low/high weight variety
        for r in bad[:max(4, min(32, len(bad) // 50))]:
            syn.add_row(r, T[r])


if __name__ == '__main__':
    G = json.load(open(sys.argv[1])); k = int(sys.argv[2])
    mono = '--monotone' in sys.argv
    out = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 0
    solver = sys.argv[sys.argv.index('--solver') + 1] if '--solver' in sys.argv else 'cadical153'
    n, E = G['n'], [tuple(e) for e in G['edges']]
    print(f"{G['name']}: n={n} |E|={len(E)} k={k} monotone={mono}", flush=True)
    t = time.time()
    res = run(n, E, k, mono, seed, log=lambda s: print(s, flush=True), solver=solver)
    if res is None:
        print(f"RESULT UNSAT k={k} time={time.time()-t:.1f}s", flush=True)
    else:
        print(f"RESULT SAT k={k} size={len(res)} time={time.time()-t:.1f}s", flush=True)
        print(json.dumps(res))
        if out:
            json.dump({'graph': G, 'gates': res}, open(out, 'w'))
