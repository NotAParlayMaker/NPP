"""Contingency table for note 2: has_4cycle x (unknown/tight/below) on all graphs with n vertices.

The claim note 2 makes is that 4-cycle-free graphs are exactly the ones where the
formula |E|+tau-1 equals the exact minimum. That claim needs the *joint* table, not
the two marginals: full6.py prints `tight` over all graphs and a separate
`mismatch_free`, so the count of 4-cycle-free graphs that are tight is not visible.
This program prints it, so every number in the note comes from one run.

Usage: python3 programs/note2_table.py [closure.txt] [n]
"""
import itertools
import os
import sys

from exact_ref import target_mask, tau, has_4cycle


def main() -> None:
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser("~/pnp_loop/data/closure_n6.txt")
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    cost = {}
    for line in open(src):
        parts = line.split()
        if len(parts) == 2:
            cost[int(parts[0], 16)] = int(parts[1])
    pairs = list(itertools.combinations(range(n), 2))

    # counts[four][kind] for kind in unknown, tight, below, above
    counts = {True: dict(unknown=0, tight=0, below=0, above=0),
              False: dict(unknown=0, tight=0, below=0, above=0)}
    for bits in range(1, 1 << len(pairs)):
        edges = [e for i, e in enumerate(pairs) if (bits >> i) & 1]
        c = cost.get(target_mask(n, edges))
        f = len(edges) + tau(n, edges) - 1
        row = counts[has_4cycle(n, edges)]
        if c is None:
            row["unknown"] += 1
        elif c == f:
            row["tight"] += 1
        elif c < f:
            row["below"] += 1
        else:
            row["above"] += 1

    print(f"n={n} masks={len(cost)}")
    print(f"{'has_4cycle':10} {'unknown':>8} {'tight':>7} {'below':>7} {'above':>6} {'graphs':>7}")
    for four in (False, True):
        r = counts[four]
        print(f"{str(four):10} {r['unknown']:8d} {r['tight']:7d} {r['below']:7d} {r['above']:6d} {sum(r.values()):7d}")
    free, cyc = counts[False], counts[True]
    print(f"exactly-tight without a 4-cycle: {free['tight']}; with a 4-cycle: {cyc['tight']}")
    print(f"below the formula without a 4-cycle: {free['below']}; with a 4-cycle: {cyc['below']}")
    print("NOTE-2 CLAIM HOLDS" if free["below"] == 0 else "NOTE-2 CLAIM FAILS")


if __name__ == "__main__":
    main()
