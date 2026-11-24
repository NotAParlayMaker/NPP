# Note 2: four-cycle-freeness is what makes `|E| + tau - 1` exact

Status: conjecture with exhaustive evidence up to 6 vertices and a verified upper bound everywhere.
Supersedes nothing; note 1 proves individual rows by gate elimination. This note isolates the
hypothesis those rows have in common.

## Statement

Let `G = (V, E)` be a simple graph, `tau(G)` its vertex cover number, and `f_G : {0,1}^V -> {0,1}`
the edge function `OR over {u,v} in E of (x_u AND x_v)`. If `G` contains no 4-cycle, then the
minimum number of fan-in-two AND/OR gates computing `f_G` is exactly `|E| + tau(G) - 1`.

## Upper bound (proved, and mechanically checked)

Construction: take a minimum cover `C`; assign each edge to the smaller-indexed endpoint in `C`;
for each `c in C` build `x_c AND (OR of x_b over its assigned neighbours)`; OR the `|C|` results.
Edges assigned form a partition, so the star degrees sum to `|E|` and the gate count is
`sum_c (d_c - 1) + |C| + (|C| - 1) = |E| + tau - 1`.

Verified by `programs/formula_build.py`, evaluating every input of every circuit:

| n | graphs checked | computing the wrong function | size != formula |
|---|---|---|---|
| 4 | 63 (all nonempty) | 0 | 0 |
| 5 | 1023 (all nonempty) | 0 | 0 |
| 6 | 32767 (all nonempty) | 0 | 0 |
| 7 | 27895 (all with 1..5 edges) plus C7, pendant-6, heel, K(1,6), K(3,3)+pendant | 0 | 0 |

The same circuits are Lean theorems: `lean/PEqualNP/Outside/{C4,C5,C6,Pendant6}_WIP.lean`, each
`decide`-checked on all inputs with no `sorry`.

## Lower bound (evidence)

Exact sizes come from a sound levelled closure over masks (`notes/data/note-2/exact_ref.py`,
`notes/data/note-2/closure2.c`): a wire is a bitmask over the inputs, literals start the closure, AND and OR
are bitwise, and `cost(mask)` is the fewest gates, so presence at level k is a k-gate circuit and
absence from all levels `<= K` is a proof of `> K`. No restriction is placed on interior wires
(an earlier tool restricted them to sub-masks of the target and was wrong -- see the C4 case).

Results, from the closure run to cost 10 (1,856,991 masks):

- n = 5: all 1023 graphs decided. The formula is exact exactly on the 4-cycle-free ones
  (547 tight, 475 strictly larger, 0 smaller).
- n = 6: 31263 of 32767 graphs decided. **All 7983 4-cycle-free graphs are decided, and all 7983
  are tight.** The formula never understates the size at either n.
- The converse fails, and the two sizes differ here: on 5 vertices every graph containing a 4-cycle
  is strictly smaller than the formula (0 tight of 475), but on 6 vertices **360 graphs containing a
  4-cycle are still tight**. So 4-cycle-freeness is sufficient for tightness, not necessary, and it
  cannot be turned into an "if and only if" statement from 5 vertices alone.
- The joint table, from `notes/data/note-2/note2_table.py` (which counts what `full6.py` does not,
  the tight graphs that do contain a 4-cycle):

      has_4cycle  unknown   tight   below  above  graphs
      False             0    7983       0      0    7983
      True           1504     360   22920      0   24784

  So every 4-cycle-free graph on 6 vertices is decided and tight, and 360 of the 24784 graphs with
  a 4-cycle are also tight, 1504 undecided.

So the conjecture is verified exhaustively for *every* 4-cycle-free graph on at most 6 vertices.
What is *not* claimed: that a 4-cycle forces a saving.

## Why 4-cycles

A 4-cycle `a-b-c-d-a` lets one gate cover four edges at once: `(x_a OR x_c) AND (x_b OR x_d)` is
the edge function of that 4-cycle with three gates, where the formula would charge `4 + 2 - 1 = 5`.
So 4-cycle-freeness is not decoration: it forbids the only local sharing pattern that beats the
counting, and with it every pair of edges meets in at most one vertex.

## Open

1. pendant-6 (6-cycle plus a leaf): value 9, upper bound in Lean, lower bound needs the n = 7
   closure at k = 9, which is at the edge of the memory this machine has.
2. Everything with 7 or more vertices: the smallest is pendant-6 itself, and 7-vertex graphs with
   six or more edges are beyond the closure on this machine.
3. The general gate-elimination proof.

## Reproduction

All programs and their expected output are in `notes/data/note-2/` (see its `README.md`).

    python3 notes/data/note-2/formula_build.py        # upper bound, n <= 6, all graphs
    python3 notes/data/note-2/verify_formula_n7.py    # upper bound, n = 7 classes
    python3 notes/data/note-2/exact_ref.py c5 7       # exact C5, 7 gates
    python3 notes/data/note-2/all5.py                 # exhaustive n = 5 table
    gcc -O2 -o closure2 notes/data/note-2/closure2.c && ./closure2 6 10 > closure_n6_k10.txt
    python3 notes/data/note-2/note2_table.py closure_n6_k10.txt 6   # the joint table
    python3 notes/data/note-2/full6.py closure_n6.txt # n = 6 marginals
