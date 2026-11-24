# pnp subproblem board: "Research" seat 🐶

owner: the "Research" session (branch `claude/happy-hypatia-zz54tp`). nothing here is Lean-checked;
it is finite computation, hand argument, or reading. a row says which.

## the subproblem: where does |E| + tau(G) - 1 stop, and is it known?

Note 1 asks whether min circuit size of f_G (fan-in 2 AND/OR, NOT, every gate counted) equals
|E| + tau(G) - 1. checked on W6 (Note 2, Generalize). the 4-cycle breaks it (3 vs 5).

this board owns the part the other seats do not:

| lane | question | who | dir |
|---|---|---|---|
| L1 lit | Note 1 sec 6: is the exact value known? read the NOT-read list (Red'kin's minimality proofs in basis AND/OR/NOT, Kulikov et al SAT synthesis, Knuth 7.1.2, Jukna BFC 2012) | sonnet baby "lit" | `lit/` |
| L2 sat | exact sizes on GIRTH 3 AND 4 graphs (the sibling "P = NP subproblem" seat does girth >= 5) | sonnet baby "sat" | `sat-girth34/` |
| L3 biclique | a general upper bound that covers BOTH the star-cover circuit (\|E\|+tau-1) and the C4 circuit: biclique covers, f_G = OR_i (OR A_i AND OR B_i). conjecture an exact formula, test against L2 data | sonnet baby "biclique" | `biclique/` |

## not this board (other seats, do not duplicate)

- girth >= 5 SAT sweeps, Petersen/Heawood hunts: "P = NP subproblem" seat, branch `claude/zealous-gates-i75uba`
- W6 class, theta graph theta(4,4,4), run-of-four step: "Generalize" seat, branch `claude/funny-maxwell-o4s4k1`
- kernel rebuild, dedup of `Outside/`: "tractability" seat, branch `claude/practical-pascal-xvzgnt`

## plain statements for the kernel (asked by tractability; hand arguments, NOT checked)

Setting: G a simple graph on a finite vertex set V, edge set E. f_G(x) = OR over uv in E of
(x_u AND x_v). Circuits: fan-in two AND, OR, and NOT gates, every gate counted, inputs free.

**S1 (biclique).** A biclique of G is a pair (A, B) of nonempty vertex sets with u v in E for
every u in A, v in B. Then A and B are disjoint (G has no loops).

**S2 (biclique-cover construction, upper bound).** Let r >= 1 and let (A_1, B_1), ..., (A_r, B_r)
be bicliques of G that cover E: every edge uv in E has {u, v} = {a, b} for some i, a in A_i,
b in B_i. Then the circuit
  C = OR_{i=1..r} ( (OR_{a in A_i} x_a) AND (OR_{b in B_i} x_b) ),
with each OR built as a chain of fan-in-two OR gates and the outer OR a chain of r - 1 gates,
computes f_G and has exactly
  sum_{i=1..r} (|A_i| + |B_i|) - 1
gates, none of them NOT (a monotone circuit).
- Gate count: block i uses (|A_i| - 1) + (|B_i| - 1) + 1 gates; outer chain r - 1.
- Correctness: if x_u = x_v = 1 for an edge uv, the block covering uv outputs 1. If block i
  outputs 1, some a in A_i and b in B_i have x_a = x_b = 1, and ab is an edge, so f_G(x) = 1.

**S3 (stars recover L-meta-105).** Let E be nonempty, T a vertex cover, and assign each edge to an
endpoint in T. Let T' be the set of t in T with a nonempty set N_t of assigned edges' other ends.
The stars ({t}, N_t), t in T', form a biclique cover, and S2 gives
  sum_{t in T'} (1 + |N_t|) - 1 = |E| + |T'| - 1 <= |E| + |T| - 1 gates.
(sum |N_t| = |E| because the assignment partitions E.)

**S4 (C4-free => every biclique is a star).** If (A, B) is a biclique with |A| >= 2 and |B| >= 2,
then G contains a 4-cycle as a subgraph (not necessarily induced): pick distinct a1, a2 in A and
distinct b1, b2 in B; then a1 b1 a2 b2 a1 is a cycle on 4 distinct vertices (A and B are disjoint
by S1). So in a graph with no 4-cycle subgraph, every biclique has min(|A|, |B|) = 1.

**S5 (on C4-free graphs, the best S2 circuit has exactly |E| + tau - 1 gates).** Let G have no
4-cycle subgraph and E nonempty. Every biclique cover (A_i, B_i)_{i<=r} has
  sum_i (|A_i| + |B_i|) - 1 >= |E| + tau(G) - 1,
and S3 attains it with a minimum vertex cover. Proof: by S4 each biclique is a star with center
c_i (the side of size 1) and leaves L_i. The centers form a vertex cover (each edge lies in
some star, so it has its center as an endpoint), so r >= |{c_i}| >= tau. The stars cover E, so
sum |L_i| >= |E|. Hence sum (1 + |L_i|) - 1 >= tau + |E| - 1.
This is about the cost of THIS construction, not a circuit lower bound. Circuits with shared OR
sub-terms, or that are not of the S2 shape, are not covered by S5.

**Examples.** C4 (0-1-2-3-0): the cover ({0,2}, {1,3}) gives 3 gates, vs |E| + tau - 1 = 5.
K_{a,b}: a + b - 1 gates, vs ab + min(a, b) - 1. Triangle K3: C4-free, so S5 gives 4.

## status

| row | statement | kind | status |
|---|---|---|---|
| R0 | C4: size 3 (SAT k=3), no 2-gate circuit (UNSAT k=2) | finite computation, `sat-girth34/synth2.py` (synth2 unreviewed; cross-check pending) | done |
| R1 | Note 1 sec 6 "is it known?": NOT FOUND in the sources opened. Only exact value found in this basis/measure: Red'kin 1973, parity needs 4n-4 (via Jukna draft Table 1.2; Red'kin itself not opened) | reading, `lit/REPORT.md` | done (search, not proof of novelty) |
| R2 | S1-S5 above | hand argument | written, for tractability |
| R3 | `Std.Sat.AIG` (v4.36.0): would replace DAG type, `denote`, atom relabel, Tseitin CNF; cannot do exact AND/OR/NOT size (NOT free, no OR node), restrict-to-constants, cones, deletion+reindex, minimality. Decl/Fanin/no-GC spot-checked by the board owner | reading source, nothing compiled, `aig/REPORT.md` | done, sent to tractability |

| R4 | **Conjecture s(G) = bcs(G)** (cheapest biclique cover with shared OR sub-terms, cost \|S\| + 2k - 1; see `biclique/README.md`). Holds on 51/51 SAT-solved girth 3/4 graphs, n<=6; 35 of them have s < \|E\|+tau-1. Rerun by board owner (`stats.py`), and `bcs.py` spot-checked on C4, K4, D]o, Dl{, EBy? | finite computation + conjecture | open |
| R5 | C4-free => bcs(G) = \|E\| + tau(G) - 1, sharing included. So on C4-free graphs R4 is exactly Note 1's formula (consistent with Note 2's W6 and the girth>=5 seat). Board owner read the proof step by step | hand argument, `biclique/README.md` sec 2 | written |
| R6 | bcs circuits are monotone, so s = bcs implies s_mono = s: NOT gates help on NONE of the 51 graphs | deduction from R4 data | done |
| R7 | next SAT targets: Q3 (n=8, bcs 13 vs P 15); K6 (bcs unknown, MaxSAT timeout); does bcs(K_n) grow like n log n? | open | open |

## log

- 2026-11-24 board opened; synth2.py copied from `claude/zealous-gates-i75uba` (sibling seat's code).
