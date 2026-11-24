# L3 biclique lane: shared-biclique-cover circuits for f_G

Everything here is hand argument or finite computation (python, pysat RC2). NOTHING is Lean-checked.
Files: `bc.py` (no-sharing exact, MaxSAT), `bcs.py` (sharing exact, MaxSAT), `sweep*.py`, `cmp2.py`, `stats.py`,
raw outputs `sweep.out` (n<=7: g6 n m girth tau P star_cost bc cover), `sweep2.out`, `sweep3_6.out`, `sweep3_7.out` (g6 bcs [secs] or TIMEOUT).

Notation: f_G = OR_{uv in E} x_u x_v; P(G) = |E| + tau(G) - 1 (tau = vertex cover number); s(G) = min circuit size (AND/OR/NOT, every gate counted, inputs free).

## 1. Definitions and upper bounds

A *biclique* is (A,B), A,B nonempty disjoint vertex sets with every pair a in A, b in B an edge of G
(so it is a K_{|A|,|B|} subgraph, not necessarily induced-complete inside A or B). A *biclique cover* is a family
(A_i,B_i), i=1..k covering E. Then f_G = OR_i ((OR A_i) AND (OR B_i)): each product term is a subfunction of f_G
because all its edges are in G, and every edge appears in some term.

**bc(G), no sharing.** Each OR is built separately as a tree. Cost = sum_i (|A_i|+|B_i|-1) + (k-1)
(ORs of sides: |A_i|-1 and |B_i|-1; one AND per biclique; k-1 ORs to join). bc(G) = min over covers.

**bcs(G), sharing OR-subterms.** Choose a set S of "OR-gates" (vertex sets of size >=2); each U in S must be the union
of two members of S U {singletons} (proper subsets; overlap allowed, OR is idempotent). Every side A_i, B_i of size >=2
must be in S. Cost = |S| + k + (k-1) = |S| + 2k - 1. bcs(G) = min over covers and S. WLOG each U in S lies inside some side
(prune unused gates). bcs is computed exactly by `bcs.py` as weighted MaxSAT
(vars: biclique chosen, set present, decomposition chosen; weights 2 per biclique, 1 per set).

**Prop 1 (upper bound, hand).** s(G) <= bcs(G) <= bc(G). Proof: the circuit above has exactly that many gates and computes f_G.
Note also bc counts the absorbed version for free: OR-ing a term g with g => A_i into the B_i side costs the same as the final OR.

**Prop 2 (stars give P, hand).** Restrict to stars ({t},L): cost |L|-1+1 = |L|; with centers T (a vertex cover) and edges assigned
to centers, sum |L_t| = |E| (partition), plus (|T|-1) joining ORs: |E|+|T|-1, minimised by |T|=tau. Conversely any star cover
(overlaps allowed) has sum|L_t| >= |E| and centers forming a vertex cover, so the min is exactly P(G).
Verified: star-restricted bc = P(G) on all 993 connected graphs n<=7 (`sweep.out`, column 7 vs 6).

**Prop 3 (C4).** C4 = K_{2,2}: one biclique, cost 2+2-1 = 3 (versus P = 5). Matches the SAT value s=3.
In general K_{a,b}: a+b-1 (data: K33 5, K34 6).

## 2. C4-free graphs: bcs(G) = P(G) (hand argument, includes sharing)

Claim. If G has no C4 (equivalently any two vertices have <=1 common neighbour), then bcs(G) = P(G).
Proof sketch. (i) A biclique with |A|,|B|>=2 contains a C4, so all bicliques are stars. (ii) Merge stars with the same
center (union of leaf sets): never increases cost, so assume distinct centers t_1..t_k; the centers form a vertex cover
(single-edge bicliques: pick either end), so k >= tau. (iii) The OR-gates in S have size >=2 and lie inside a leaf set L_t. A set of size >=2
lying in L_t and in L_t' (t != t') would be two vertices with two common neighbours (the t, t' side: any two vertices u,w in
L_t ∩ L_t' have common neighbours t,t'), i.e. a C4. So S splits into disjoint families S_t of gates with set inside L_t, and building L_t needs
>= |L_t|-1 gates of S_t (a binary-union tree with |L_t| leaves). So |S| >= sum(|L_t|-1) and cost >= sum |L_t| - k + 2k - 1 = sum|L_t| + k - 1 >= |E| + tau - 1.
(sum |L_t| >= |E| since every edge is covered.) QED.
Consequence: the conjecture s = bcs below is, for C4-free graphs, exactly Note 1's claim s = |E|+tau-1, so it is
proven on the Lean-checked classes (forests, long cycles, windows of degree-2 vertices) and open elsewhere.
Data check: all 90 C4-free connected graphs n<=7 solved have bcs = P (`stats.py`, "bad []").
Note the converse fails: sharing alone can beat P with a C4 present but no *useful* non-star biclique, e.g. g6 `EQKo`
(C4 2-4-3-5 plus pendants 0-2, 1-3): no-sharing bc = P = 7 but bcs = 6 via stars at 2 and 3 sharing the subterm (x4 OR x5).
So "two stars with a common 2-set of leaves" is the sharing mechanism; K_{2,2} inside is the same phenomenon.

## 3. Conjecture

**Conjecture (exact formula).** For every graph G (no isolated-vertex issues), s(G) = bcs(G): the minimum circuit size of the edge
function in basis {AND, OR, NOT}, every gate counted, equals the cheapest shared biclique cover, with
bcs(G) = min over biclique covers (A_i,B_i)_{i<=k} and OR-DAGs S of  |S| + 2k - 1.
Special cases: bcs = |E|+tau-1 if G is C4-free; bcs(C4)=3; bcs(K_{a,b}) = a+b-1; bcs(K3)=4, K4=7, K5=10.

Supporting data (SAT lane `../sat-girth34/results.csv`, n<=6 so far): see table. NOT gates are never used by the bcs circuits;
the conjecture implicitly says NOT gates never help (they are monotone function, plausible by Razborov-type monotone-vs-nonmonotone
gap not mattering at this scale, but unproved and unlikely to be easy).

## 4. Data

Table A: n<=7 connected graphs (atlas), bcs computed exactly (11 dense n=7 graphs and K6 timed out, 30-60 s limit; those not counted).

| n | graphs solved | bcs < P | C4-free | C4-free with bcs = P |
|---|---|---|---|---|
| 2 | 1 | 0 | 1 | 1 |
| 3 | 2 | 0 | 2 | 2 |
| 4 | 6 | 3 | 3 | 3 |
| 5 | 21 | 13 | 8 | 8 |
| 6 | 111 | 92 | 19 | 19 |
| 7 | 842 | 785 | 57 | 57 |

(The "C4-free" column here means no two vertices with two common neighbours. Sharing is strictly better than no-sharing bc on 396 of these graphs; bc<P much more often than the C4 alone suggests, because triangle-rich dense graphs have many K_{2,2}.)

Table B: comparison with SAT exact sizes s(G) (51 graphs, all status EXACT at time of writing, n<=6, girth 3 and 4):
**s(G) = bcs(G) on 51/51**. With no-sharing bc only: equal on 31 of 36 earlier, e.g. `Dl{` (s=6, bc=7, bcs=6), `Dn{` (K5 minus an edge: s=8, bc=9, bcs=8). In both
SAT witnesses the saving is exactly OR-sharing: `Dl{` computes (x0|x2) once and uses it in both A={0,2,4} and the star term x4(x0|x2).
35 of the 51 have s < P. `D~{` = K5: s = 10 = bcs (SAT took k=10 after UNSAT at 9, 562 s).
Larger values: Q3 (cube): P=15, bcs=13; K_{3,3}: 5 (P=11); C6: 8; C8: 11; wheel W5: 11 (P=13).
(Table B should be recomputed with `python3 stats.py` as `results.csv` grows.)

## 5. Lower-bound side / what a proof would look like (hand, speculative)

* C4-free: reduces to Note 1 (section 2); no new lower bound.
* In general a gate-elimination proof would have to show a minimal circuit can be put in "biclique form": every AND gate's two
  inputs are ORs of vertex sets (A,B), A x B a subgraph of G. Failure modes to test, none seen yet in data n<=6: AND of non-OR terms (majority/K3
  tricks), XOR/NOT tricks, ANDs deeper than one level (e.g. (A AND (B OR (C AND D)))) -- but the last is a generalisation of absorbed products
  and costs the same as the flat version when C AND D => A.
* Possible refinement to watch for at n>=7: nested bicliques (A&B | C&D with A&B shared sub-ANDs) -- AND gates are not shared in bcs. If s < bcs ever
  appears, inspect the SAT circuit for a repeated AND of two ORs.

## 6. Open questions
1. Is s(G)=bcs(G) for all G? Need SAT data on n=6 dense graphs, n=7 (e.g. Q3 itself needs n=8: bcs 13 vs P 15 -- a good SAT target, k=12 UNSAT / k=13 SAT).
2. Asymptotics: bcs(K_n) looks like 3n-5 for n=3,4,5 but recursive halving suggests Theta(n log n); compute bcs(K6),K7 (timed out here, MaxSAT symmetric) -- if s(K_n)=O(n log n) then P=|E|+tau-1 is wildly off for dense graphs.
3. Does sharing of AND gates ever help (two bicliques with a common A-side and overlapping B-sides)? Equivalent to merging; bcs handles it by merging bicliques, but check.
4. Prove Note 1 for C4-free graphs of girth 3 (triangles): section 2 only reduces it.
