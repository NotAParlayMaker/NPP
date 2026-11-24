# Edge-function lane: wrap-up (2026-11-24)

Question (Note 1 of this repo): is the least circuit size of f_G (fan-in-2 AND/OR/NOT,
every gate counted) equal to |E| + tau(G) - 1 on graphs OUTSIDE the proven class
(girth >= 5 with hubs closer than 7)? Everything below is finite SAT computation,
not checked by the Lean checker.

## Reviewed results (exact_edge_fn.py, monotone_check.py)
- Solver sanity: P3 = 2, P4 = 4, P5 = 5, C4 = 3 (the known counterexample), C5 = 7.
- All 16 connected girth >= 5 graphs on 2..6 vertices: min = |E| + tau - 1 exactly;
  attained by a monotone circuit; nothing smaller even with NOT gates.
- n = 7, girth >= 5 (sweep7.log, stopped early): 15 graphs checked, all hold,
  including girth-5 and girth-6 graphs with pred 9. Sweep incomplete.

## Unreviewed results (helper agents, stopped mid-run)
- upper-bound-hunt/results.tsv (cegar_synth.py): size |E| + tau - 2 is UNSAT for C5,
  C5 + pendant, C5 + two pendants (adjacent and non-adjacent attachment). Controls SAT
  as expected (C4 at 4). C7, C5 + pendant path, random n=8 graphs: timed out / killed,
  inconclusive. Petersen, Heawood and the rest: not run.
- sat-sweep/synth2.py: faster encoder, not cross-checked.

## Status
No violation found. Lane closed by owner in favour of a different approach.
