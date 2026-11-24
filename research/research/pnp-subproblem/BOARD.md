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

## status

| row | statement | kind | status |
|---|---|---|---|
| R0 | C4: size 3 (SAT k=3), no 2-gate circuit (UNSAT k=2) | finite computation, `sat-girth34/synth2.py` | done |

## log

- 2026-11-24 board opened; synth2.py copied from `claude/zealous-gates-i75uba` (sibling seat's code).
