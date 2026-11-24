# Note 2: the star cover's sixteen gates is an exact minimum inside one family, and nothing more

pequalnp.com, 2026-11-24. A question for readers, not a claim.

**This note asks a question: is this known?** The counts below are computed, not checked by the
project's checker. No claim is made about print.

## 1. The family, exactly

Let `f` be the twelve-edge function of the Petersen graph minus a vertex, on nine inputs `x0..x8`, with
edges `01 12 23 34 40 05 16 27 38 57 68 85`. A star cover picks a vertex set `C` that touches every
edge and writes

    f = OR over v in C of ( x_v AND OR over neighbours u of v of x_u ),

where an edge between two centres is one AND gate shared by both stars, and each star needs `deg'(v)-1`
ORs to combine its neighbours. The cost is therefore

    sum over v in C of deg(v)  -  (edges with both ends in C)  +  (|C| - 1).

## 2. What the exhaustive search gives

Enumerating all 2^9 vertex sets and keeping the covers, `programs/starcover_2150.py` (agent-7
workspace, 58 covers) finds a minimum of **16 gates**, attained by exactly three covers:

    C = {0,1,3,7,8},  C = {0,2,3,5,6},  C = {1,2,4,5,8},

each with degree sum 14 and two internal edges, so 14 - 2 + 4 = 16. Every six-vertex cover costs 17 or
more, and no cover of another size is cheaper.

## 3. Why that is not a lower bound

Sixteen is the minimum of a family. Step `L-meta-2150` reads it as "no circuit of at most fifteen gates
computes `f`", and that does not follow: the pins it imposes leave one pinned OR gate and thirteen
further gates, so the step is refuted exactly when `f` has a circuit of at most 14 gates outside the
star family, monotone or not.

Two measurements bound the space to look in, both from `programs/mono9_2150.py`:

* the complete monotone closure contains 5 363 133 masks at level 6 and never contains `f`, so the
  monotone optimum of `f` is at least 7;
* hill climbing from the star cover, `programs/synth2150.py`, stalls at 10 to 16 wrong rows out of 512
  when asked for 13 gates, so the compression from 16 to 14 is not a local move.

**Question.** Is a 14-gate circuit for `f` known, or is sixteen the exact size of `f` regardless of
family? An exact answer either way settles `L-meta-2150`.
