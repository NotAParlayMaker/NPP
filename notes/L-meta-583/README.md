# L-meta-583 · The subdivided K₄ edge function needs 15 monotone gates

The inputs are the four original vertices (hubs) and the six new vertices
(midpoints). The output is true if an active hub is incident to an active
midpoint. Gates are binary AND and OR. The project permits gates with fewer
inputs and references to missing wires. In a minimum circuit for this
nonconstant function, one may propagate constants, bypass copies and
repeated operands, replace missing reads by their default false, and remove
dead gates. These simplifications preserve the function and never add gates.

## A 15-gate construction

For each hub, take the OR of its three incident midpoints and
AND that with the hub. This costs three gates per hub. Combine the four
terms with three OR gates to get 15 gates. The accompanying Python program
checks the construction on all 1,024 assignments.

## Why 14 gates cannot suffice

Fix any one midpoint to false. The remaining graph consists of
three internally disjoint paths of lengths 2, 4 and 4 between the two hubs
opposite the deleted midpoint. For example, deleting midpoint 4 (on edge
01) leaves paths 2-9-3, 2-5-0-6-3 and 2-7-1-8-3. The four hubs form a
vertex cover, and the disjoint edges 0-5, 1-7, 2-9 and 3-8 force every
cover to have size at least four. Permuting hubs covers all six deletions.

The project's checked theorem L_meta_615, with internal vertex counts
p = 1, q = r = 3 and minimum cover size t = 4, says this restricted
function needs at least p + q + r + 2 + t = 13 monotone gates. [Lean theorem](https://github.com/brilliant-hq/pequalnp-proofs/blob/334c967c8c0f10b17c6db235605a464e1436ec08/lean/PEqualNP/Outside/L_meta_615.lean)

Suppose a minimum circuit has at most 14 gates. Every midpoint must be
read because changing it can change the output. If two different gates
read the same midpoint, fixing it to false eliminates both gates by
constant propagation. This leaves at most 12 gates for the restricted
function, a contradiction. Its unique reader cannot be an AND gate
either. Setting the midpoint to false would make that gate constant and
eliminate a downstream gate as well. The reader cannot itself be the
output in this case because the restricted function is nonconstant.
Every midpoint therefore has exactly one reader, an OR gate.

Consider the earliest gate that reads a midpoint. If its other operand is
another midpoint, exchanging the two leaves this gate and the whole
circuit unchanged, since both have this gate as their unique reader.
The two midpoints have different endpoints. Switching them while only a
hub in the symmetric difference of their endpoint sets is active
distinguishes them in the target function.

Otherwise the other operand depends only on hubs. It is true when all hubs
are true, since constants and copies have been simplified and a
nonconstant monotone function is true on the all-true input. In that
setting the OR gate masks changes to its midpoint. With all other
midpoints false the target changes precisely when this midpoint does.
This contradicts correctness and proves the lower bound of 15.

## Reproducing the checks

From this directory, run the following commands with Python 3.10 or later and
GCC with C++20 support.

```sh
python3 verify_graph.py
bash reproduce.sh
```

The Python check verifies the 15-gate construction on all 1,024 inputs and
the paths and vertex covers for all six restrictions. The second command
checks the lower bound independently by enumerating prefixes of circuits.
Its final row is `8 1488 0`, meaning that it considered 1,488 eight-gate
prefixes after earlier pruning and eliminated them all. A circuit depending
on all ten inputs needs at least nine binary gates, so every candidate at
the proposed size would have such a prefix. [Search argument](search.txt)

The project has checked the theta-graph theorem in Lean. The deduction above
and the independent enumeration for L-meta-583 have not been formalized in Lean.
