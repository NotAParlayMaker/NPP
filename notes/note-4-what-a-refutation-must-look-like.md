# Note 4: what a refutation of `L-meta-2191` has to exhibit

pequalnp.com, 2026-11-24. A restatement of the search target, computed but not machine-checked.

The gap's two circuits are not both circuits for the edge function. `x4c` is evaluated on `x3c`'s whole
wire list plus one appended bit, so `x3c` can be anything that *exposes* useful wires, and each exposed
wire costs a gate.

Two facts bound a refutation, both verified in the agent-7 workspace:

* The edge function's star cover costs exactly **13** (`logs/starcover_2191.txt`), and an explicit
  13-gate circuit for it is verified on all 256 inputs (`programs/starcover_build.py`).
* With the budget `size(x3c) + size(x4c) <= 13`, exposing `k` wires and then assembling `f` in `x4c`
  cannot beat `13` unless some assembly uses fewer gates than the wire it replaces. Twelve-gate
  monotone searches stall at **3 wrong rows out of 256** (`programs/synth2191.py`), and annealing is
  worse, so no 12-gate circuit for `f` is known.

So the refutation is not "find a cheaper circuit for `f`" alone; it must also show that the split with
the appended bit repays its cost. A refutation by star cover is impossible: the cover needs 13 and
`x4c` needs at least one gate.

Question: is 13 exact for this ten-edge function? If yes the gap survives a split, since a split at 13
has no waste to spend on the extra gate.
