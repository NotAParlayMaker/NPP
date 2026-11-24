# note 2: reproduction data and programs

Programs behind `notes/note-2-four-cycle-freeness.md`. All are plain Python 3, no dependencies.

`f_G` is the edge function `OR over {u,v} in E of (x_u AND x_v)`; sizes count every fan-in-two
gate, AND and OR only; `tau(G)` is the vertex cover number; the formula is `|E| + tau(G) - 1`.

## Expected output

The joint table is the point of the note: 4-cycle-freeness is *sufficient* for the formula to be
exact, and it is not necessary. `note2_table.py` prints the has-4-cycle-by-verdict table, which
`full6.py` cannot, because `full6.py` reports `tight` over all graphs plus a separate
`mismatch_free` count, leaving the number of tight graphs that do contain a 4-cycle invisible.

    $ python3 note2_table.py closure_n6_k10.txt 6
    n=6 masks=1856991
    has_4cycle  unknown   tight   below  above  graphs
    False             0    7983       0      0    7983
    True           1504     360   22920      0   24784
    exactly-tight without a 4-cycle: 7983; with a 4-cycle: 360
    below the formula without a 4-cycle: 0; with a 4-cycle: 22920
    NOTE-2 CLAIM HOLDS

The weaker cost-8 closure (`closure2 6 8`, 377985 masks) decides less but agrees where it looks:

    False           910    7073       0      0    7983
    True          12519     180   12085      0   24784

## Generating the closure

    gcc -O2 -o closure2 closure2.c        # needs a C compiler; prints one line per level
    ./closure2 6 10 > closure_n6_k10.txt  # 1856991 masks, about 66 MB
    ./closure2 5 9  > closure_n5.txt

Each line is `<mask in hex> <cost>`; a mask is one wire's truth table over the n inputs, cost is
the fewest fan-in-two AND/OR gates producing it. Absence of a target mask below a cost bound is a
proof of a strict lower bound. Interior wires are unrestricted.

## The rest

    python3 formula_build.py       # upper bound |E|+tau-1 by construction, all graphs n <= 6
    python3 verify_formula_n7.py   # same construction on the n = 7 classes that fit
    python3 exact_ref.py c5 7      # exact minimum for C5, by hand-checked closure
    python3 all5.py                # exhaustive n = 5 table: 547 tight, 475 above, 0 below
    python3 full6.py closure_n6.txt
