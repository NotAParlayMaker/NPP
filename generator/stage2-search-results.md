# Stage 2: our own search, and what it says about the open steps

Written 24 November 2026. Machine: 4 cores, 15 GB. Upstream at `048b39b`.

## What exists now

- `generator/search1672.py`: our own program that does the same frontier search as the
  9-input certificate (the one first accepted as L-meta-1672). It is a line-by-line port
  of the Lean functions `stepTest`, `unaryMoves`, `binaryMoves` and `search`, with the
  same rules and tags. It reads the test rows from an accepted file.
- `generator/examples/L_meta_3116.lean`: a complete proof file for step L-meta-3116,
  built here. `L_meta_3116_glue_only.lean` is just the new part (about 190 lines).

Not built: a program that prints new lookup tables in the Lean file's format. The
measurements below show why that would not have helped for the steps now open.

## Test against an accepted case

Starting from the nine inputs with 14 gates allowed, for every number of NOT gates from
0 to 6, the program reports "target not reachable". That is the result the accepted
certificate proves. The whole search visits 46,406 positions and takes about 3 seconds.

Lean's kernel is far slower. Timed here on four direct searches: about **100 search
steps per second**. The checker runs the kernel twice (once to build, once to re-check),
so a 20-minute check leaves room for only about 40,000 search steps on top of the
4 minutes the embedded 8-input proof needs. The accepted certificate gets under this by
storing positions and by using the graph's 12 symmetries, which cut the work twelvefold.

## What the three live steps are

Read from the public list on `data.pequalnp.com`:

- **L-meta-3116**: nine inputs, plus the wires AND(x0, x3) and its NOT given for free.
  No circuit with 13 or fewer gates. *Glue is enough.* Proof written and built; the
  project's own checker, run locally, printed ACCEPTED. But four pull requests from
  other agents (5924, 5974, 6013, 6061) were already open, the desk no longer offers
  the step, and nothing was submitted.
- **L-meta-3138**: first gate OR(x0, x3), then 13 gates with at most one NOT, then a
  final OR. Needs a new search.
- **L-meta-3104**: 8 inputs, 13 gates, a circuit that must work in two modes. Needs a
  new search and new Lean rules. Not measured.

## Measured size of the new searches

"Positions" is how many distinct positions the search visits. "Replay" is how many
search steps Lean would need with no stored tables. For comparison, the accepted
certificate is the first row. Every row came out "target not reachable", so each
statement looks true.

| case | positions | replay |
|---|---|---|
| accepted certificate (nine inputs, 14 gates) | 46 thousand | 470 thousand |
| 3120, input 6, all pieces | 21 thousand | 110 thousand |
| 3120, input 5, all pieces | 140 thousand | 1.0 million |
| 3138 | 3.9 million | not counted |
| 1666 (first gate NOT x4) | 0.75 million | 11.6 million |
| 1665 and 3271 (first gate NOT x0) | 1.5 million | 31.6 million |

Step 3120 is a sibling of 3116 with no pull request yet. It is the only one close to
feasible, and it still does not fit: its starting positions have no symmetry, so
nothing cuts the 110 thousand replay steps down to the 40 thousand a check allows, and
storing positions costs more file space than is free. It could be done by splitting it
with reductions into three or four separate statements, each with its own file. That is
several sessions of work with no certainty.

## Conclusions

1. The search is never the bottleneck. Seconds here. The Mac Studio is not needed.
2. The limits are Lean's kernel speed inside a 20-minute check and the 512 KiB file.
3. Steps that glue can settle are taken by other agents within about an hour of being
   posted. Steps with no pull request are the ones that need a search too large for
   one file.
4. The pipeline works end to end: assemble one file, pass the project's file-rule
   guard, build, and pass the project's checker locally in about 5 minutes.

## How to rerun

    python3 generator/search1672.py lean/PEqualNP/Outside/L_meta_2529.lean old
    python3 generator/search1672.py lean/PEqualNP/Outside/L_meta_2529.lean 3120
    python3 generator/search1672.py lean/PEqualNP/Outside/L_meta_2529.lean 3138

To check a finished proof file as the project does (the statement file holds the exact
posted statement):

    node .github/scripts/outside-guard.mjs imports <file> <imports.json> <path in repo> check
    node tools/check-lean.mjs <file> <statement file> check
