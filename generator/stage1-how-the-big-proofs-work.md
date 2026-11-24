# Stage 1: how the large accepted proofs are built

Written 24 November 2026, from a reading of the accepted files in
`lean/PEqualNP/Outside/` at upstream commit `99ec5f8`. Files read closely:
`L_meta_2036`, `L_meta_2529`, `L_meta_2746`, `L_meta_2549`, `R_meta_2303_317`, and the
headers and final theorems of about fifteen siblings.

## 1. What is being proved

Take a small graph. Its "edge function" has one true/false input per vertex and answers
"true" when both ends of some edge are switched on. The fleet wants the exact number of
AND, OR and NOT gates (each reading at most two wires) needed to compute this function,
for the Petersen graph with one vertex removed (9 inputs, 12 edges) and for a smaller
8-input relative of it (10 edges).

The expected answers are 16 gates for the 9-input function and 13 for the 8-input one.
Circuits of those sizes are known. The hard part is the other direction: showing that no
circuit with one gate fewer exists. There is no clever shortcut for that. Every possible
smaller circuit has to be ruled out, and Lean has to see it happen.

## 2. The idea that makes this checkable

There are far too many circuits to list. The accepted proofs shrink the problem with
three ideas.

**Signatures.** Pick a few hundred test inputs, half on which the function must answer
true ("positive rows") and half on which it must answer false ("negative rows"), arranged
in pairs. `L_meta_2036` uses 252 pairs; the 9-input proofs use 414. Every wire in a
circuit is then replaced by its "signature": the list of values it takes on those test
inputs, stored as two large binary numbers (one for the positive rows, one for the
negative rows). Two wires with the same signature are treated as the same wire. The wire
we want at the end has the signature "all ones, all zeros". I decoded the 252 pairs of
`L_meta_2036`: 152 of them are every pair of inputs that differ in exactly one position
with different answers, and 100 more were added, presumably wherever the search needed
them.

**Frontiers.** Read a circuit from the inputs towards the output and, at each moment,
write down the set of signatures that some later gate still needs. That set is the
"frontier". It starts as the set of inputs and must end as the single target signature.
Each gate takes one or two signatures out of the frontier, puts its result in, and may
or may not keep what it used. The Lean files call a legal sequence of this kind `Live`.
A general lemma (`extract`) shows that any real circuit with `k` gates gives such a
sequence with at most `k` steps. So if no sequence exists, no circuit exists.

**Pruning.** Most frontiers can be thrown away at once:

- Coverage. For every test pair, some signature in the frontier must tell the positive
  row from the negative row, because the final answer does and a gate cannot create a
  distinction that none of its inputs has. A frontier that fails this is dead.
- Size. Each AND or OR gate can shrink the frontier by at most one. With `k` gates left
  the frontier can hold at most about `k + 1` signatures.
- NOT count. The search is run separately for each number `t` of NOT gates still to
  come. Once `t` is zero the remaining circuit is monotone, and coverage becomes a
  stricter test.
- Sub-bounds. Switching one input off turns the graph into a smaller graph whose bound
  is already known. If the circuit wasted too many gates on that input, the smaller
  bound would be broken. This limits how certain inputs may be used (for example "a
  degree-two input may only be used once, by an OR gate"). The 9-input proofs track
  this with labels on wires called tags. Each such rule needs its own embedded proof of
  the smaller bound: `L_meta_2036` carries a 7-input "theta graph" certificate inside
  it, and the 9-input proofs carry the whole 8-input proof inside them.

With these rules the search over frontiers is finite and small enough to run.

## 3. What the certificate is, and what Lean verifies

The important point: **Lean redoes the whole search itself.** The file contains a Lean
function `search` that explores frontiers with the rules above, and a proof
(`search_complete`) that if a legal sequence existed, `search` would return true. The
theorem then only needs the fact "`search` returns false from the starting frontier".
That fact is established by the Lean kernel computing it (`decide +kernel`). This is
allowed; the banned `native_decide` is a different thing that trusts compiled code.

A single computation of that size would be too slow and too deep, so the file carries a
table of intermediate frontiers. This table is the "certificate". In `L_meta_2036`:

| gates left | frontiers stored | how each is checked |
|---|---|---|
| 8 | 1,698 | Lean runs the full search from it and gets "impossible" |
| 9 | 1,021 | Lean tries every single next gate and looks each result up one level down |
| 10 | 199 | same |
| 11 | 24 | same |
| 12 (start) | 1 | same |

The supporting data around the table:

- A list of every signature used (about 1,000), each stored once and referred to by a
  10-bit number.
- Hash tables so that "is this frontier in the table?" is one lookup. The lookup result
  is never trusted: Lean compares the frontier with the stored one.
- Symmetry. The graph has symmetries (8 for the 8-input graph, 12 for the 9-input one).
  Only one frontier per symmetric family is stored, and the lookup says which symmetry
  to apply. Lean proves that the symmetries preserve everything that matters.
- The checks are cut into about 150 to 200 separate small lemmas of 30 frontiers each,
  so no single computation is too big.

None of the data is trusted. If any number in the tables were wrong, a kernel
computation would return the wrong value and the file would fail to build. The data are
hints that make the check fast, and the price is file size: two thirds of
`L_meta_2036` (330 of 508 KB) is table data. That is why so many accepted files sit just
under the 512 KiB cap. The cap, not the search time, is what limits how hard a case this
method can reach.

The outside search program is not in the repository. Its job is to run the same search,
record which frontiers to store, pick the test pairs, and print the tables. The search
itself is light: Lean's kernel, which is slow, replays all of it in a few minutes.

## 4. How a new case is adapted from an old one

This was the most useful thing I learned. Almost all of the large accepted files are
**not new searches**. There are two certificates in circulation:

1. The 8-input, 12-gate certificate, first accepted as L-meta-1007 (credited to
   jfsantoropereira, pull request 2299).
2. The 9-input, 15-gate certificate with the first gate fixed to an AND of two
   non-adjacent inputs, first accepted as L-meta-1672 (credited to jmwalsh96, pull
   request 4290). It contains certificate 1 inside it.

A file cannot import another proof file, so each new proof pastes one of these two in
whole, renames it, and adds a short "glue" section that turns the new statement into
the old one. Examples:

| file | what it adds to the pasted certificate |
|---|---|
| `L_meta_2036` | nothing but a restatement: it is certificate 1 |
| `L_meta_2529` | 100 lines that rebuild the circuit so the fixed first gate and a final OR match certificate 2 |
| `L_meta_2555` | adds one unused gate to convert a bound with a first-gate condition into one without |
| `L_meta_1670` | a different first gate (adjacent inputs); the starting frontier and its tags change, the tables do not |
| `L_meta_2024`, `2022`, `1912`, `2044` | glue only |

The checksums of the embedded input signatures agree across eleven of the 9-input files
I compared, which confirms they share one table.

The small files (`L_meta_2746`, `L_meta_2549`) are a different kind: ordinary short
proofs for corner cases, such as "a circuit with only one gate cannot do this".

So a new step in this family is settled in one of two ways:

- **Glue.** Find a short argument that reduces it to one of the two certificates. Cheap,
  and what nearly everyone has done.
- **A new search.** Needed when no such reduction exists. This needs a search program
  and, usually, changes to the Lean rules. Only a few contributors have done this.

## 5. Costs measured on this machine

This session has 4 cores and 15 GB of memory (the earlier session had 2 and 7).

| step | time |
|---|---|
| Install elan and Lean 4.36.0, fetch Mathlib cache | about 3 minutes |
| Build `PEqualNP.Defs` | 25 seconds |
| Check `L_meta_2036` (508 KB) | 5 min 56 s, peak memory 10.3 GB |
| Check `L_meta_2529` (523 KB) | 5 min 10 s, peak memory 4.1 GB |

The two checks ran side by side, each on about one core. The 10.3 GB peak is above the
checker's stated 6.5 GB, yet that file was accepted, so Lean probably uses less when
less is available. I have not confirmed this. It is a risk to watch.

## 6. What this means for stages 2 and 3

- The search is not the bottleneck. A program doing the same work as Lean's kernel
  should finish in seconds to minutes here. I do not expect to need the Mac Studio for
  searching. The limits that bite are the 512 KiB file size and the checker's memory.
- The sensible "template" is the Lean side of an accepted proof, with credit, as the
  other contributors do. Writing 2,800 to 4,400 lines of soundness proof from nothing
  would take far longer and gain little. Our own work is the search program that
  produces the tables, plus any new Lean rules a new statement needs.
- Proposed stage 2 test: regenerate the tables of `L_meta_2036` with our own program
  and show the resulting file builds. That exercises every part: choosing pairs, the
  search, symmetry, the hash tables, the packing.
- For stage 3, the first question for any live step is whether glue is enough. Only if
  it is not do we need a new search, and then the generator tells us in advance (number
  of stored frontiers, so file size; number of search steps, so checking time) whether
  the result can fit under the limits.

## 7. What I am not sure about

- I have not seen the exact statements of L-meta-3104, 3138 and 3116. They are not in
  the repository, and I was told not to take desk steps before stage 3. The site keeps
  its public data on `data.pequalnp.com`, which this session may not reach.
- My guess, from `R_meta_2303_317`, is that 3104 is its hypothesis `marked`: a 13-gate
  bound for the 8-input function where the circuit must work in two modes at once. If
  so it is one gate deeper than certificate 1 and needs a new kind of move in the
  search, so it would be a new search and not glue. This is a guess until I see the
  statement.
- Whether a search one gate deeper fits in 512 KiB is unknown. The existing certificate
  at 12 gates already fills the file.
- How the original authors chose the extra 100 test pairs and which frontiers to store
  is not recorded. I will have to find choices that work; they need not match theirs.

## Words used

- **Gate, fan-in two:** a gate is one AND, OR or NOT; fan-in two means it reads at most
  two wires.
- **Kernel:** the small trusted core of Lean that does the final check of every proof.
- **`decide +kernel`:** asks the kernel to work out a yes/no fact by direct calculation.
- **Certificate:** data stored in the file that lets Lean confirm a result quickly. It
  is checked, never trusted.
- **Lease:** the desk's 20-minute reservation of a step for one agent.
- **Glue:** a short proof that converts one statement into another already proved.
