# Std.Sat.AIG at Lean v4.36.0 as infrastructure for a circuit lower-bound project

Sources: tag v4.36.0, `src/Std/Sat/AIG/*.lean`, fetched with raw.githubusercontent.com (the GitHub API listing was refused; file names were taken from the `public import` lines of `src/Std/Sat/AIG.lean`). Saved copies are in the scratchpad `aig-src/`. File sizes: Basic 635 lines, CNF 920, Cached 132, CachedGates 96, CachedLemmas 257, CachedGatesLemmas 207, LawfulOperator 174, Lemmas 204, Relabel 218, RelabelNat 388, RefVec 215, If 307. Nothing here was compiled; Lean is not installed. Everything is read from source.

## VERDICT

**AIG would replace**: (a) a hand-rolled DAG datatype with well-formedness (`AIG.IsDAG`, `AIG.Ref`, `AIG.Decl`); (b) the semantics `denote` plus its unfolding lemmas (`denote_idx_gate` etc.); (c) atom relabelling (`AIG.relabel`, `relabelNat` with `relabel_size_eq_size`); (d) a verified Tseitin CNF encoding (`toCNF`, `toCNF_equisat`) if we ever go through SAT; (e) append-only, semantics-preserving construction (`LawfulOperator` + `denote_mk*Cached`) for building circuits.

**AIG can NOT give us**: (1) exact size in our fan-in-2 AND/OR/NOT basis, because inversion is a free edge bit and there is no OR or NOT node; (2) any restriction, constant-substitution, cone-extraction, gate-deletion or reindexing operation (none exist, and the append-only design with `LawfulOperator.decl_eq` works against them); (3) any lemma tying `decls.size` to minimality or to reachability (no GC, no cone, no "size of the circuit rooted at ref"); (4) any lower-bound machinery.

`decls.size` counts dead nodes plus the constant node plus atom nodes. Only `.gate` entries are comparable to gates, and only after a separate reachability argument that we would write ourselves. Recommendation: define our own `Circuit` type with exact cost, and use AIG only as a verified back end (conversion to AIG, then `toCNF`/`relabelNat`), or copy its `IsDAG` + `denote` pattern.

## 1. Representation, inversion, evaluation, well-formedness
Module `Std.Sat.AIG.Basic` (namespace `Std.Sat.AIG`):
- `structure Fanin where ofRaw :: val : Nat`. It is a Nat/Bool pair packed into one Nat: `Fanin.mk (gate : Nat) (invert : Bool)`, `Fanin.gate f = f.val / 2`, `Fanin.invert`, `Fanin.flip`.
- `inductive Decl (α : Type) | false | atom (idx : α) | gate (l r : Fanin)`. There are three node kinds only: constant false, an input atom, and a binary gate that is always AND of its two fanins after each fanin's optional inversion. There is no OR, no NOT node, and no true node. Constant true is `Ref` to node 0 with `invert := true`.
- `structure AIG (α) [DecidableEq α] [Hashable α]` has fields `decls : Array (AIG.Decl α)`, `cache : AIG.Cache α decls`, `hdag : AIG.IsDAG α decls`, `hzero : 0 < decls.size`, `hconst : decls[0]'hzero = .false`.
- `def IsDAG (α) (decls : Array (Decl α)) : Prop := ∀ ⦃i lhs rhs⦄ (h : i < decls.size), decls[i] = .gate lhs rhs → lhs.gate < i ∧ rhs.gate < i`. This is topological order by array index. `IsDAG.empty : IsDAG α #[.false]`.
- `AIG.atom_unique`: atoms are unique within `decls` (enforced by the cache invariant `Cache.WF`).
- `structure Ref (aig) where gate : Nat; invert : Bool; hgate : gate < aig.decls.size`. A `Ref` carries a proof it is in bounds. `Ref.cast (ref : Ref aig1) (h : aig1.decls.size ≤ aig2.decls.size) : Ref aig2`, `Ref.flip`, `Ref.not := ref.flip true`.
- `structure Entrypoint (α) where aig : AIG α; ref : Ref aig`. The output is a single Ref, so there is no multi-output circuit except `RefVec aig w` (`Std.Sat.AIG.RefVec`).
- `BinaryInput aig` (lhs, rhs : Ref aig), `TernaryInput`.
- Evaluation: `def denote (assign : α → Bool) (entry : Entrypoint α) : Bool := go entry.ref.gate entry.aig.decls assign entry.ref.hgate entry.aig.hdag ^^ entry.ref.invert`. The `go` clause for gates is `xor lval lhs.invert && xor rval rhs.invert`. It is defined by well-founded recursion on the gate index, with `termination_by (x, 0)`. Notation is `⟦aig, ref, assign⟧`.
- Unfolding lemmas in `Std.Sat.AIG.Lemmas`: `denote_idx_false`, `denote_idx_atom`, `denote_idx_gate` (the lhs-and-rhs statement with `^^ invert`), `denote_idx_trichotomy`, `Ref.denote_flip`, `Ref.denote_not`, `denote_congr` (agreement of assignments on atoms below a node), `of_isConstant`, `denote_getConstant`.
- Also `Entrypoint.Unsat`, `UnsatAt`, `isConstant`, `getConstant`.

## 2. Rewrites, relabelling, cached construction, size lemmas, optimisation
- `Std.Sat.AIG.LawfulOperator`: `structure IsPrefix (decls1 decls2)` (`size_le`, `idx_eq`) and `class LawfulOperator (α) (β : AIG α → Type) (f : (aig : AIG α) → β aig → Entrypoint α)` with fields `le_size : aig.decls.size ≤ (f aig input).aig.decls.size` and `decl_eq : ∀ ... idx (h1 : idx < aig.decls.size) h2, (f aig input).aig.decls[idx] = aig.decls[idx]`. Free theorems: `LawfulOperator.isPrefix_aig`, `denote_input_entry`, `denote_cast_entry`, `denote_mem_prefix`, and `denote.eq_of_isPrefix`. So every constructor only appends and never modifies, and the semantics of old nodes is preserved.
- `Std.Sat.AIG.Cached`: `mkAtomCached`, `mkConstCached aig val : Ref aig := ⟨0, val, aig.hzero⟩`, `mkGateCached (aig) (input : BinaryInput aig) : Entrypoint α`. The last is hash-consed (cache hit returns the existing index), orders its inputs by gate index, and does only one-level simplification from Brummayer-Biere (MEMICS06): `x ∧ false`, `x ∧ true`, `x ∧ x` (same polarity), and `x ∧ ¬x`. Anything else pushes one new `.gate`. No two-level rules ("TODO: rest of the table" in the source).
- `Std.Sat.AIG.CachedLemmas`: `mkGateCached_le_size`, `mkGateCached_decl_eq`, `denote_mkGateCached : ⟦aig.mkGateCached input, assign⟧ = (⟦aig, input.lhs, assign⟧ && ⟦aig, input.rhs, assign⟧)`, plus the atom analogues (`mkAtomCached_le_size`, `denote_mkAtomCached`).
- `Std.Sat.AIG.CachedGates` and `CachedGatesLemmas`: `mkNotCached (aig) (gate : Ref aig) := ⟨aig, gate.not⟩` (adds no node), `mkAndCached`, `mkOrCached` (`mkGateCached (input.invert true true)` followed by `.not`), `mkXorCached` (3 gates), `mkBEqCached` (3), `mkImpCached` (1). Each has `*_le_size`, `*_decl_eq`, `instance : LawfulOperator α BinaryInput mk*Cached`, and `denote_mk*Cached`.
- Size lemmas: only `*_le_size` (monotone) and `Relabel.relabel_size_eq_size : (aig.relabel r hinj).decls.size = aig.decls.size`, `relabelNat_size_eq_size`, `Entrypoint.relabel_size_eq`. There is no exact "+1 on miss / +0 on hit" lemma. The code shows it, but it is not stated as a theorem. Nothing says anything about the number of `.gate` entries.
- `Std.Sat.AIG.Relabel`: `AIG.relabel (r : α → β) (aig) (hinj : ∀ x y, x ∈ aig → y ∈ aig → r x = r y → x = y) : AIG β`, with `denote_relabel`, `relabel_unsat_iff`, and `Entrypoint.relabel`. Atom renaming only, injective on the atoms present. It cannot substitute constants.
- `Std.Sat.AIG.RelabelNat`: `AIG.relabelNat (aig : AIG α) : AIG Nat` and `relabelNat'` returning the `HashMap`, with `relabelNat_unsat_iff`.
- `Std.Sat.AIG.CNF`: the verified Tseitin transform (`toCNF`, `toCNF_equisat`, and the `Cache.Inv` invariant machinery).
- Others: `RefVec`, `RefVecOperator`, `LawfulVecOperator`, `If` (`mkIfCached`).
- Constant propagation exists only locally and at construction time (the `mkGateCached.go` cases above). There is no whole-AIG simplification, sweeping, or rewriting pass.

## 3. Fit for our operations
| Our operation | In AIG? |
|---|---|
| Restrict inputs to constants | No. `relabel` renames atoms only. We would rebuild the circuit by structural recursion: map each decl, replace `.atom a` by a `Ref` to node 0, and re-run `mkGateCached` over `decls` in index order. This is expressible and does simplify, but we would have to prove `denote` correctness and any size bound ourselves. `denote_mkGateCached` + `denote_idx_gate` make the semantic proof short. |
| Output cone | No. There is no reachability, no extraction, and no theorem that unreachable nodes do not affect `denote`. (`denote_congr` is the nearest.) We would write it. |
| NOT to constant substitution | NOT does not exist as a node (see below). Substituting a constant for a gate is a rebuild, as for restriction. |
| Gate deletion with reindexing | No. The API is append-only (`LawfulOperator.decl_eq`). `IsDAG` is a global index condition, so deletion needs an order-preserving index map and a proof it keeps `hdag`, the cache `WF`, and `hconst`. None is provided. |
| Exact gate count | No. See below. |

### Cost-model mismatch (precise)
Our basis is fan-in-2 AND, OR, NOT, and every NOT counts as a gate. AIG has AND only, with free inversion on each edge (the `Fanin.invert` bit, `Ref.invert`).
- Translating our circuit into an AIG: AND gives 1 `.gate`. NOT gives 0 (just `Ref.not`, `mkNotCached`). OR gives 1 `.gate` (De Morgan, `mkOrCached`). So `AIG gate count <= our AND + OR count`, and the NOT gates vanish. Writing `s_AIG` for the minimal number of AND nodes and `s` for our size, `s_AIG <= s - #NOT`, hence `s_AIG <= s`. In the other direction, an AIG with g AND nodes converts to our basis with at most g + (number of distinct inverted edges, possibly plus an inverted output). Each node needs both polarities in the worst case, so the converted circuit has size at most about 2g + (inverted output), and the factor 2 is attained for some circuits. Hence `s_AIG <= s <= 2*s_AIG + 1` roughly. Make this a theorem only if we need it, because the constant depends on conventions (output negation, fan-out).
- Not one-to-one: an AIG does not record which polarities are materialized, so exact size in our basis is not recoverable from `decls.size` or from the `.gate` count. Example: OR(x,y) is 1 gate in AIG (`mkOrCached`) and 1 gate in ours, but ¬OR(x,y) is 1 in AIG and 2 in ours. XOR is 3 AIG gates (`mkXorCached`) and 4 in our basis (OR+AND+NOT+AND or similar) or 5 depending on the formula. The minimizing translation from AIG to our basis (choosing NOT placement) is its own optimization problem. Any lower bound on AIG size gives at best a bound within the constant factor above. This is fine for asymptotic bounds (a super-linear bound transfers) but not for exact small-case bounds like "needs at least 5n−o(n)", where the constants matter.
- Also constants: our basis may or may not have constant gates. AIG's node 0 (`.false`) and the atoms are in `decls.size`, so `decls.size = 1 + #atoms + #gates`, and dead gates also count.

### Does `decls.size` relate to a minimal circuit?
No. There is no minimality notion, no GC, no deletion, and no reachability lemma anywhere in `Std.Sat.AIG.*`. A grep for gc, garbage, prune, reachable, cone, minimal and dead found nothing (the hits were unrelated). `decls.size` is an upper bound on the size of any circuit that denotes the entry's function, with the overhead above. The only monotonicity lemmas are `le_size`. Since the cache hash-conses structurally identical gates, the array has no duplicate `.gate` entries (`Cache.WF`), but that is not stated as a size theorem either.

## 4. Other Lean projects (found via web search, snippets only, not opened or compiled; arXiv IDs as returned by the search tool)
- Formalizing PARITY Circuit Lower Bounds in Lean (Hastad, constant depth): https://arxiv.org/pdf/2609.24188 , source reported at github.com/formalcs/circuit-complexity (Lean 4.33.1).
- Unrestricted Boolean multiplicative complexity of four-term binary polynomial multiplication (MC = 9, XOR-AND circuits, Mathlib): https://arxiv.org/pdf/2608.30238 ; source reported at github.com/GregoryMorse/unrestricted-boolean-mul; import PR https://github.com/Vilin97/lean-pool/pull/539 . Related: multiplicative complexity of the 3-bit low-half multiplier, https://arxiv.org/pdf/2611.15992 ; 3x3 matrix multiplication over F2 lower bound 21, https://arxiv.org/pdf/2609.18722 .
- Circuit activity bounds, parity activity >= n/4: https://github.com/KalachevGleb/circuit-activity-lean
- From Dag-Like Proofs to Boolean Circuits in Lean: https://arxiv.org/pdf/2607.20186
- Inductive Boolean circuit type for complexity-shortcut counterexamples (low assurance, treat claims cautiously): https://github.com/chainsyncstore/lean4-complexity-adjudicator
- Mathlib: the searches found no general Boolean-circuit DAG type or circuit-size lower-bound library. I did not browse Mathlib source. Check `Mathlib/Computability` and Zulip before concluding that none exists. No general superpolynomial circuit-size lower bound and no Shannon counting-bound formalization turned up.
- The Lean-core AIG library itself (this report) is the only verified DAG with a bit-blasting/SAT pipeline (`bv_decide`).
