# Lit lane: is |E| + tau(G) - 1 for f_G known? (Note 1, section 6)

Date of search: 2026-11-24. Tools: WebSearch (snippet-level summaries only), WebFetch, curl (only web.vu.lt
and arxiv-hosted PDFs reachable; econpapers.repec.org, mathnet.ru and link.springer.com did not resolve in this
sandbox, so the Red'kin chapter itself and the Springer pages were NOT opened).

## (a) Verdict

**Not found.** Partial, indirect evidence only. In everything actually opened I found no statement of the exact
size of f_G (OR of ANDs of edges) in {AND,OR,NOT} with NOT counted, for any graph class, and no statement that
implies (a)-(c) of Note 1.

What is in print, in this basis and cost measure: Red'kin (1973) proved C(parity_n) = 4n - 4 over {AND,OR,NOT}
(Jukna draft, Table 1.2, "C(parity_n) = 4n-4, Redkin (1973)" and Sec 1.5.2, "tight"). This is the only exact
all-gates-counted AND/OR/NOT value located, and it is for parity, not for f_G. It shows the method (exact
minimality with NOT counted) exists in the literature, but gives no result for monotone quadratic forms.

Caveats on coverage: Red'kin's own papers, Knuth 7.1.2, Lenz-Wegener, Mirwald-Schnorr, Amano-Maruoka (journal) and the
2012 printed book were NOT opened. Absence of a hit in the sources actually read is not proof of absence in these.
"Not found" is a statement about my search, not about the literature.

## (b) Per-source table

Legend: OPENED = full text or a substantial part read by me (via pdftotext, text searched and passages read);
SNIPPET = only a search-result summary seen; basis B2 = all 16 binary gates, DM = {AND,OR,NOT}.

| Source | Status | Basis | Cost | What it says | Relation to |E|+tau-1 |
|---|---|---|---|---|---|
| Jukna, Boolean Function Complexity, Springer 2012 | NOT opened (printed form). Opened: TOC.pdf, Chapter 1 (chapter1.pdf, Springer proof version, 2497 lines), Chapter 9 (Chapter9.pdf), and the older public draft bool-V7.pdf (28k lines, searched for keywords: Red'kin, quadratic, vertex cover, single-level, Lenz, Mirwald, Amano; passages read). All from web.vu.lt/mif/s.jukna/boolean/ | various | various | Sec 1.5.2 / Table 1.2: parity C = 4n-4 over {AND,OR,NOT} (Red'kin 1973; "tight"), 7n-7 over {AND,NOT} or {OR,NOT}. Thm 1.29 (Schnorr 1974): AND+OR gates for parity = 3(n-1), NOT gates not counted. Thm 1.28: 2n-4 for threshold-2 in B2. Sec 7.2 (draft): "quadratic function f_G = OR x_i x_j"; L+(f_G) <= 2|E|; Example 7.1 complete bipartite K_{S,T} gives monotone formula leafsize n; Thm 7.2 (Jukna 2006): triangle-free C4-free G gives monotone formula leaves >= |E|. Ch. 9 has a "Vertex Cover function" (monotone function of an edge-indicator input: "G has cover of size k"), a different function, not f_G. No exact circuit-size theorem for f_G, no |E|+tau term anywhere found. | Related only. Thm 7.2 is the formula/leaves/monotone analogue (already in Note 1). The K_{S,T} formula n matches the star case n (Note 1 star K_{1,n}, size n) in spirit but is a formula upper bound, not an exact circuit result. |
| Red'kin 1973, "Proof of minimality of circuits consisting of functional elements" (Problemy Kibernetiki; Springer English chapter 10.1007/978-1-4757-0079-4_4) | SNIPPET only (search listing; page fetch blocked). Title and the 4n-4 value verified only via the Jukna draft, not Red'kin | DM | gates incl. NOT (4n-4 = 3(n-1) AND/OR + (n-1) NOT, my arithmetic, consistent with Schnorr Thm 1.29; the "NOT counted" reading is inferred, not read from Red'kin) | Parity exact 4n-4. Jukna also credits Cardot 1952 with S(parity)=4n-4 (S = contact/switching measure, per Jukna's table; not verified). | No f_G result seen. Method (adaptive restriction eliminating gates incl. NOTs) is the same family as the Lean proof. NOT verified that Red'kin treats any monotone or graph function. |
| Kojevnikov-Kulikov-Yaroslavtsev, SAT 2009 | SNIPPET only (dblp, abstract summaries). Full text not opened | B2 | gates, NOT free | Abstract: SAT-solver search for small circuits, focused on MOD_{K,k} functions. | No graph functions seen. |
| Kulikov-Pechenev-Slezkin, "SAT-based circuit local improvement" (arXiv 2102.12579v3, MFCS 2022) | OPENED (pdftotext of full PDF, keyword scans plus abstract/Sec 1-2 read) | B2 | gates, NOT free | Exact synthesis feasible to ~size 7 quickly, ~size 13 takes over a week. Tables 1-4 concern SUM_n, MOD3, symmetric functions, running times. Knuth cited for exact optima of SUM_n, n <= 7. Keyword scan for graph/edge/vertex/quadratic: no hits relevant. | No graph-function table. Useful only as a feasibility hint: exact B2 synthesis for 6-8 variable f_G would be a size ~6-12 search. |
| Knuth, TAOCP 4A 7.1.2 | SNIPPET only (secondary web summaries). Not opened | B2 (all 2-input gates cost 1; 1-input NOT free) | gates, NOT free | Secondary summaries: exact optimal costs for all 5-variable functions (NPN classes, max 12 gates); exhaustive for symmetric functions of 4-5 variables. | Different basis. Could give B2 sizes for P_5, C_5, K_{1,4}, etc., but B2 values are not comparable (C4 gives 3 in both only by coincidence of the XOR-free circuit). Not a source for AND/OR/NOT counts. |
| Amano-Maruoka, Algorithmica 46 (2006) "The monotone circuit complexity of quadratic Boolean functions" | SNIPPET only (abstract via search; ISAAC 2004 version abstract). Journal not opened. Jukna's TR05-021 (already opened per Note 1) quotes it | monotone (AND, OR, no NOT) | gates / conjunctive complexity | Abstract: exponential gap between single-level and general monotone circuits for quadratic functions; set of quadratic functions with monotone complexity strictly < single-level complexity. | Monotone, asymptotic-gap results; no exact value for path/cycle. Does not contradict. |
| Lenz-Wegener TCS 1991 | SNIPPET only (second-hand via ECCC TR05-021 reference list: "multiplicative complexity of quadratic forms over {OR,AND,0,1}", linked to single-level / bipartite structure). Paper not found or opened | monotone | AND gates (multiplicative) | Second-hand only. | Unknown; counts AND gates only, so cannot directly give |E|+tau-1 anyway. |
| Mirwald-Schnorr TCS 102 (1992) | SNIPPET only (abstract summary) | over GF(2) / XOR-AND | multiplicative complexity of quadratic forms = half matrix rank | Not about OR of ANDs; quadratic forms over GF(2). | Irrelevant to f_G (OR-form, not XOR-form). |
| Cavalar-Oliveira, "Boolean circuit complexity and two-dimensional cover problems" (arXiv 2503.14117) | SNIPPET only | n/a | n/a | Graph cover complexity vs circuit lower bounds; random-graph cover complexity linear. | Not an exact size result; probably not relevant. Mentioned for completeness. |
| Golovnev-Hirsch, Find et al. gate elimination, "weighted gate elimination quadratic dispersers" | SNIPPET only | B2 | gates | Generic 3n..3.11n lower bounds for dispersers. | Different goal (explicit hard functions); no exact sparse-graph values. |

Direct phrase searches ("vertex cover" "circuit complexity" "graph function" exact; quadratic boolean function circuit
size vertex cover; edge function exact circuit size NOT gates; gate elimination path cycle tight): about 7 queries
this session, 0 hits stating an exact size for f_G.

## (c) Exact values from print usable as test data

Honest answer: very little.
1. Parity in {AND,OR,NOT}, NOT counted: C(parity_n) = 4n - 4 (Red'kin 1973, as quoted in Jukna draft Table 1.2).
   Parity_2 gives 4, parity_3 gives 8. Check: XOR = (x OR y) AND NOT(x AND y) uses OR, AND, NOT, AND = 4 gates, matching 4n-4 at n=2.
   Useful only as a sanity check that a counter for this basis reproduces a published value; it says nothing about f_G.
2. Threshold-2 / complete graph (Jukna Thm 1.28, Wegener): >= 2n - 4 gates in B2 (NOT free). Dense, different class,
   B2 basis. Not directly comparable.
3. Parity 3(n-1) AND/OR gates with NOT uncounted (Schnorr). Separates the two cost measures; do not mix.
4. Knuth 7.1.2 table of exact B2 costs for all 5-variable functions exists (not read); it would give B2 values for
   P_5 (path on 5 vertices, 5 variables), C_5, K_{1,4}, but obtaining them needs the book or Knuth's published
   programs. Alternative: compute them ourselves with SAT (Kulikov-style) in B2 and in {AND,OR,NOT}; sizes <= 8 are
   within quick reach per Kulikov et al. This is the only realistic source of independent test data, and would be
   self-generated, not from print.

## Recommendations
- Leave the question "open as far as this search goes", and state the red-flag list: Red'kin's 1973 paper itself,
  Knuth 7.1.2 text, Lenz-Wegener, Amano-Maruoka journal version, printed Jukna book (his book may differ from draft).
- To close the remaining gaps one needs access to econpapers/Springer/mathnet (blocked here) or a library copy.
- The closest published structure found is gate elimination for parity (Schnorr / Red'kin): same technique,
  different function.

## Honesty log
- Opened with text extraction: Jukna TOC.pdf, chapter1.pdf, Chapter9.pdf, bool-V7.pdf; Kulikov et al. arXiv 2102.12579v3.
  Large files were keyword-scanned, only listed passages were read in full.
- Everything else: search snippets only.
- Red'kin's "4n-4" and "7n-7" statements were read in Jukna, not in Red'kin. The reading "NOT counted" is deduced
  from 4n-4 versus Schnorr's 3(n-1) AND/OR-only count in the same book.
