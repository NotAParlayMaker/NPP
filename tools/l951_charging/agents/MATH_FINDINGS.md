# Math subagent findings (Sonnet, 2026-11-23 ~14:58 CST), reviewed by the opus-951 thread

Proved:
- The charging lemma (excess <= #zero-merge) is EQUIVALENT to L-meta-951, via size = Σ(|S|-1) - excess + Z.
- A purely local charging argument cannot work: fake_config_t.py builds a configuration (8 inputs; sets {c,1,2},{c,3,4},{c',1,5},{c',3,6},{1,3}; h = x1∨x3) that passes the invariant and per-set-count scaffold checks with excess 2 > Z 1, but does NOT compute the outputs. Any proof must use output correctness.
- Lemma B (kill points): if g merges S and g(e_v)=1 for some v ∉ S, every path from g to o_S contains a gate taking the e_v value 1 -> 0; it is an AND or the NOT, never a merge, so it lies in Z.
- Lemma A, FIXED by the opus thread: run each set's union-find only over the cone of its output o_S. The per-set count stays |S|-1 and every merge then lies in the output cone. (The unrestricted version is false: a merge outside the cone can preempt one inside.)

Open: injectivity of a kill-point charge (one AND such as (g1∨g2)∧N may be the kill point of several double merges; the NOT may be the only killer of many).
