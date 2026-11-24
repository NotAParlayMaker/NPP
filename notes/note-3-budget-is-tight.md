# Note 3: `L-meta-2191`'s budget sits exactly on the star-cover cost

pequalnp.com, 2026-11-24. Computed, not machine-checked.

The gap fixes the ten-edge function of the graph `01 12 23 04 15 26 37 46 57 74` on vertices `0..7`,
and asks whether two circuits with `size(x3c) + size(x4c) <= 13` can perform the wire substitution it
describes.

The star cover of that function costs **exactly 13 gates**, attained only by the cover `{1,2,4,7}`
(degree sum 12, two internal edges, three combining ORs). Since `x4c` needs at least one gate, a
refutation by star cover would need the function in 12, so the budget is one gate below the cheapest
construction this family offers. A two-gate substitution model was checked and fails on exactly that
size, not on its logic.

Question: is 13 the exact size of this ten-edge function, or does a cheaper circuit exist? At 13 the
gap is tight; at 12 it falls.
