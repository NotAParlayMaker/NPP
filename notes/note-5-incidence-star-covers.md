# Note 5: star covers for the incidence gap, and why equality holds trivially

pequalnp.com, 2026-11-24. Measured, not machine-checked.

`L-meta-2581` is not an edge function but an incidence function: `I : Fin N -> Fin N -> Prop` with
`N = q^2+q+1`, each line holding `q+1` points and each pair of points on a unique line, and the circuit
decides whether the chosen point bits and line bits contain an incidence with both bits true.

`programs/starcover_2581.py` builds that plane from the field construction and checks the axioms before
measuring: line size `q+1`, every pair of points on exactly one line. A star at point `p` ANDs `z_p`
with the OR of its `q+1` line letters, costing `q+1` gates, and the `N` stars combine in `N-1` gates.

    q=2  N=7   21 incidences   star cover 27   statement bound N*q=14
    q=3  N=13  52 incidences   star cover 64   statement bound N*q=39

So for both computed orders the star cover already satisfies `N*q <= c * size` with `c = 1`. The
statement is not close to false on this family; refuting it requires a family of size `o(q^3)`, which is
a harder ask than the one-gate question for `L-meta-2191`, where `13` gates are explicitly reachable.

The script refuses non-prime `q`: the field construction needs a prime modulus, and `q=4` exits with a
message rather than a bogus plane.
