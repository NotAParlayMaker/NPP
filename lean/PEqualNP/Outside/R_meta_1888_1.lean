import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reduce the wired Petersen case to its bijective core.
-- The wiring map x2 sends circuit input wires to graph coordinates.
-- When x2 misses a coordinate, that coordinate reaches the circuit only through the hint wire
-- (the OR of coordinates zero and two), and pairs of inputs differing only there refute any
-- circuit: with a hidden coordinate outside the pair, the singletons on a hidden edge refute;
-- when only zero is hidden the pair (zero two four, two four) refutes, its hint reads true on
-- both halves since two is true, and the function differs on the edge four zero; when only two
-- is hidden the pair (zero two three, zero three) refutes, the hint reads true through zero and
-- the function differs on the edge two three. On Fin 10 a surjective wiring is bijective, so
-- the only hard case is a bijective wiring.
theorem PEqualNP.Outside.R_meta_1888_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), FanInTwo x1 → x1.size ≤ 18 → Function.Surjective x2 → ∃ (x5 : Fin 10 → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 0 || x5 2]) ≠ (fun (x6 : Fin 10 → Bool) => (x6 (0) && x6 (1) || (x6 (1) && x6 (2) || (x6 (2) && x6 (3) || (x6 (3) && x6 (4) || (x6 (4) && x6 (0) || (x6 (0) && x6 (5) || (x6 (1) && x6 (6) || (x6 (2) && x6 (7) || (x6 (3) && x6 (8) || (x6 (4) && x6 (9) || (x6 (5) && x6 (7) || (x6 (7) && x6 (9) || (x6 (9) && x6 (6) || (x6 (6) && x6 (8) || x6 (8) && x6 (5)))))))))))))))) x5) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), FanInTwo x1 → x1.size ≤ 18 → ¬ Function.Surjective x2 → ∃ (x5 : Fin 10 → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 0 || x5 2]) ≠ (fun (x6 : Fin 10 → Bool) => (x6 (0) && x6 (1) || (x6 (1) && x6 (2) || (x6 (2) && x6 (3) || (x6 (3) && x6 (4) || (x6 (4) && x6 (0) || (x6 (0) && x6 (5) || (x6 (1) && x6 (6) || (x6 (2) && x6 (7) || (x6 (3) && x6 (8) || (x6 (4) && x6 (9) || (x6 (5) && x6 (7) || (x6 (7) && x6 (9) || (x6 (9) && x6 (6) || (x6 (6) && x6 (8) || x6 (8) && x6 (5)))))))))))))))) x5) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => (x6 (0) && x6 (1) || (x6 (1) && x6 (2) || (x6 (2) && x6 (3) || (x6 (3) && x6 (4) || (x6 (4) && x6 (0) || (x6 (0) && x6 (5) || (x6 (1) && x6 (6) || (x6 (2) && x6 (7) || (x6 (3) && x6 (8) || (x6 (4) && x6 (9) || (x6 (5) && x6 (7) || (x6 (7) && x6 (9) || (x6 (9) && x6 (6) || (x6 (6) && x6 (8) || x6 (8) && x6 (5)))))))))))))))) x5 := by
  intro surjCase nonsurjCase x1 x2 hFan hSz
  rcases Classical.em (Function.Surjective x2) with hSurj | hNsurj
  · exact surjCase x1 x2 hFan hSz hSurj
  · exact nonsurjCase x1 x2 hFan hSz hNsurj
