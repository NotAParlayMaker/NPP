import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_4284_1
    (seedUnread : ∀ (gs : List Gate) (a b : ℕ),
      gs.length = 13 → FanInTwo ⟨gs, 0⟩ →
      gs.countP (fun g => g.op.eval [false]) = 0 →
      (∀ g ∈ gs, 9 ∉ g.inputs) →
      10 ≤ a → a ≤ b → b < 23 →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && w.getD b false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5))
    (seedRead : ∀ (gs : List Gate) (a b : ℕ),
      gs.length = 13 → FanInTwo ⟨gs, 0⟩ →
      gs.countP (fun g => g.op.eval [false]) = 0 →
      (∃ g ∈ gs, 9 ∈ g.inputs) →
      10 ≤ a → a ≤ b → b < 23 →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && w.getD b false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 = (0 : ℕ) →         (10 : ℕ) ≤ x2 →           x2 ≤ x3 →             x3 < (23 : ℕ) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false && x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro gs a b hlen hfan hnot ha hab hb
  by_cases h : ∃ g ∈ gs, 9 ∈ g.inputs
  · exact seedRead gs a b hlen hfan hnot h ha hab hb
  · push_neg at h
    exact seedUnread gs a b hlen hfan hnot h ha hab hb
