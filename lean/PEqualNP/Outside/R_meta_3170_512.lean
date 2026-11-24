import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3170_512
    (h1 : let all := 2^512-1
      let raw := fun i : Nat => all / (2^(2^i)+1) * 2^(2^i)
      let base := (List.range 9).map raw ++ [all ^^^ raw 0, raw 1 ||| raw 5, 0, all]
      let step := fun (ws : List Nat) (g : Fin 3 × Fin 26 × Fin 26) =>
        let a := ws.getD g.2.1.val 0
        let b := ws.getD g.2.2.val 0
        ws ++ [if g.1.val = 0 then a &&& b else if g.1.val = 1 then a ||| b else all ^^^ a]
      ∀ (u : List Nat) (c : PEqualNP.CircuitLowerBounds.Circuit),
        u.length = 2 → (∀ j ∈ u, j = 1 ∨ j = 5) → PEqualNP.MetaComplexity.FanInTwo c →
        c.size ≤ 13 → ∃ (gs : List (Fin 3 × Fin 26 × Fin 26)) (o : Fin 26),
          gs.length ≤ 13 ∧ ∀ r : Fin 512, let x : Fin 9 → Bool := fun j => r.val.testBit j.val
          let v := List.ofFn x ++ [!x 0]
          ((gs.foldl step base).getD o.val 0).testBit r.val =
            c.eval (v ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (u.map fun j => v.getD j false)]))
    (h2 : let all := 2^512-1
      let raw := fun i : Nat => all / (2^(2^i)+1) * 2^(2^i)
      let base := (List.range 9).map raw ++ [all ^^^ raw 0, raw 1 ||| raw 5, 0, all]
      let step := fun (ws : List Nat) (g : Fin 3 × Fin 26 × Fin 26) =>
        let a := ws.getD g.2.1.val 0
        let b := ws.getD g.2.2.val 0
        ws ++ [if g.1.val = 0 then a &&& b else if g.1.val = 1 then a ||| b else all ^^^ a]
      ∀ (gs : List (Fin 3 × Fin 26 × Fin 26)) (o : Fin 26),
        gs.length ≤ 13 → ∃ r : Fin 512,
        ((gs.foldl step base).getD o.val 0).testBit r.val ≠ (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : Nat).testBit r.val) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro u hu _ allowed c hf hs
  obtain ⟨g,o,hg,agree⟩ := h1 u c hu allowed hf hs
  obtain ⟨r,different⟩ := h2 g o hg
  let x : Fin 9 → Bool := fun j => r.val.testBit j.val
  refine ⟨x, ?_⟩
  have table : ∀ row : Fin 512, (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : Nat).testBit row.val =
      (let x : Fin 9 → Bool := fun j => row.val.testBit j.val; (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    decide +kernel
  change _ ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  rw [← agree r, ← table r]
  exact different
