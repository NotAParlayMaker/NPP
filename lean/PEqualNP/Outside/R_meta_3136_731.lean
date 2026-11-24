import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3136_731
    (normalize : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      gs.length = 13 → PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      ∃ ps : List (Fin 3 × Fin 25 × Fin 25), ps.length = 13 ∧
        ps.countP (fun p => decide (p.1.val = 2)) ≤ 1 ∧
        ∀ u : List Bool, u.length = 10 →
          ps.foldl (fun (w : List Bool) (p : Fin 3 × Fin 25 × Fin 25) =>
          let rd := fun (i : Fin 25) => if i.val = 24 then true else w.getD i.val false
          let a := rd p.2.1
          let b := rd p.2.2
          w ++ [if p.1.val = 0 then a && b else if p.1.val = 1 then a || b else !a]) u =
            (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires u)
    (obstruction : ∀ ps : List (Fin 3 × Fin 25 × Fin 25), ps.length = 13 →
      ps.countP (fun p => decide (p.1.val = 2)) ≤ 1 →
      ∀ a b : Fin 25, ∃ x : Fin 9 → Bool,
        let ws := ps.foldl (fun (w : List Bool) (p : Fin 3 × Fin 25 × Fin 25) =>
          let rd := fun (i : Fin 25) => if i.val = 24 then true else w.getD i.val false
          let a := rd p.2.1
          let b := rd p.2.2
          w ++ [if p.1.val = 0 then a && b else if p.1.val = 1 then a || b else !a]) (List.ofFn x ++ [x 0 || x 3])
        (ws.getD a.val false && ws.getD b.val false) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro gs a b hlen hf hc ha hb
  obtain ⟨ps, hp, hn, hs⟩ := normalize gs hlen hf hc
  obtain ⟨x, hx⟩ := obstruction ps hp hn ⟨a, by omega⟩ ⟨b, by omega⟩
  refine ⟨x, ?_⟩
  dsimp only at hx
  rw [hs _ (by simp)] at hx
  exact hx
