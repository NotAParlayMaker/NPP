import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2509_271
    (cofactor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)) 12)
    (splice : ∀ (p t : Circuit) (i : ℕ), FanInTwo p → FanInTwo t →
      i < 8 + p.size →
      ∃ C : Circuit, FanInTwo C ∧ C.size = p.size + t.size ∧
        ∀ x : Fin 8 → Bool,
          let w := p.wires (List.ofFn x)
          C.eval (List.ofFn x) = t.eval (w ++ [w.getD i false]))
    (control : ∀ (p t : Circuit) (i : ℕ) (d : Bool), FanInTwo p → FanInTwo t →
      8 ≤ i → i < 8 + p.size →
      ∃ C : Circuit, FanInTwo C ∧ C.size = p.size + t.size + 1 ∧
        (∃ j k : ℕ, j < C.size ∧ 9 ≤ k ∧ k < 9 + j ∧
          C.gates[j]? = some ⟨if d then GateOp.or else GateOp.and, [8, k]⟩ ∧
          ∀ g ∈ C.gates.take j ++ C.gates.drop (j + 1), 8 ∉ g.inputs) ∧
        ∀ (x : Fin 8 → Bool) (b : Bool),
          let w := p.wires (List.ofFn x)
          C.eval (List.ofFn x ++ [b]) =
            t.eval (w ++ [if b = d then d else w.getD i false]))
    (exclude :
      let f := (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4))
      ∀ (C : Circuit) (j k : ℕ) (d : Bool), FanInTwo C → C.size = 14 →
        j < C.size → 9 ≤ k → k < 9 + j →
        C.gates[j]? = some ⟨if d then GateOp.or else GateOp.and, [8, k]⟩ →
        (∀ g ∈ C.gates.take j ++ C.gates.drop (j + 1), 8 ∉ g.inputs) →
        (∀ (x : Fin 8 → Bool) (b : Bool), C.eval (List.ofFn x ++ [b]) =
          if b = d then f x || x 0 || x 3 else f x) → False) :
    (have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         (8 : ℕ) ≤ x4 →           x4 < (8 : ℕ) + x2.size →             have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);             have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;             (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = !x5) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [x5]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ)))) := by
  let f := (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4))
  dsimp only
  intro p t i d hp ht hsize hi hlt _ hlo
  change ∀ x, t.eval (p.wires (List.ofFn x) ++ [(p.wires (List.ofFn x)).getD i false]) =
    f x at hlo
  by_contra! hhi
  change ∀ x, t.eval (p.wires (List.ofFn x) ++ [d]) = (f x || x 0 || x 3) at hhi
  by_cases h : p.size + t.size ≤ 12
  · obtain ⟨C, hC, hs, he⟩ := splice p t i hp ht hlt
    exact cofactor ⟨C, hC, by omega, fun x => (he x).trans (hlo x)⟩
  · obtain ⟨C, hC, hs, ⟨j, k, hj, hk, hjk, hg, hread⟩, he⟩ := control p t i d hp ht hi hlt
    apply exclude C j k d hC (by omega) hj hk hjk hg hread
    intro x b
    rw [he x b]
    split
    · exact hhi x
    · exact hlo x
