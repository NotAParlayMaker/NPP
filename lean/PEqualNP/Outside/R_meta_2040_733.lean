import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2040_733
    (decompose :
      let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      let reads := fun g : Gate =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any
          (fun i => i == 4 || i == 9)
      let input := fun (b : Bool) (x : Fin 8 → Bool) =>
        [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7, !b]
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → D.gates.countP reads ≤ 1 →
        (∀ x : Fin 8 → Bool, D.eval (input false x) = lo x) →
        (∀ x : Fin 8 → Bool, D.eval (input true x) = (lo x || x 0 || x 3)) →
        ∃ (p t : Circuit) (i : ℕ) (d : Bool), FanInTwo p ∧ FanInTwo t ∧
          p.size + t.size ≤ 13 ∧ 8 ≤ i ∧ i < 8 + p.size ∧
          (∀ x : Fin 8 → Bool, lo x = false → (x 0 || x 3) = true →
            (p.wires (List.ofFn x)).getD i false = !d) ∧
          (∀ x : Fin 8 → Bool, t.eval (p.wires (List.ofFn x) ++ [(p.wires (List.ofFn x)).getD i false]) = lo x) ∧
          (∀ x : Fin 8 → Bool, t.eval (p.wires (List.ofFn x) ++ [d]) = (lo x || x 0 || x 3)))
    (exclude :
      let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (p t : Circuit) (i : ℕ) (d : Bool), FanInTwo p → FanInTwo t →
        p.size + t.size ≤ 13 → 8 ≤ i → i < 8 + p.size →
        let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
        let u := fun x : Fin 8 → Bool => (w x).getD i false
        (∀ x, lo x = false → (x 0 || x 3) = true → u x = !d) →
        (∀ x, t.eval (w x ++ [u x]) = lo x) →
        ∃ x, t.eval (w x ++ [d]) ≠ (lo x || x 0 || x 3)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (0 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x2, x3 (4 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (6 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), !x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  let lo := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let input := fun (b : Bool) (x : Fin 8 → Bool) =>
    [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7, !b]
  dsimp only
  intro D fan size readers low
  by_contra! high
  change ∀ x, D.eval (input false x) = lo x at low
  change ∀ x, D.eval (input true x) = (lo x || x 0 || x 3) at high
  obtain ⟨p, t, i, d, fp, ft, bound, lo8, hi, sens, a, b⟩ :=
    decompose D fan size readers low high
  obtain ⟨x, bad⟩ := exclude p t i d fp ft bound lo8 hi sens a
  exact bad (b x)
