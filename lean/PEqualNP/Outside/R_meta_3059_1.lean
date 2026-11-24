import PEqualNP.Defs

-- The target is the edge function of the graph on inputs 0 to 7, with inputs 0 and 3 joined to
-- it by OR. Fixing inputs 0 and 3 to false leaves the edge function of a cycle of length six on
-- the other six inputs. The cut separates the three parts of the count: the gates that read
-- the constant wire compute a constant or a copy and can all be dropped (constant); some gate
-- reads input 0 and some gate reads input 3, and fixing both to false drops two gates
-- (pinned); and the six-cycle needs eight gates (core; a SAT run finds no circuit of seven).
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3059_1
    (core : ¬ HasCircuitSize 6 (fun z : Fin 6 → Bool => (z 0 && z 1) || (z 0 && z 3) || (z 1 && z 4) || (z 2 && z 4) || (z 3 && z 5) || (z 5 && z 2)) 7)
    (pinned : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4) || x 0 || x 3)) →
      HasCircuitSize 6 (fun z : Fin 6 → Bool => (z 0 && z 1) || (z 0 && z 3) || (z 1 && z 4) || (z 2 && z 4) || (z 3 && z 5) || (z 5 && z 2)) (C.size - 2))
    (constant : ∀ (p t : Circuit) (b : Bool), FanInTwo p → FanInTwo t →
      (∀ x : Fin 8 → Bool, t.eval (p.wires (List.ofFn x) ++ [b]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4) || x 0 || x 3)) →
      ∃ R : Circuit, FanInTwo R ∧
        R.size + t.gates.countP (fun g : Gate => (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + p.size)) ≤ p.size + t.size ∧
        ∀ x : Fin 8 → Bool, R.eval (List.ofFn x) = t.eval (p.wires (List.ofFn x) ++ [b])) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x7 : Fin (8 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [x4]) = (x1 x7 || x7 (0 : Fin (8 : ℕ)) || x7 (3 : Fin (8 : ℕ)))) → (10 : ℕ) + List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (if x8.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains ((8 : ℕ) + x2.size)) x3.gates ≤ x2.size + x3.size := by
  dsimp only
  intro p t b hp ht he
  obtain ⟨R, hR, hs, hRe⟩ := constant p t b hp ht he
  obtain ⟨S, hS, hSs, hSe⟩ := pinned R hR (fun x => (hRe x).trans (he x))
  have big : ¬ S.size ≤ 7 := fun h => core ⟨S, hS, h, hSe⟩
  omega
