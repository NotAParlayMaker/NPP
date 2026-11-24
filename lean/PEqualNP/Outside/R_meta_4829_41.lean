import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The 22 inputs are precisely the high inputs where turning off vertex four destroys the edge.
theorem PEqualNP.Outside.R_meta_4829_41
    (extract : ∀ (C : Circuit) (k : Fin C.size), FanInTwo C → C.size ≤ 15 →
      (C.gates.get k).op ≠ .or → (∀ t : Fin C.size, 4 ∈ (C.gates.get t).inputs ↔ t=k) → circuitFun 9 C = (fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      ∃ (w : ℕ) (order : Bool), w ≠ 4 ∧ C.gates.get k = ⟨.and,if order then [w,4] else [4,w]⟩)
    (five : ∀ (C : Circuit) (k : Fin C.size) (w : ℕ) (order : Bool),
      (∀ t : Fin C.size, 4 ∈ (C.gates.get t).inputs ↔ t=k) → (C.gates.get k = ⟨.and,if order then [w,4] else [4,w]⟩) → w ≠ 4 → circuitFun 9 C = (fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) →
      9 ≤ w ∧ w < 9+k.val ∧ ∀ m ∈ ([17,21,24,25,26,56,58,81,85,88,89,120,145,152,153,154,209,216,217,273,277,401] : List ℕ), (⟨C.gates.take k.val,w⟩ : Circuit).eval (List.ofFn (fun i : Fin 9 => m.testBit i.val)) = true)
    (search : ∀ (C : Circuit) (k : Fin C.size) (w : ℕ) (order : Bool), FanInTwo C → C.size ≤ 15 →
      (∀ t : Fin C.size, 4 ∈ (C.gates.get t).inputs ↔ t=k) → (C.gates.get k = ⟨.and,if order then [w,4] else [4,w]⟩) → 9 ≤ w → w < 9+k.val → (∀ m ∈ ([17,21,24,25,26,56,58,81,85,88,89,120,145,152,153,154,209,216,217,273,277,401] : List ℕ), (⟨C.gates.take k.val,w⟩ : Circuit).eval (List.ofFn (fun i : Fin 9 => m.testBit i.val)) = true) →
      circuitFun 9 C ≠ (fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin x1.size), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (x1.gates.get x2).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (x6 : Fin x1.size), (4 : ℕ) ∈ (x1.gates.get x6).inputs ↔ x6 = x2) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) := by
  intro C k fan small nonOr sole good
  obtain ⟨w,order,other,gate⟩ := extract C k fan small nonOr sole good
  obtain ⟨lo,hi,traces⟩ := five C k w order sole gate other good
  exact search C k w order fan small sole gate lo hi traces good
