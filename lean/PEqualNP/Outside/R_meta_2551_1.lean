import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2551_1
    (minor :
      let f (x : Fin 9 → Bool) := ([1,12,23,4,34,5,16,27,57,38,58,68] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
      ∀ D : Circuit, Monotone2 D →
        (∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = f (Fin.insertNth 4 false x)) →
        13 ≤ D.size)
    (contract :
      let f (x : Fin 9 → Bool) := ([1,12,23,4,34,5,16,27,57,38,58,68] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
      ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4]) = f x) →
        (2 ≤ C.gates.countP (fun g => g.inputs.contains 4) ∨
          ∃ g ∈ C.gates, g.op = GateOp.and ∧ (4 : ℕ) ∈ g.inputs) →
        ∃ D : Circuit, Monotone2 D ∧ D.size + 2 ≤ C.size ∧
          ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = f (Fin.insertNth 4 false x))
    (few :
      let f (x : Fin 9 → Bool) := ([1,12,23,4,34,5,16,27,57,38,58,68] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
      ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4]) = f x) →
        C.gates.countP (fun g => g.inputs.contains 4) ≤ 1 →
        (∀ g ∈ C.gates, (4 : ℕ) ∈ g.inputs → g.op = GateOp.or) →
        15 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ))]) = (fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) x3) → (15 : ℕ) ≤ x1.size := by
  intro C mono eval
  have ruled : (2 ≤ C.gates.countP (fun g => g.inputs.contains 4) ∨
      ∃ g ∈ C.gates, g.op = GateOp.and ∧ (4 : ℕ) ∈ g.inputs) → 15 ≤ C.size := by
    intro readership
    obtain ⟨D, monoD, cost, evalD⟩ := contract C mono eval readership
    have lower := minor D monoD evalD
    omega
  by_cases many : 2 ≤ C.gates.countP (fun g => g.inputs.contains 4)
  · exact ruled (Or.inl many)
  by_cases andReader : ∃ g ∈ C.gates, g.op = GateOp.and ∧ (4 : ℕ) ∈ g.inputs
  · exact ruled (Or.inr andReader)
  refine few C mono eval (by omega) ?_
  intro g hg read4
  have kind : g.op = GateOp.and ∨ g.op = GateOp.or := (mono g hg).1
  exact kind.resolve_left (fun isAnd => andReader ⟨g, hg, isAnd, read4⟩)
