import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2303_417
    (deleteShadow :
      ∀ (n j r : ℕ) (C : Circuit) (T : Set (List Bool)),
        FanInTwo C → j < C.size → (r < n+j ∨ n+C.size ≤ r) →
        (∀ x ∈ T, x.length = n) →
        (∀ x ∈ T, (C.wires x).getD (n+j) false = (C.wires x).getD r false) →
        ∃ D : Circuit, FanInTwo D ∧ D.size < C.size ∧ ∀ x ∈ T, D.eval x = C.eval x)
    (bound :
      let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
        (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let diag (x : Fin 9 → Bool) := List.ofFn x ++ [x 0]
      ∀ C : Circuit, FanInTwo C → C.size = 14 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) = f x) →
        (∀ j < C.size, ∀ r, r < 10+j ∨ 24 ≤ r → ∃ x : Fin 9 → Bool,
          (C.wires (diag x)).getD (10+j) false ≠ (C.wires (diag x)).getD r false) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x4 (0 : Fin (9 : ℕ)) = Bool.true ∨ x4 (6 : Fin (9 : ℕ)) = Bool.false → x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → (∀ (x7 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))]) = x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ))])) → (14 : ℕ) ≤ x5.size) → ∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.false ∧ x6 (6 : Fin (9 : ℕ)) = Bool.true ∧ x1.eval (List.ofFn x6 ++ [Bool.true]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C fan size good minimal
  by_contra! no
  let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let diag (x : Fin 9 → Bool) := List.ofFn x ++ [x 0]
  have full (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 6]) = f x := by
    cases h0 : x 0 <;> cases h6 : x 6
    · simpa [f,h0,h6,Bool.or_assoc] using good x (Or.inr h6)
    · simpa [f,h0,h6,Bool.or_assoc] using no x h0 h6
    · simpa [f,h0,h6,Bool.or_assoc] using good x (Or.inl h0)
    · simpa [f,h0,h6,Bool.or_assoc] using good x (Or.inl h0)
  apply bound C fan size full
  intro j hj r hr
  by_contra! equal
  let T := Set.range diag
  have lengths : ∀ x ∈ T, (x : List Bool).length = 10 := by
    rintro _ ⟨x,rfl⟩
    simp [diag]
  have agree : ∀ x ∈ T, (C.wires x).getD (10+j) false = (C.wires x).getD r false := by
    rintro _ ⟨x,rfl⟩
    exact equal x
  have valid : r < 10+j ∨ 10+C.size ≤ r := by simpa [size] using hr
  obtain ⟨D,fanD,small,same⟩ := deleteShadow 10 j r C T fan hj valid lengths agree
  have large := minimal D fanD (fun x => same (diag x) ⟨x,rfl⟩)
  omega
