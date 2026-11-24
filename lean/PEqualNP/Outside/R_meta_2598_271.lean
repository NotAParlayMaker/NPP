import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Encode gates using three operators and bounded wire addresses. Address 29 is
-- the permanent false wire. A one-input AND or OR may read its operand twice.
-- The second child ranges solely over finite types, so an exact synthesis
-- solver may tackle it without choosing bounds on lists or wire addresses.
theorem PEqualNP.Outside.R_meta_2598_271
    (encode : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      ∃ (k : Fin 19) (ops : Fin k.val → Fin 3 × Fin 30 × Fin 30) (o : Fin 30),
      ∀ y : List Bool, y.length = 11 →
        (Circuit.mk (List.ofFn fun i =>
          let t := ops i
          Gate.mk (if t.1 = 0 then .and else if t.1 = 1 then .or else .not)
            [t.2.1.val, t.2.2.val]) o.val).eval y = C.eval y)
    (exhaust : ∀ (k : Fin 19) (ops : Fin k.val → Fin 3 × Fin 30 × Fin 30) (o : Fin 30),
      ∃ x : Fin 10 → Bool,
        (Circuit.mk (List.ofFn fun i =>
          let t := ops i
          Gate.mk (if t.1 = 0 then .and else if t.1 = 1 then .or else .not)
            [t.2.1.val, t.2.2.val]) o.val).eval (List.ofFn x ++ [!x 0]) ≠
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hC hs
  obtain ⟨k, ops, o, equal⟩ := encode C hC hs
  obtain ⟨x, different⟩ := exhaust k ops o
  refine ⟨x, fun hx => different ?_⟩
  rw [equal _ (by simp), hx]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  rfl
