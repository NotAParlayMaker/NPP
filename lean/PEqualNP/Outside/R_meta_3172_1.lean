import Mathlib
import PEqualNP.Defs

-- Cut by the pair of wires the OR gate reads.
-- or23, or38, or28: the OR gate reads two different wires among x2, x3, x8.
-- same: the OR gate reads one wire twice, so wire 10 is a copy of it.
-- Each case is one forest of the size a single file can hold.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3172_1
  (or23 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++ [x 2 || x 3]) ≠
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
  (or38 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++ [x 3 || x 8]) ≠
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
  (or28 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++ [x 2 || x 8]) ≠
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
  (same : ∀ i : Fin 9, i = 2 ∨ i = 3 ∨ i = 8 → ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++ [x i]) ≠
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
  :
  ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro l hlen _ hmem C hfan hsize
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  have key : ∀ (x : Fin 9 → Bool) (i : Fin 9),
      (List.ofFn x ++ [!x 0]).getD i.val false = x i := by
    intro x i
    fin_cases i <;> rfl
  have conv : ∀ (i j : Fin 9) (y : Bool) (x : Fin 9 → Bool), (x i || x j) = y →
      PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (List.map (fun k : ℕ => (List.ofFn x ++ [!x 0]).getD k false) [i.val, j.val]) = y := by
    intro i j y x e
    simp only [List.map_cons, List.map_nil, key, PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.any_cons, List.any_nil, id, Bool.or_false]
    exact e
  have close : ∀ (i j : Fin 9) (o : (Fin 9 → Bool) → Bool), a = i.val → b = j.val →
      (∀ x, (x i || x j) = o x) →
      (∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++ [o x]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      ∃ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++
        [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (List.map (fun k : ℕ => (List.ofFn x ++ [!x 0]).getD k false) [a, b])]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro i j o ea eb eo ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [ea, eb, conv i j (o x) x (eo x)]
    exact hx
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact close 2 2 (fun x => x 2) rfl rfl (fun x => Bool.or_self _) (same 2 (by decide) C hfan hsize)
  · exact close 2 3 (fun x => x 2 || x 3) rfl rfl (fun x => rfl) (or23 C hfan hsize)
  · exact close 2 8 (fun x => x 2 || x 8) rfl rfl (fun x => rfl) (or28 C hfan hsize)
  · exact close 3 2 (fun x => x 2 || x 3) rfl rfl (fun x => Bool.or_comm _ _) (or23 C hfan hsize)
  · exact close 3 3 (fun x => x 3) rfl rfl (fun x => Bool.or_self _) (same 3 (by decide) C hfan hsize)
  · exact close 3 8 (fun x => x 3 || x 8) rfl rfl (fun x => rfl) (or38 C hfan hsize)
  · exact close 8 2 (fun x => x 2 || x 8) rfl rfl (fun x => Bool.or_comm _ _) (or28 C hfan hsize)
  · exact close 8 3 (fun x => x 3 || x 8) rfl rfl (fun x => Bool.or_comm _ _) (or38 C hfan hsize)
  · exact close 8 8 (fun x => x 8) rfl rfl (fun x => Bool.or_self _) (same 8 (by decide) C hfan hsize)
