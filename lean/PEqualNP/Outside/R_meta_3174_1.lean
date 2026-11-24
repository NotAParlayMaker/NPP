import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3174_1
    (hPair : ∀ a : ℕ, a = (1 : ℕ) ∨ a = (5 : ℕ) →
  ∀ b : ℕ, b = (2 : ℕ) ∨ b = (3 : ℕ) ∨ b = (8 : ℕ) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (13 : ℕ) →
    ∃ x : Fin (9 : ℕ) → Bool,
      let x9 : List Bool := List.ofFn x ++ [!x (0 : Fin (9 : ℕ))];
      C.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (List.map (fun i : ℕ => x9.getD i Bool.false) [a, b])]) ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (hComm : ∀ a b : ℕ, ∀ x : Fin (9 : ℕ) → Bool,
      let x9 : List Bool := List.ofFn x ++ [!x (0 : Fin (9 : ℕ))];
      PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (List.map (fun i : ℕ => x9.getD i Bool.false) [a, b]) =
      PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (List.map (fun i : ℕ => x9.getD i Bool.false) [b, a])) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen hmem hcross C hfan hsize
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  have hsplit :
      ((a = (1 : ℕ) ∨ a = (5 : ℕ)) ∧
        (b = (2 : ℕ) ∨ b = (3 : ℕ) ∨ b = (8 : ℕ))) ∨
      ((b = (1 : ℕ) ∨ b = (5 : ℕ)) ∧
        (a = (2 : ℕ) ∨ a = (3 : ℕ) ∨ a = (8 : ℕ))) := by
    by_cases haA : a = (1 : ℕ) ∨ a = (5 : ℕ)
    · left
      refine ⟨haA, ?_⟩
      by_contra hbB
      apply hcross.1
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact haA
      · rcases hb with h | h | h | h | h
        · exact Or.inl h
        · exact False.elim (hbB (Or.inl h))
        · exact False.elim (hbB (Or.inr (Or.inl h)))
        · exact Or.inr h
        · exact False.elim (hbB (Or.inr (Or.inr h)))
    · right
      have haB : a = (2 : ℕ) ∨ a = (3 : ℕ) ∨ a = (8 : ℕ) := by
        rcases ha with h | h | h | h | h
        · exact False.elim (haA (Or.inl h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact False.elim (haA (Or.inr h))
        · exact Or.inr (Or.inr h)
      refine ⟨?_, haB⟩
      by_contra hbA
      apply hcross.2
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact haB
      · rcases hb with h | h | h | h | h
        · exact False.elim (hbA (Or.inl h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact False.elim (hbA (Or.inr h))
        · exact Or.inr (Or.inr h)
  rcases hsplit with h | h
  · obtain ⟨haA, hbB⟩ := h
    exact hPair a haA b hbB C hfan hsize
  · obtain ⟨hbA, haB⟩ := h
    simpa only [hComm a b] using hPair b hbA a haB C hfan hsize
