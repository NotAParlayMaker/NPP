import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3174_1
    (near1 : ∀ (p : ℕ), (p = (2 : ℕ) ∨ p = (3 : ℕ) ∨ p = (8 : ℕ)) →
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x5 →
          x5.size ≤ (13 : ℕ) →
            ∃ (x8 : Fin (9 : ℕ) → Bool),
              have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];
              x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) [(1 : ℕ), p])]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))))
    (near5 : ∀ (p : ℕ), (p = (2 : ℕ) ∨ p = (3 : ℕ) ∨ p = (8 : ℕ)) →
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x5 →
          x5.size ≤ (13 : ℕ) →
            ∃ (x8 : Fin (9 : ℕ) → Bool),
              have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];
              x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) [(5 : ℕ), p])]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen hmem hmix x5 hC hs
  obtain ⟨hn, hf⟩ := hmix
  rcases x1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hlen
  · simp at hlen
  rotate_left
  · simp at hlen
  · have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    have swap : ∀ (g : ℕ → Bool),
        PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map g [b, a]) =
        PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map g [a, b]) := by
      intro g
      show (g b || (g a || false)) = (g a || (g b || false))
      cases g a <;> cases g b <;> rfl
    have key : ((a = 1 ∨ a = 5) ∧ (b = 2 ∨ b = 3 ∨ b = 8)) ∨
        ((b = 1 ∨ b = 5) ∧ (a = 2 ∨ a = 3 ∨ a = 8)) := by
      rcases ha with ha | ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb | hb <;>
        subst ha hb <;> simp at hn hf ⊢
    rcases key with ⟨ha | ha, hb⟩ | ⟨hb | hb, ha⟩
    · subst ha; exact near1 b hb x5 hC hs
    · subst ha; exact near5 b hb x5 hC hs
    · subst hb
      obtain ⟨x8, hx⟩ := near1 a ha x5 hC hs
      exact ⟨x8, by simpa only [swap] using hx⟩
    · subst hb
      obtain ⟨x8, hx⟩ := near5 a ha x5 hC hs
      exact ⟨x8, by simpa only [swap] using hx⟩
