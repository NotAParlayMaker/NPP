import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2891_1
  (h1 :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size = (0 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (1 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))))
  (h2 :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[(0 : ℕ)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (1 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))))
  (h3 :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[(0 : ℕ)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (1 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))))
  (h4 :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ (∃ g : PEqualNP.CircuitLowerBounds.Gate, x1.gates[(0 : ℕ)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (1 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)))) :
  ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (1 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))) := by
  rintro ⟨x1, hfan, hsz, heval⟩
  rcases Nat.eq_zero_or_pos x1.gates.length with h0 | hpos
  · exact h1 ⟨x1, hfan, h0, heval⟩
  · obtain ⟨g, hg⟩ : ∃ g, x1.gates[(0 : ℕ)]? = Option.some g :=
      ⟨x1.gates[(0 : ℕ)], getElem?_pos x1.gates 0 hpos⟩
    have hmem := (hfan g (List.mem_of_getElem? hg)).1
    cases hop : g.op
    · exact h2 ⟨x1, hfan, hsz, ⟨g, hg, hop⟩, heval⟩
    · exact h3 ⟨x1, hfan, hsz, ⟨g, hg, hop⟩, heval⟩
    · exact h4 ⟨x1, hfan, hsz, ⟨g, hg, hop⟩, heval⟩
    · rw [hop] at hmem; simp at hmem
    · rw [hop] at hmem; simp at hmem
