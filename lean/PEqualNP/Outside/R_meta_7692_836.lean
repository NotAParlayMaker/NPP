import PEqualNP.Defs

-- Submitted via OpenAI Codex by gpt-6.2-astra.

open PEqualNP PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_7692_836
    (residual : ∃ D : Circuit, D.size ≤ 22 ∧ TopForm.IsAO2 14 D ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.output < 14 + D.size ∧ D.output ≠ 2 ∧
      ∀ x : Fin 14 → Bool,
        D.eval (List.ofFn (Function.update x 2 (x 8 || (x 9 || x 13)))) =
          decide (∃ i j : Fin 7, i ≠ 2 ∧ (i = j ∨ i = j + 1 ∨ i = j + 3) ∧
            x (Fin.castAdd 7 i) = true ∧ x (Fin.natAdd 7 j) = true))
    (splice : ∀ (D : Circuit) (p a b c : Fin 14),
      TopForm.IsAO2 14 D → (∀ g ∈ D.gates, g.inputs.Nodup) → D.output < 14 + D.size →
      D.output ≠ p.val → a ≠ b → b ≠ c → a ≠ c →
      ∃ (C : Circuit) (u v : ℕ), C.size ≤ D.size + 2 ∧ TopForm.IsAO2 14 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ u < 14 + C.size ∧ v < 14 + C.size ∧
        u ≠ p.val ∧ u ≠ v ∧ ∀ x : Fin 14 → Bool,
          let h := x a || (x b || x c)
          let w := BlindGate.wireValue C 14 x
          w u = D.eval (List.ofFn (Function.update x p h)) ∧ w v = h ∧ w p.val = x p) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ),   x1.size ≤ (24 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧         x2 < (14 : ℕ) + x1.size ∧           x3 < (14 : ℕ) + x1.size ∧             x2 ≠ (2 : ℕ) ∧               x2 ≠ x3 ∧                 ∀ (x4 : Fin (14 : ℕ) → Bool),                   have x5 : ℕ → Bool := PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x4;                   (x5 x2 || x5 (2 : ℕ) && x5 x3) = Decidable.decide (∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x7) = Bool.true) ∧ ∀ x6 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))], (x4 = fun (x8 : Fin (14 : ℕ)) => Decidable.decide (x8 = x6)) → x5 (2 : ℕ) = Bool.false ∧ x5 x3 = Bool.false := by
  obtain ⟨D, hs, hD, hn, ho, hne, hres⟩ := residual
  obtain ⟨C, u, v, hsz, hC, hnd, hu, hv, hup, huv, hw⟩ :=
    splice D 2 8 9 13 hD hn ho hne (by decide) (by decide) (by decide)
  refine ⟨C, u, v, by omega, hC, hnd, hu, hv, hup, huv, ?_⟩
  have row : ∀ j : Fin 7, ((2 : Fin 7) = j ∨ (2 : Fin 7) = j + 1 ∨ (2 : Fin 7) = j + 3) ↔
      j = 1 ∨ j = 2 ∨ j = 6 := by decide +kernel
  intro x
  obtain ⟨he, hh, hp⟩ := hw x
  change BlindGate.wireValue C 14 x u = _ at he
  change BlindGate.wireValue C 14 x v = (x 8 || (x 9 || x 13)) at hh
  change BlindGate.wireValue C 14 x 2 = x 2 at hp
  dsimp only
  constructor
  · rw [he, hh, hp, hres]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨i, j, _, h, hi, hj⟩ | ⟨hi, hj | hj | hj⟩)
      · exact ⟨i, j, h, hi, hj⟩
      · exact ⟨2, 1, (row 1).2 (by decide), hi, hj⟩
      · exact ⟨2, 2, (row 2).2 (by decide), hi, hj⟩
      · exact ⟨2, 6, (row 6).2 (by decide), hi, hj⟩
    · rintro ⟨i, j, h, hi, hj⟩
      by_cases h2 : i = 2
      · subst i
        right
        refine ⟨hi, ?_⟩
        rcases (row j).1 h with rfl | rfl | rfl
        · exact Or.inl hj
        · exact Or.inr (Or.inl hj)
        · exact Or.inr (Or.inr hj)
      · exact Or.inl ⟨i, j, h2, h, hi, hj⟩
  · rw [hh, hp]
    intro i hi hx
    subst x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> decide
