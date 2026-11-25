import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7645_aux

theorem fin_part : ∀ a b : Fin 14, (14 : ℕ) * ↑a + ↑b ∈ [(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] → ∃ x5 ∈ [(129 : ℕ), (257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)], (fun (x6 : Fin 14) => x5.testBit ↑x6) = (fun i => (i == a || i == b)) := by
  decide

end PEqualNP.Outside.L_meta_7645_aux

theorem PEqualNP.Outside.L_meta_7645 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), (14 : ℕ) * ↑x2 + ↑x3 ∈ [(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∀ (x2 : Fin (14 : ℕ) → Bool), x1 x2 → (∀ x4 ≤ x2, x1 x4 → x4 = x2) → ∃ x5 ∈ [(129 : ℕ), (257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)], (fun (x6 : Fin (14 : ℕ)) => x5.testBit ↑x6) = x2 := by
  intro x1 x2 hx2 hmin
  obtain ⟨a, b, hk, ha, hb⟩ := hx2
  have hle : (fun i => (i == a || i == b)) ≤ x2 := by
    intro i
    by_cases h1 : i = a
    · subst h1; simp [ha]
    · by_cases h2 : i = b
      · subst h2; simp [hb]
      · have h3 : (i == a || i == b) = false := by simp [h1, h2]
        show (i == a || i == b) ≤ x2 i
        rw [h3]; exact Bool.false_le _
  have he : x1 (fun i => (i == a || i == b)) := ⟨a, b, hk, by simp, by simp⟩
  have := hmin _ hle he
  subst this
  exact PEqualNP.Outside.L_meta_7645_aux.fin_part a b hk
