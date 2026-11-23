import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1464 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    3 ≤ (S i0).card → (∀ i : Fin m, i ≠ i0 → (S i ∩ S i0).card ≤ 1) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, i ≠ i0 → f i ∈ S i0 ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ S i0, r (f i) y := by
  intro n m S i0 h3 h1
  obtain ⟨p1, m1, p2, m2, p3, m3, h12, h13, h23⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < (S i0).card)
  refine ⟨fun a b => (a = p2 ∧ b = p1) ∨ (a = p3 ∧ b = p2) ∨ (a = p1 ∧ b ≠ p1 ∧ b ≠ p2),
    fun i => if p1 ∈ S i then p2 else if p2 ∈ S i then p3 else p1, ?_, ?_⟩
  · intro a b hab hba
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hb1, hb2⟩ <;>
      rcases hba with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h', h''⟩ <;> aesop
  · intro i hi
    have hle := Finset.card_le_one.mp (h1 i hi)
    by_cases ha : p1 ∈ S i
    · beta_reduce
      rw [if_pos ha]
      have n2 : p2 ∉ S i := fun h =>
        h12 (hle p1 (Finset.mem_inter.mpr ⟨ha, m1⟩) p2 (Finset.mem_inter.mpr ⟨h, m2⟩))
      refine ⟨m2, n2, fun y hy => Or.inl ⟨rfl, hle y hy p1 (Finset.mem_inter.mpr ⟨ha, m1⟩)⟩⟩
    · by_cases hb : p2 ∈ S i
      · beta_reduce
        rw [if_neg ha, if_pos hb]
        have n3 : p3 ∉ S i := fun h =>
          h23 (hle p2 (Finset.mem_inter.mpr ⟨hb, m2⟩) p3 (Finset.mem_inter.mpr ⟨h, m3⟩))
        refine ⟨m3, n3, fun y hy => Or.inr (Or.inl ⟨rfl, hle y hy p2 (Finset.mem_inter.mpr ⟨hb, m2⟩)⟩)⟩
      · beta_reduce
        rw [if_neg ha, if_neg hb]
        refine ⟨m1, ha, fun y hy => Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)⟩
        · rintro rfl
          exact ha (Finset.mem_inter.mp hy).1
        · rintro rfl
          exact hb (Finset.mem_inter.mp hy).1
