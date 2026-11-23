import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1462 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (X B : Finset (Fin n))
    (r : Fin n → Fin n → Prop) (f : Fin m → Fin n),
    (∀ a b : Fin n, r a b → ¬ r b a) →
    (∀ i : Fin m, ¬ S i ⊆ X → f i ∈ B ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ B, r (f i) y) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S i = {p}) ∧
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j,
        ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, ((if s ∈ X then ({s} : Finset (Fin n)) else {s, f j}) ∩ S i).Nonempty))) := by
  intro n m S X B r f hr hf
  refine ⟨?_, ?_⟩
  · intro i p hp
    by_cases hx : p ∈ X
    · rw [ite_eq_left hx]
      ext q
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro h; subst h; exact ⟨rfl, hp⟩
    · rw [ite_eq_right hx]
      have hsub : ¬ S i ⊆ X := fun h => hx (h hp)
      have h2 := (hf i hsub).2.1
      ext q
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h | h, hq⟩
        · exact h
        · subst h; exact absurd hq h2
      · intro h; subst h; exact ⟨Or.inl rfl, hp⟩
  · intro i j _ ⟨⟨p, hp, hpn⟩, ⟨s, hs, hsn⟩⟩
    rw [Finset.mem_sdiff] at hp hs
    obtain ⟨q, hq⟩ := hpn
    obtain ⟨t, ht⟩ := hsn
    have hpX : p ∉ X := by
      intro hx
      rw [ite_eq_left hx, Finset.mem_inter, Finset.mem_singleton] at hq
      obtain ⟨h1, h2⟩ := hq
      subst h1; exact hp.2 h2
    have hsX : s ∉ X := by
      intro hx
      rw [ite_eq_left hx, Finset.mem_inter, Finset.mem_singleton] at ht
      obtain ⟨h1, h2⟩ := ht
      subst h1; exact hs.2 h2
    rw [ite_eq_right hpX, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq
    rw [ite_eq_right hsX, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at ht
    have hfi : f i ∈ S j := by
      obtain ⟨h1 | h1, h2⟩ := hq
      · subst h1; exact absurd h2 hp.2
      · subst h1; exact h2
    have hfj : f j ∈ S i := by
      obtain ⟨h1 | h1, h2⟩ := ht
      · subst h1; exact absurd h2 hs.2
      · subst h1; exact h2
    have Ai := hf i (fun h => hpX (h hp.1))
    have Aj := hf j (fun h => hsX (h hs.1))
    have r1 : r (f i) (f j) := Ai.2.2 (f j) (Finset.mem_inter.2 ⟨hfj, Aj.1⟩)
    have r2 : r (f j) (f i) := Aj.2.2 (f i) (Finset.mem_inter.2 ⟨hfi, Ai.1⟩)
    exact hr _ _ r1 r2
