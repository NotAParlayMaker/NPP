import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1464 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    3 ≤ (S i0).card → (∀ i : Fin m, i ≠ i0 → (S i ∩ S i0).card ≤ 1) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, i ≠ i0 → f i ∈ S i0 ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ S i0, r (f i) y := by
  intro n m S i0 h3 hS
  classical
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (Nat.lt_of_succ_le h3)
  have key : ∃ g : Fin n → Fin n, (∀ y, g y ∈ S i0) ∧ (∀ y, g y ≠ y) ∧ ∀ x y, x = g y → ¬ y = g x := by
    refine ⟨fun y => if y = a then b else if y = b then c else a, ?_, ?_, ?_⟩
    · intro y
      show (if y = a then b else if y = b then c else a) ∈ S i0
      by_cases h1 : y = a
      · rw [if_pos h1]; exact hb
      · by_cases h2 : y = b
        · rw [if_neg h1, if_pos h2]; exact hc
        · rw [if_neg h1, if_neg h2]; exact ha
    · intro y
      show (if y = a then b else if y = b then c else a) ≠ y
      intro hy
      by_cases h1 : y = a
      · rw [if_pos h1] at hy; exact hab (h1.symm.trans hy.symm)
      · by_cases h2 : y = b
        · rw [if_neg h1, if_pos h2] at hy
          exact hbc (h2.symm.trans hy.symm)
        · rw [if_neg h1, if_neg h2] at hy; exact h1 hy.symm
    · intro x y hx hy
      have hx' : x = if y = a then b else if y = b then c else a := hx
      have hy' : y = if x = a then b else if x = b then c else a := hy
      by_cases h1 : y = a
      · rw [if_pos h1] at hx'
        rw [hx', if_neg hab.symm, if_pos rfl] at hy'
        exact hac (h1.symm.trans hy')
      · by_cases h2 : y = b
        · rw [if_neg h1, if_pos h2] at hx'
          rw [hx', if_neg hac.symm, if_neg hbc.symm] at hy'
          exact hab (hy'.symm.trans h2)
        · rw [if_neg h1, if_neg h2] at hx'
          rw [hx', if_pos rfl] at hy'
          exact h2 hy'
  obtain ⟨g, hgS, hgne, hanti⟩ := key
  refine ⟨fun x y => x = g y, fun i => if h : (S i ∩ S i0).Nonempty then g h.choose else a, hanti, ?_⟩
  intro i hi
  have h1 := Finset.card_le_one.mp (hS i hi)
  by_cases h : (S i ∩ S i0).Nonempty
  · have hy := h.choose_spec
    have hf : (if h : (S i ∩ S i0).Nonempty then g h.choose else a) = g h.choose := dif_pos h
    refine ⟨?_, ?_, ?_⟩
    · show (if h : (S i ∩ S i0).Nonempty then g h.choose else a) ∈ S i0
      rw [hf]; exact hgS _
    · show (if h : (S i ∩ S i0).Nonempty then g h.choose else a) ∉ S i
      rw [hf]
      intro hin
      exact hgne _ (h1 _ (Finset.mem_inter.mpr ⟨hin, hgS _⟩) _ hy)
    · intro y hy'
      show (if h : (S i ∩ S i0).Nonempty then g h.choose else a) = g y
      rw [hf, h1 y hy' _ hy]
  · have hf : (if h : (S i ∩ S i0).Nonempty then g h.choose else a) = a := dif_neg h
    refine ⟨?_, ?_, ?_⟩
    · show (if h : (S i ∩ S i0).Nonempty then g h.choose else a) ∈ S i0
      rw [hf]; exact ha
    · show (if h : (S i ∩ S i0).Nonempty then g h.choose else a) ∉ S i
      rw [hf]
      intro hin
      exact h ⟨a, Finset.mem_inter.mpr ⟨hin, ha⟩⟩
    · intro y hy'
      exact absurd ⟨y, hy'⟩ h
