import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta248

theorem closure (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ)
    (hsym : ∀ u v : Fin N, E u v → E v u)
    (hlab : ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N,
      (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧
        pos b = (pos v + 1) % (2 * k + 1))
    (L : ℕ) (c : ℕ → Fin N) (hL : 3 ≤ L) (hc : c L = c 0)
    (hE : ∀ i : ℕ, i < L → E (c i) (c (i + 1)))
    (hd : ∀ i j : ℕ, i < j → j < L → c i ≠ c j)
    (i : ℕ) (hi : i < L) (hp : pos (c i) ≠ 0) :
    (∃ j, j < L ∧ pos (c j) + 1 = pos (c i)) ∧
      (∃ j, j < L ∧ pos (c j) = (pos (c i) + 1) % (2 * k + 1)) := by
  obtain ⟨-, a, b, hab, ha, hb⟩ := hlab _ hp
  have hd' : ∀ i j : ℕ, i < L → j < L → i ≠ j → c i ≠ c j := by
    intro i j hi hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hd i j h hj
    · exact (hd j i h hi).symm
  obtain ⟨n, hn, hEn, hnne⟩ : ∃ n, n < L ∧ E (c i) (c n) ∧ (n = i + 1 ∨ (n = 0 ∧ i + 1 = L)) := by
    by_cases h : i + 1 = L
    · refine ⟨0, by omega, ?_, Or.inr ⟨rfl, h⟩⟩
      have := hE i hi
      rwa [h, hc] at this
    · exact ⟨i + 1, by omega, hE i hi, Or.inl rfl⟩
  obtain ⟨p, hp', hEp, hpne, hpn⟩ : ∃ p, p < L ∧ E (c i) (c p) ∧ p ≠ i ∧ p ≠ n := by
    by_cases h : i = 0
    · subst h
      refine ⟨L - 1, by omega, ?_, by omega, ?_⟩
      · have := hE (L - 1) (by omega)
        rw [show L - 1 + 1 = L by omega, hc] at this
        exact hsym _ _ this
      · omega
    · refine ⟨i - 1, by omega, ?_, by omega, ?_⟩
      · have := hE (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at this
        exact hsym _ _ this
      · omega
  have hcne : c n ≠ c p := hd' n p hn hp' (Ne.symm hpn)
  have hn2 := (hab _).1 hEn
  have hp2 := (hab _).1 hEp
  have hA : ∃ j, j < L ∧ c j = a := by
    rcases hn2 with h | h
    · exact ⟨n, hn, h⟩
    · rcases hp2 with h' | h'
      · exact ⟨p, hp', h'⟩
      · exact absurd (h.trans h'.symm) hcne
  have hB : ∃ j, j < L ∧ c j = b := by
    rcases hn2 with h | h
    · rcases hp2 with h' | h'
      · exact absurd (h.trans h'.symm) hcne
      · exact ⟨p, hp', h'⟩
    · exact ⟨n, hn, h⟩
  obtain ⟨ja, hja, hja'⟩ := hA
  obtain ⟨jb, hjb, hjb'⟩ := hB
  exact ⟨⟨ja, hja, by rw [hja']; exact ha⟩, ⟨jb, hjb, by rw [hjb']; exact hb⟩⟩

end PEqualNP.Outside.Meta248

open PEqualNP.Outside.Meta248 in
theorem PEqualNP.Outside.L_meta_248 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → ∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L → c L = c 0 → (∀ i : ℕ, i < L → E (c i) (c (i + 1))) → (∀ i j : ℕ, i < j → j < L → c i ≠ c j) → 2 * k + 1 ≤ L := by
  intro N k E pos _ ⟨hsym, hnz, hlab⟩ L c hL hc hE hd
  have cl := closure N k E pos hsym hlab L c hL hc hE hd
  obtain ⟨i0, hi0, hp0⟩ : ∃ i, i < L ∧ pos (c i) ≠ 0 := by
    rcases hnz _ _ (hE 0 (by omega)) with h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
  have hle := (hlab _ hp0).1
  have down : ∀ d, d ≤ pos (c i0) → ∃ j, j < L ∧ pos (c j) = pos (c i0) - d := by
    intro d
    induction d with
    | zero => intro _; exact ⟨i0, hi0, by simp⟩
    | succ d ih =>
      intro hd1
      obtain ⟨j, hj, hj'⟩ := ih (by omega)
      obtain ⟨⟨j2, hj2, hj2'⟩, -⟩ := cl j hj (by omega)
      exact ⟨j2, hj2, by omega⟩
  have up : ∀ d, pos (c i0) + d ≤ 2 * k → ∃ j, j < L ∧ pos (c j) = pos (c i0) + d := by
    intro d
    induction d with
    | zero => intro _; exact ⟨i0, hi0, by simp⟩
    | succ d ih =>
      intro hd1
      obtain ⟨j, hj, hj'⟩ := ih (by omega)
      obtain ⟨-, ⟨j2, hj2, hj2'⟩⟩ := cl j hj (by omega)
      refine ⟨j2, hj2, ?_⟩
      rw [hj2', hj', Nat.mod_eq_of_lt (by omega)]
      omega
  have hsub : Finset.range (2 * k + 1) ⊆ (Finset.range L).image (fun j => pos (c j)) := by
    intro q hq
    rw [Finset.mem_range] at hq
    rw [Finset.mem_image]
    by_cases hq' : q ≤ pos (c i0)
    · obtain ⟨j, hj, hj'⟩ := down (pos (c i0) - q) (by omega)
      exact ⟨j, Finset.mem_range.2 hj, by omega⟩
    · obtain ⟨j, hj, hj'⟩ := up (q - pos (c i0)) (by omega)
      exact ⟨j, Finset.mem_range.2 hj, by omega⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  exact this.trans (Finset.card_image_le.trans (by simp))
