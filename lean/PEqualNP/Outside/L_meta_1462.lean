import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1462

lemma row_hit {n m : ℕ} (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) (f : Fin m → Fin n)
    (i j : Fin m) (p : Fin n) (hp : p ∈ S i) (hpj : p ∉ S j)
    (h : ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty) :
    ¬ S i ⊆ X ∧ f i ∈ S j := by
  obtain ⟨y, hy⟩ := h
  rw [Finset.mem_inter] at hy
  obtain ⟨hy1, hy2⟩ := hy
  split_ifs at hy1 with hpX
  · rw [Finset.mem_singleton] at hy1
    rw [hy1] at hy2
    exact (hpj hy2).elim
  · rw [Finset.mem_insert, Finset.mem_singleton] at hy1
    refine ⟨fun hsub => hpX (hsub hp), ?_⟩
    rcases hy1 with h1 | h1
    · rw [h1] at hy2
      exact (hpj hy2).elim
    · rw [h1] at hy2
      exact hy2

lemma row_own {n m : ℕ} (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) (f : Fin m → Fin n)
    (i : Fin m) (p : Fin n) (hp : p ∈ S i) (hfi : ¬ S i ⊆ X → f i ∉ S i) :
    (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S i = {p} := by
  split_ifs with hpX
  · exact Finset.singleton_inter_of_mem hp
  · have hnot : f i ∉ S i := hfi (fun hsub => hpX (hsub hp))
    ext y
    rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
    constructor
    · rintro ⟨h1 | h1, hy⟩
      · exact h1
      · rw [h1] at hy
        exact (hnot hy).elim
    · intro h1
      rw [h1]
      exact ⟨Or.inl rfl, hp⟩

end PEqualNP.Outside.L_meta_1462

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
  constructor
  · intro i p hp
    exact PEqualNP.Outside.L_meta_1462.row_own S X f i p hp (fun hnot => (hf i hnot).2.1)
  · rintro i j _ ⟨⟨p, hp, hpn⟩, ⟨s, hs, hsn⟩⟩
    rw [Finset.mem_sdiff] at hp hs
    obtain ⟨hi1, hi2⟩ := PEqualNP.Outside.L_meta_1462.row_hit S X f i j p hp.1 hp.2 hpn
    obtain ⟨hj1, hj2⟩ := PEqualNP.Outside.L_meta_1462.row_hit S X f j i s hs.1 hs.2 hsn
    have ha := hf i hi1
    have hb := hf j hj1
    exact hr _ _ (ha.2.2 (f j) (Finset.mem_inter.mpr ⟨hj2, hb.1⟩))
      (hb.2.2 (f i) (Finset.mem_inter.mpr ⟨hi2, ha.1⟩))
