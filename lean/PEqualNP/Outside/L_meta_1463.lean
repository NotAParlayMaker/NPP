import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1463_aux

def P (c x : Fin 7) : Prop := x - c = 1 ∨ x - c = 2 ∨ x - c = 4

instance (c x : Fin 7) : Decidable (P c x) := by unfold P; infer_instance

theorem P_anti : ∀ a b : Fin 7, P a b → ¬ P b a := by decide

theorem P_dom : ∀ a b : Fin 7, ∃ c, c ≠ a ∧ c ≠ b ∧ P c a ∧ P c b := by decide

theorem two_pts {n : ℕ} (s A : Finset (Fin n)) (hs : s ⊆ A) (hA : A.Nonempty)
    (h : s.card ≤ 2) : ∃ p ∈ A, ∃ q ∈ A, s ⊆ {p, q} := by
  obtain ⟨z, hz⟩ := hA
  interval_cases hc : s.card
  · rw [Finset.card_eq_zero] at hc
    exact ⟨z, hz, z, hz, by simp [hc]⟩
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
    exact ⟨p, hs (by simp), p, hs (by simp), by simp⟩
  · obtain ⟨p, q, _, rfl⟩ := Finset.card_eq_two.mp hc
    exact ⟨p, hs (by simp), q, hs (by simp), le_refl _⟩

end PEqualNP.Outside.L_meta_1463_aux

open PEqualNP.Outside.L_meta_1463_aux in
theorem PEqualNP.Outside.L_meta_1463 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ A ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ A, r (f i) y := by
  intro n m S A hA hS
  have hne : A.Nonempty := by
    rw [← Finset.card_pos, hA]; norm_num
  let e : A ≃ Fin 7 := Fintype.equivFinOfCardEq (by simp [hA])
  let r : Fin n → Fin n → Prop := fun a b =>
    ∃ ha : a ∈ A, ∃ hb : b ∈ A, P (e ⟨a, ha⟩) (e ⟨b, hb⟩)
  have H : ∀ i, ∃ x, x ∈ A ∧ x ∉ S i ∧ ∀ y ∈ S i ∩ A, r x y := by
    intro i
    obtain ⟨p, hp, q, hq, hsub⟩ := two_pts (S i ∩ A) A Finset.inter_subset_right hne (hS i)
    obtain ⟨c, hcp, hcq, hPp, hPq⟩ := P_dom (e ⟨p, hp⟩) (e ⟨q, hq⟩)
    have hfA : (e.symm c).1 ∈ A := (e.symm c).2
    have hec : e ⟨(e.symm c).1, hfA⟩ = c := by simp
    refine ⟨(e.symm c).1, hfA, ?_, ?_⟩
    · intro hmem
      have h2 := hsub (Finset.mem_inter.mpr ⟨hmem, hfA⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2
      rcases h2 with h2 | h2
      · apply hcp
        rw [← hec]; congr 2
      · apply hcq
        rw [← hec]; congr 2
    · intro y hy
      have h2 := hsub hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2
      refine ⟨hfA, (Finset.mem_inter.mp hy).2, ?_⟩
      rw [hec]
      rcases h2 with rfl | rfl
      · exact hPp
      · exact hPq
  choose f hf using H
  refine ⟨r, f, ?_, hf⟩
  rintro a b ⟨ha, hb, h1⟩ ⟨ha', hb', h2⟩
  exact P_anti _ _ h1 h2
