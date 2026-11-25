import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7686_aux

theorem key {α β : Type} [DecidableEq α] (E : α → β → Prop) [∀ a, DecidablePred (fun b => E a b)]
    [∀ b, DecidablePred (fun a => E a b)] (A : Finset α) (B : Finset β) (k : ℕ)
    (hC : ∀ a a' b b', E a b → E a b' → E a' b → E a' b' → a = a' ∨ b = b')
    (v : α) (hv : v ∈ A)
    (hA : ∀ a ∈ A, k < (B.filter (fun b => E a b)).card)
    (hB : ∀ b ∈ B, k < (A.filter (fun a => E a b)).card) : k * (k + 1) < A.card := by
  have hsub : (B.filter (fun b => E v b)).biUnion (fun b => (A.filter (fun a => E a b)).erase v)
      ⊆ A.erase v := by
    intro u hu
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_filter] at hu ⊢
    obtain ⟨b, -, hne, hA', -⟩ := hu
    exact ⟨hne, hA'⟩
  have hdisj : ∀ b ∈ B.filter (fun b => E v b), ∀ b' ∈ B.filter (fun b => E v b), b ≠ b' →
      Disjoint ((A.filter (fun a => E a b)).erase v) ((A.filter (fun a => E a b')).erase v) := by
    intro b hb b' hb' hne
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_erase, Finset.mem_filter] at hu hu' hb hb'
    rcases hC u v b b' hu.2.2 hu'.2.2 hb.2 hb'.2 with h | h
    · exact hu.1 h
    · exact hne h
  have hcard := Finset.card_biUnion
    (fun b hb b' hb' hne => hdisj b (Finset.mem_coe.mp hb) b' (Finset.mem_coe.mp hb') hne)
  have h1 := Finset.card_le_card hsub
  have h2 : ∀ b ∈ B.filter (fun b => E v b),
      k ≤ ((A.filter (fun a => E a b)).erase v).card := by
    intro b hb
    simp only [Finset.mem_filter] at hb
    have := hB b hb.1
    have hm : v ∈ A.filter (fun a => E a b) := by simp [hv, hb.2]
    rw [Finset.card_erase_of_mem hm]
    omega
  have h3 := Finset.card_nsmul_le_sum _ _ k h2
  have h4 := hA v hv
  have h5 := Finset.card_erase_of_mem hv
  have h6 : 0 < A.card := Finset.card_pos.mpr ⟨v, hv⟩
  rw [hcard] at h1
  simp only [smul_eq_mul] at h3
  have h7 : (k + 1) * k ≤ (B.filter (fun b => E v b)).card * k := Nat.mul_le_mul_right k h4
  have h8 : k * (k + 1) = (k + 1) * k := Nat.mul_comm _ _
  omega

end PEqualNP.Outside.L_meta_7686_aux

theorem PEqualNP.Outside.L_meta_7686 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)) (x4 x5 : Finset (Fin x1)), (∀ (x6 x7 x8 x9 : Fin x1), (x6, x8) ∈ x3 → (x6, x9) ∈ x3 → (x7, x8) ∈ x3 → (x7, x9) ∈ x3 → x6 = x7 ∨ x8 = x9) → x4.Nonempty → x5.Nonempty → (∀ x9 ∈ x4, x2 < {x11 ∈ x5 | (x9, x11) ∈ x3}.card) → (∀ x10 ∈ x5, x2 < {x12 ∈ x4 | (x12, x10) ∈ x3}.card) → x2 * (x2 + (1 : ℕ)) < x4.card ∧ x2 * (x2 + (1 : ℕ)) < x5.card ∧ (x2 + (1 : ℕ)) * (x2 * (x2 + (1 : ℕ)) + (1 : ℕ)) ≤ {x11 ∈ x3 | x11.1 ∈ x4 ∧ x11.2 ∈ x5}.card := by
  intro x1 x2 x3 x4 x5 hC h4 h5 hA hB
  obtain ⟨v, hv⟩ := h4
  obtain ⟨w, hw⟩ := h5
  have e1 := PEqualNP.Outside.L_meta_7686_aux.key (fun a b => (a, b) ∈ x3) x4 x5 x2
    (fun a a' b b' h1 h2 h3 h4 => hC a a' b b' h1 h2 h3 h4) v hv hA hB
  have e2 := PEqualNP.Outside.L_meta_7686_aux.key (fun b a => (a, b) ∈ x3) x5 x4 x2
    (fun b b' a a' h1 h2 h3 h4 => (hC a a' b b' h1 h3 h2 h4).symm) w hw hB hA
  refine ⟨e1, e2, ?_⟩
  have hfib : ∀ a ∈ x4, x2 + 1 ≤
      (Finset.filter (fun e => e.1 = a) {x11 ∈ x3 | x11.1 ∈ x4 ∧ x11.2 ∈ x5}).card := by
    intro a ha
    have hs : (Finset.filter (fun b => (a, b) ∈ x3) x5).image (fun b => (a, b)) ⊆
        Finset.filter (fun e => e.1 = a) {x11 ∈ x3 | x11.1 ∈ x4 ∧ x11.2 ∈ x5} := by
      intro e he
      simp only [Finset.mem_image, Finset.mem_filter] at he ⊢
      obtain ⟨b, ⟨hb1, hb2⟩, rfl⟩ := he
      exact ⟨⟨hb2, ha, hb1⟩, rfl⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ (fun b b' h => (Prod.mk.inj h).2)] at hc
    have := hA a ha
    omega
  have hsum := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := x4)
    (s := {x11 ∈ x3 | x11.1 ∈ x4 ∧ x11.2 ∈ x5})
    (fun e he => (Finset.mem_filter.mp he).2.1)
  have h3 := Finset.card_nsmul_le_sum x4 _ (x2 + 1) hfib
  simp only [smul_eq_mul] at h3
  rw [hsum]
  have h9 : (x2 * (x2 + 1) + 1) * (x2 + 1) ≤ x4.card * (x2 + 1) := Nat.mul_le_mul_right _ e1
  have h10 : (x2 + 1) * (x2 * (x2 + 1) + 1) = (x2 * (x2 + 1) + 1) * (x2 + 1) := Nat.mul_comm _ _
  omega
