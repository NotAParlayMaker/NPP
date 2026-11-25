import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6258

theorem num (d : ℕ) : 93 * d ≤ 2208 + d * d := by
  have h : (93 : ℤ) * d ≤ 2208 + d * d := by nlinarith [sq_nonneg (2 * (d : ℤ) - 93)]
  exact_mod_cast h

-- One side has at most 2208 vertices: count the ordered pairs of neighbours of each right vertex.
theorem half {n : ℕ} (E : Finset (Fin n × Fin n))
    (hC : ∀ a b c d : Fin n, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (b, c) ∈ E ∧ (a, d) ∈ E ∧ (b, d) ∈ E))
    (ha : (Finset.image Prod.fst E).card ≤ 2208) :
    E.card ≤ 24 * ((Finset.image Prod.fst E).card + (Finset.image Prod.snd E).card - 1) := by
  classical
  let P := Finset.image Prod.fst E
  let Q := Finset.image Prod.snd E
  let F : Fin n → Finset (Fin n × Fin n) := fun q => E.filter fun e => e.2 = q
  let N : Fin n → Finset (Fin n) := fun q => (F q).image Prod.fst
  have memN : ∀ q x, x ∈ N q ↔ (x, q) ∈ E := by
    intro q x
    constructor
    · intro h
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      rw [← he2]
      exact he1
    · intro h
      exact Finset.mem_image.mpr ⟨(x, q), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩
  have cardN : ∀ q, (N q).card = (F q).card := by
    intro q
    apply Finset.card_image_of_injOn
    intro e1 h1 e2 h2 h12
    have h1' := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have h2' := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    exact Prod.ext h12 (h1'.trans h2'.symm)
  have he : E.card = ∑ q ∈ Q, (F q).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he => Finset.mem_image_of_mem Prod.snd he)
  have hdisj : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → Disjoint ((N q).offDiag) ((N q').offDiag) := by
    intro q _ q' _ hne
    rw [Finset.disjoint_left]
    intro xy h1 h2
    rw [Finset.mem_offDiag] at h1 h2
    exact hC xy.1 xy.2 q q' h1.2.2 hne
      ⟨(memN q _).mp h1.1, (memN q _).mp h1.2.1, (memN q' _).mp h2.1, (memN q' _).mp h2.2.1⟩
  have hsub : (Q.biUnion fun q => (N q).offDiag) ⊆ P.offDiag := by
    intro xy h
    obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp h
    rw [Finset.mem_offDiag] at hq ⊢
    exact ⟨Finset.mem_image.mpr ⟨(xy.1, q), (memN q _).mp hq.1, rfl⟩,
      Finset.mem_image.mpr ⟨(xy.2, q), (memN q _).mp hq.2.1, rfl⟩, hq.2.2⟩
  have hoff : ∑ q ∈ Q, ((F q).card * (F q).card - (F q).card) ≤ P.card * P.card - P.card := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj, Finset.offDiag_card] at h1
    have h2 : ∀ q ∈ Q, ((N q).offDiag).card = (F q).card * (F q).card - (F q).card := by
      intro q _
      rw [Finset.offDiag_card, cardN q]
    rw [Finset.sum_congr rfl h2] at h1
    exact h1
  have hsum : ∑ q ∈ Q, 93 * (F q).card ≤
      ∑ q ∈ Q, (2208 + ((F q).card * (F q).card - (F q).card) + (F q).card) := by
    apply Finset.sum_le_sum
    intro q _
    have h1 := num (F q).card
    have h2 : (F q).card ≤ (F q).card * (F q).card := Nat.le_mul_self _
    omega
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    smul_eq_mul, ← he] at hsum
  show E.card ≤ 24 * (P.card + Q.card - 1)
  have ha' : P.card ≤ 2208 := ha
  by_cases h0 : P.card = 0
  · have hE : E = ∅ := by
      have : P = ∅ := Finset.card_eq_zero.mp h0
      exact Finset.image_eq_empty.mp this
    rw [hE]
    simp
  · have h3 : P.card * P.card - P.card ≤ 2208 * (P.card - 1) := by
      have := Nat.mul_le_mul_right (P.card - 1) ha'
      rw [Nat.mul_sub_one] at this
      exact this
    omega

theorem mem_swap {n : ℕ} (E : Finset (Fin n × Fin n)) (a b : Fin n) :
    (a, b) ∈ E.image Prod.swap ↔ (b, a) ∈ E := by
  constructor
  · intro h
    obtain ⟨e, he, hab⟩ := Finset.mem_image.mp h
    have : e = (b, a) := by
      rw [← Prod.swap_swap e, hab]; rfl
    rw [← this]; exact he
  · intro h
    exact Finset.mem_image.mpr ⟨(b, a), h, rfl⟩

end PEqualNP.Outside.L_meta_6258

theorem PEqualNP.Outside.L_meta_6258 : ∀ {x1 : ℕ} (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → (Finset.image Prod.fst x2).card ≤ (2208 : ℕ) ∨ (Finset.image Prod.snd x2).card ≤ (2208 : ℕ) → x2.card ≤ (24 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n E hC h
  rcases h with h | h
  · exact PEqualNP.Outside.L_meta_6258.half E hC h
  · have e1 : Finset.image Prod.fst (E.image Prod.swap) = Finset.image Prod.snd E := by
      rw [Finset.image_image]; rfl
    have e2 : Finset.image Prod.snd (E.image Prod.swap) = Finset.image Prod.fst E := by
      rw [Finset.image_image]; rfl
    have e3 : (E.image Prod.swap).card = E.card :=
      Finset.card_image_of_injective E Prod.swap_injective
    have := PEqualNP.Outside.L_meta_6258.half (E.image Prod.swap) (by
      intro a b c d hab hcd hh
      rw [PEqualNP.Outside.L_meta_6258.mem_swap, PEqualNP.Outside.L_meta_6258.mem_swap,
        PEqualNP.Outside.L_meta_6258.mem_swap, PEqualNP.Outside.L_meta_6258.mem_swap] at hh
      exact hC c d a b hcd hab ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2⟩) (by rw [e1]; exact h)
    rw [e1, e2, e3] at this
    omega
