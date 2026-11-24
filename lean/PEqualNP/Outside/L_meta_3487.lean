import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3487

-- The first coordinates joined to the second coordinate c.
def nb {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) (c : β) : Finset α :=
  (E.filter (fun p => p.2 = c)).image Prod.fst

lemma mem_nb {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) (c : β) (a : α) :
    a ∈ nb E c ↔ (a, c) ∈ E := by
  unfold nb
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a', c'⟩, ⟨h1, h2⟩, h3⟩
    simp only at h2 h3
    subst h2
    subst h3
    exact h1
  · intro h
    exact ⟨(a, c), ⟨h, rfl⟩, rfl⟩

lemma card_fiber {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) (c : β) :
    (E.filter (fun p => p.2 = c)).card = (nb E c).card := by
  unfold nb
  symm
  apply Finset.card_image_of_injOn
  intro p hp q hq hpq
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
  exact Prod.ext hpq (hp.2.trans hq.2.symm)

-- The tangent line of d * (d - 1) at d = 87, 88.
lemma tangent (d : ℕ) : 174 * d ≤ d * d - d + 7656 := by
  have h : d ≤ d * d := Nat.le_mul_self d
  rcases le_or_gt d 87 with h1 | h1
  · have h2 : 174 * d + d ≤ d * d + 7656 := by nlinarith [Nat.mul_le_mul (Nat.sub_le 87 d) (Nat.sub_le 88 d), mul_nonneg (Nat.zero_le (87 - d)) (Nat.zero_le (88 - d)), Nat.sub_add_cancel h1, Nat.sub_add_cancel (Nat.le_succ_of_le h1)]
    omega
  · have h2 : 174 * d + d ≤ d * d + 7656 := by nlinarith [mul_nonneg (Nat.zero_le (d - 88)) (Nat.zero_le (d - 87)), Nat.sub_add_cancel h1, Nat.sub_add_cancel (Nat.le_of_lt h1)]
    omega

lemma key {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (hC : ∀ (a a' : α) (b b' : β), a ≠ a' → b ≠ b' →
      ¬((a, b) ∈ E ∧ (a', b) ∈ E ∧ (a, b') ∈ E ∧ (a', b') ∈ E))
    (hm : (E.image Prod.fst).card ≤ 7656) :
    E.card ≤ 44 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
  set R := E.image Prod.fst with hR
  set S := E.image Prod.snd with hS
  have hsub : ∀ c, nb E c ⊆ R := by
    intro c a ha
    rw [mem_nb] at ha
    exact Finset.mem_image.mpr ⟨(a, c), ha, rfl⟩
  have h1 : E.card = ∑ c ∈ S, (nb E c).card := by
    rw [Finset.card_eq_sum_card_image Prod.snd E]
    apply Finset.sum_congr rfl
    intro c _
    exact card_fiber E c
  have hdisj : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → Disjoint (nb E c).offDiag (nb E c').offDiag := by
    intro c _ c' _ hcc
    rw [Finset.disjoint_left]
    rintro ⟨a, a'⟩ h h'
    rw [Finset.mem_offDiag] at h h'
    obtain ⟨ha, ha', hne⟩ := h
    obtain ⟨hb, hb', _⟩ := h'
    rw [mem_nb] at ha ha' hb hb'
    exact hC a a' c c' hne hcc ⟨ha, ha', hb, hb'⟩
  have h2 : ∑ c ∈ S, ((nb E c).card * (nb E c).card - (nb E c).card) ≤ R.card * R.card - R.card := by
    have e1 : ∑ c ∈ S, ((nb E c).card * (nb E c).card - (nb E c).card) =
        (S.biUnion fun c => (nb E c).offDiag).card := by
      rw [Finset.card_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.offDiag_card]
    rw [e1, ← Finset.offDiag_card]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨c, _, hp⟩ := hp
    rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨hsub c hp.1, hsub c hp.2.1, hp.2.2⟩
  have h3 : 174 * E.card ≤ (R.card * R.card - R.card) + 7656 * S.card := by
    calc 174 * E.card = ∑ c ∈ S, 174 * (nb E c).card := by rw [h1, Finset.mul_sum]
      _ ≤ ∑ c ∈ S, ((nb E c).card * (nb E c).card - (nb E c).card + 7656) :=
          Finset.sum_le_sum fun c _ => tangent _
      _ = ∑ c ∈ S, ((nb E c).card * (nb E c).card - (nb E c).card) + 7656 * S.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ (R.card * R.card - R.card) + 7656 * S.card := Nat.add_le_add_right h2 _
  rcases Nat.eq_zero_or_pos R.card with h0 | hpos
  · have hE : E = ∅ := by
      have : R = ∅ := Finset.card_eq_zero.mp h0
      exact Finset.image_eq_empty.mp this
    rw [hE]
    simp
  · have h4 : R.card * R.card - R.card ≤ 7656 * (R.card - 1) := by
      have : R.card * R.card - R.card = R.card * (R.card - 1) := by
        rw [Nat.mul_sub, Nat.mul_one]
      rw [this]
      exact Nat.mul_le_mul_right _ hm
    omega

lemma keySwap {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (hC : ∀ (a a' : α) (b b' : β), a ≠ a' → b ≠ b' →
      ¬((a, b) ∈ E ∧ (a', b) ∈ E ∧ (a, b') ∈ E ∧ (a', b') ∈ E))
    (hm : (E.image Prod.snd).card ≤ 7656) :
    E.card ≤ 44 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
  have hmem : ∀ (b : β) (a : α), (b, a) ∈ E.image Prod.swap ↔ (a, b) ∈ E := by
    intro b a
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨a', b'⟩, h, h'⟩
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact h
    · intro h
      exact ⟨(a, b), h, rfl⟩
  have hf : (E.image Prod.swap).image Prod.fst = E.image Prod.snd := by
    rw [Finset.image_image]
    rfl
  have hs : (E.image Prod.swap).image Prod.snd = E.image Prod.fst := by
    rw [Finset.image_image]
    rfl
  have hc : (E.image Prod.swap).card = E.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have := key (E.image Prod.swap) (by
    intro b b' a a' hb ha h
    rw [hmem, hmem, hmem, hmem] at h
    exact hC a a' b b' ha hb ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩) (by rw [hf]; exact hm)
  rw [hf, hs, hc] at this
  omega

end PEqualNP.Outside.L_meta_3487

theorem PEqualNP.Outside.L_meta_3487 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n E hC hmin
  rcases min_le_iff.mp hmin with h | h
  · exact PEqualNP.Outside.L_meta_3487.key E hC h
  · exact PEqualNP.Outside.L_meta_3487.keySwap E hC h
