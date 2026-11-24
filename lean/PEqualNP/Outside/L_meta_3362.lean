import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3362

theorem star {N : ℕ} (I : Fin N → Fin N → Prop)
    (huniq : ∀ (p q : Fin N), p ≠ q → ∃! l : Fin N, I p l ∧ I q l)
    (A B : Finset (Fin N)) (hAB : ∀ a ∈ A, ∀ b ∈ B, I a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra h
  simp only [not_or, not_le] at h
  obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨b1, hb1, b2, hb2, hneb⟩ := Finset.one_lt_card.mp h.2
  obtain ⟨l, _, hl⟩ := huniq a1 a2 hne
  have e1 := hl b1 ⟨hAB a1 ha1 b1 hb1, hAB a2 ha2 b1 hb1⟩
  have e2 := hl b2 ⟨hAB a1 ha1 b2 hb2, hAB a2 ha2 b2 hb2⟩
  exact hneb (e1.trans e2.symm)

theorem mul_le_add (a b : ℕ) (h : a ≤ 1 ∨ b ≤ 1) : a * b ≤ a + b := by
  rcases h with h | h
  · interval_cases a <;> omega
  · interval_cases b <;> omega

theorem count {N k : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcol : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = k) :
    (Finset.univ.filter (fun pl : Fin N × Fin N => I pl.1 pl.2)).card = N * k := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have : ∀ l : Fin N, (∑ p : Fin N, if I p l then 1 else 0) = k := by
    intro l
    rw [← Finset.card_filter, ← hcol l, Fintype.card_subtype]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PEqualNP.Outside.L_meta_3362

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro N k m I _ hcol huniq A B hAB hcov
  have hS := PEqualNP.Outside.L_meta_3362.count I hcol
  have hsub : (Finset.univ.filter (fun pl : Fin N × Fin N => I pl.1 pl.2)) ⊆
      Finset.univ.biUnion (fun i => A i ×ˢ B i) := by
    intro pl hpl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpl
    obtain ⟨i, h1, h2⟩ := hcov pl.1 pl.2 hpl
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product]
    exact ⟨i, h1, h2⟩
  calc N * k = _ := hS.symm
    _ ≤ (Finset.univ.biUnion (fun i => A i ×ˢ B i)).card := Finset.card_le_card hsub
    _ ≤ ∑ i, (A i ×ˢ B i).card := Finset.card_biUnion_le
    _ = ∑ i, (A i).card * (B i).card := by simp [Finset.card_product]
    _ ≤ ∑ i, ((A i).card + (B i).card) := by
      apply Finset.sum_le_sum
      intro i _
      exact PEqualNP.Outside.L_meta_3362.mul_le_add _ _
        (PEqualNP.Outside.L_meta_3362.star I huniq (A i) (B i) (hAB i))
