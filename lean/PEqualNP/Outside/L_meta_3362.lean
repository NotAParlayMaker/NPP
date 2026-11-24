import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3362

theorem prod_le {N : ℕ} (I : Fin N → Fin N → Prop) (S T : Finset (Fin N))
    (h : ∀ p ∈ S, ∀ l ∈ T, I p l)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) :
    S.card * T.card ≤ S.card + T.card := by
  by_cases hS : S.card ≤ 1
  · calc S.card * T.card ≤ 1 * T.card := Nat.mul_le_mul_right _ hS
      _ ≤ S.card + T.card := by omega
  · have hT : T.card ≤ 1 := by
      by_contra hT
      obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
      obtain ⟨l1, hl1, l2, hl2, hnel⟩ := Finset.one_lt_card.1 (by omega : 1 < T.card)
      obtain ⟨l, _, hu⟩ := huniq p1 p2 hne
      have e1 := hu l1 ⟨h p1 hp1 l1 hl1, h p2 hp2 l1 hl1⟩
      have e2 := hu l2 ⟨h p1 hp1 l2 hl2, h p2 hp2 l2 hl2⟩
      exact hnel (e1.trans e2.symm)
    calc S.card * T.card ≤ S.card * 1 := Nat.mul_le_mul_left _ hT
      _ ≤ S.card + T.card := by omega

end PEqualNP.Outside.L_meta_3362

open PEqualNP.Outside.L_meta_3362 in
theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro N k m I _ hdeg huniq S T hbic hcov
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun pl => I pl.1 pl.2)
  have hE : E.card = N * k := by
    have h1 : E.card = ∑ pl : Fin N × Fin N, if I pl.1 pl.2 then 1 else 0 := by
      simp only [E, Finset.card_filter]
    rw [h1, Fintype.sum_prod_type, Finset.sum_comm]
    have h2 : ∀ l : Fin N, (∑ p : Fin N, if I p l then 1 else 0) = k := by
      intro l
      rw [← Finset.card_filter, ← hdeg l, Fintype.card_subtype]
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsub : E ⊆ Finset.univ.biUnion (fun i => S i ×ˢ T i) := by
    intro pl hpl
    have hI : I pl.1 pl.2 := (Finset.mem_filter.1 hpl).2
    obtain ⟨i, h1, h2⟩ := hcov pl.1 pl.2 hI
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_product.2 ⟨h1, h2⟩⟩
  calc N * k = E.card := hE.symm
    _ ≤ (Finset.univ.biUnion (fun i => S i ×ˢ T i)).card := Finset.card_le_card hsub
    _ ≤ ∑ i, (S i ×ˢ T i).card := Finset.card_biUnion_le
    _ = ∑ i, (S i).card * (T i).card := by simp [Finset.card_product]
    _ ≤ ∑ i, ((S i).card + (T i).card) :=
        Finset.sum_le_sum (fun i _ => prod_le I (S i) (T i) (hbic i) huniq)
