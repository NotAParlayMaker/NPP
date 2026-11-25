import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3576_317
    (hIso : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)),
      (∀ a b : Fin n, G.Adj a b → side a ≠ side b) →
      (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      3 ≤ k →
      (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) →
      (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) →
      (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) →
      (∀ j : Fin k, (I j).card + 2 ≤ n) →
      (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) →
      G.edgeFinset.Nonempty →
      (∃ v : Fin n, G.degree v = 0) →
      ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card))
    (hLeaf : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)),
      (∀ a b : Fin n, G.Adj a b → side a ≠ side b) →
      (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      3 ≤ k →
      (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) →
      (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) →
      (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) →
      (∀ j : Fin k, (I j).card + 2 ≤ n) →
      (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) →
      (∀ v : Fin n, 1 ≤ G.degree v) →
      (∃ v : Fin n, G.degree v = 1) →
      ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card))
    (hCore : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)),
      (∀ a b : Fin n, G.Adj a b → side a ≠ side b) →
      (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      3 ≤ k →
      (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) →
      (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) →
      (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) →
      (∀ j : Fin k, (I j).card + 2 ≤ n) →
      (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) →
      (∀ v : Fin n, 2 ≤ G.degree v) →
      ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) :
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card) := by
  intro n k G _ side I hbip hc4 hk2 hind hcov hmiss hsz hne
  by_cases hk3 : 3 ≤ k
  · by_cases hedge : G.edgeFinset.Nonempty
    · by_cases hiso : ∃ v : Fin n, G.degree v = 0
      · exact hIso n k G side I hbip hc4 hk3 hind hcov hmiss hsz hne hedge hiso
      · have hdeg1 : ∀ v : Fin n, 1 ≤ G.degree v := by
          intro v
          have hv : G.degree v ≠ 0 := fun h0 => hiso ⟨v, h0⟩
          omega
        by_cases hleaf : ∃ v : Fin n, G.degree v = 1
        · exact hLeaf n k G side I hbip hc4 hk3 hind hcov hmiss hsz hne hdeg1 hleaf
        · have hdeg2 : ∀ v : Fin n, 2 ≤ G.degree v := by
            intro v
            have h1 := hdeg1 v
            have hne1 : G.degree v ≠ 1 := fun h => hleaf ⟨v, h⟩
            omega
          exact hCore n k G side I hbip hc4 hk3 hind hcov hmiss hsz hne hdeg2
    · refine ⟨∅, ?_, ?_⟩
      · intro a b hab
        exact False.elim (hedge ⟨s(a, b), G.mem_edgeFinset.mpr hab⟩)
      · have hemp : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hedge
        rw [hemp, Finset.card_empty, Finset.card_empty]
        have hsum : ∑ _ : Fin k, 2 ≤ ∑ j : Fin k, (n - (I j).card) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have := hsz j
          omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
        omega
  · exfalso
    have hk_eq : k = 2 := by omega
    subst hk_eq
    have hcomp0 : 2 ≤ (I ⟨0, by omega⟩)ᶜ.card := by
      have h1 := hsz ⟨0, by omega⟩
      have h2 := Finset.card_compl (I ⟨0, by omega⟩)
      simp only [Fintype.card_fin] at h2
      omega
    have hcomp1 : 2 ≤ (I ⟨1, by omega⟩)ᶜ.card := by
      have h1 := hsz ⟨1, by omega⟩
      have h2 := Finset.card_compl (I ⟨1, by omega⟩)
      simp only [Fintype.card_fin] at h2
      omega
    obtain ⟨b1, hb1, b2, hb2, hbne⟩ := Finset.one_lt_card.mp (by omega : 1 < (I ⟨0, by omega⟩)ᶜ.card)
    obtain ⟨a1, ha1, a2, ha2, hane⟩ := Finset.one_lt_card.mp (by omega : 1 < (I ⟨1, by omega⟩)ᶜ.card)
    rw [Finset.mem_compl] at hb1 hb2 ha1 ha2
    have hfin2 : ∀ j : Fin 2, j = ⟨0, by omega⟩ ∨ j = ⟨1, by omega⟩ := by
      intro j
      by_cases h0 : j.val = 0
      · left; exact Fin.ext h0
      · right; exact Fin.ext (by change j.val = 1; have := j.isLt; omega)
    have hmem0 : ∀ v, v ∉ I ⟨1, by omega⟩ → v ∈ I ⟨0, by omega⟩ := by
      intro v hv
      obtain ⟨j, hj⟩ := hcov v
      cases hfin2 j with
      | inl h => exact h ▸ hj
      | inr h => exact False.elim (hv (h ▸ hj))
    have hadj : ∀ a b, a ∉ I ⟨1, by omega⟩ → b ∉ I ⟨0, by omega⟩ → G.Adj a b := by
      intro a b ha hb
      have ha0 : a ∈ I ⟨0, by omega⟩ := hmem0 a ha
      have habne : a ≠ b := fun e => hb (e ▸ ha0)
      by_contra hna
      obtain ⟨j, hja, hjb⟩ := hne a b habne hna
      cases hfin2 j with
      | inl h => exact hb (h ▸ hjb)
      | inr h => exact ha (h ▸ hja)
    exact hc4 a1 b1 a2 b2 hane hbne
      ⟨hadj a1 b1 ha1 hb1, (hadj a2 b1 ha2 hb1).symm, hadj a2 b2 ha2 hb2, (hadj a1 b2 ha1 hb2).symm⟩
