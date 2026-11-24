import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3576_1 (h1 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), 0 < n → (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → (∀ v : Fin n, G.degree v ≤ 7) → G.edgeFinset.card + 1 ≤ ∑ v : Fin n, max 1 ((Finset.univ.filter (fun j => v ∉ I j)).card - 1)) (h2 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), 0 < n → (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → (∃ v : Fin n, 8 ≤ G.degree v) → G.edgeFinset.card + 1 ≤ ∑ v : Fin n, max 1 ((Finset.univ.filter (fun j => v ∉ I j)).card - 1)) :
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card) := by
  intro n k G _ side I hbip hC4 hk hind hin hout hsize hpair
  have hn : 0 < n := by
    have := hsize ⟨0, by omega⟩
    omega
  have hk3 : 3 ≤ k := by
    by_contra hlt
    obtain rfl : k = 2 := by omega
    have two_out : ∀ j : Fin 2, ∃ a b : Fin n, a ≠ b ∧ a ∉ I j ∧ b ∉ I j := by
      intro j
      have hc : 1 < ((I j)ᶜ).card := by
        rw [Finset.card_compl, Fintype.card_fin]
        have := hsize j
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
      exact ⟨a, b, hab, Finset.mem_compl.mp ha, Finset.mem_compl.mp hb⟩
    have f2 : ∀ j : Fin 2, j = 0 ∨ j = 1 := by
      intro j
      fin_cases j <;> simp
    have adj : ∀ a b : Fin n, a ∉ I 0 → b ∉ I 1 → G.Adj a b := by
      intro a b ha hb
      by_contra hn'
      have hab : a ≠ b := by
        rintro rfl
        obtain ⟨j, hj⟩ := hin a
        rcases f2 j with rfl | rfl
        · exact ha hj
        · exact hb hj
      obtain ⟨j, hja, hjb⟩ := hpair a b hab hn'
      rcases f2 j with rfl | rfl
      · exact ha hja
      · exact hb hjb
    obtain ⟨a, c, hac, ha, hc⟩ := two_out 0
    obtain ⟨b, d, hbd, hb, hd⟩ := two_out 1
    exact hC4 a b c d hac hbd ⟨adj a b ha hb, (adj c b hc hb).symm, adj c d hc hd, (adj a d ha hd).symm⟩
  set c : Fin n → ℕ := fun v => (Finset.univ.filter (fun j => v ∉ I j)).card with hcdef
  have hc1 : ∀ v, 1 ≤ c v := by
    intro v
    obtain ⟨j, hj⟩ := hout v
    exact Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  set T : Finset (Fin n) := Finset.univ.filter (fun v => 2 ≤ c v) with hT
  have hcover : ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T := by
    intro a b hab
    by_contra hno
    push Not at hno
    have ha : c a ≤ 1 := by
      have := hno.1
      simp [hT] at this
      omega
    have hb : c b ≤ 1 := by
      have := hno.2
      simp [hT] at this
      omega
    have hsub : (Finset.univ : Finset (Fin k)) ⊆ (Finset.univ.filter (fun j => a ∉ I j)) ∪ (Finset.univ.filter (fun j => b ∉ I j)) := by
      intro j _
      by_cases hja : a ∈ I j
      · have : b ∉ I j := fun hjb => hind j a hja b hjb hab
        simp [this]
      · simp [hja]
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have : k ≤ c a + c b := this
    omega
  have hsum : ∑ j : Fin k, (n - (I j).card) = ∑ v : Fin n, c v := by
    have e1 : ∀ j : Fin k, n - (I j).card = ∑ v : Fin n, (if v ∉ I j then 1 else 0) := by
      intro j
      rw [Finset.sum_boole, Nat.cast_id]
      have : (Finset.univ.filter (fun v => v ∉ I j)) = (I j)ᶜ := by
        ext v; simp
      rw [this, Finset.card_compl, Fintype.card_fin]
    simp_rw [e1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_boole, Nat.cast_id]
  have hsplit : ∑ v : Fin n, c v = ∑ v : Fin n, max 1 (c v - 1) + T.card := by
    rw [hT, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    have := hc1 v
    split_ifs with h <;> omega
  have hS : G.edgeFinset.card + 1 ≤ ∑ v : Fin n, max 1 (c v - 1) := by
    by_cases hdeg : ∀ v : Fin n, G.degree v ≤ 7
    · exact h1 n k G side I hn hbip hC4 hind hin hout hpair hdeg
    · push Not at hdeg
      obtain ⟨v, hv⟩ := hdeg
      exact h2 n k G side I hn hbip hC4 hind hin hout hpair ⟨v, by omega⟩
  refine ⟨T, hcover, ?_⟩
  rw [hsum, hsplit]
  omega
