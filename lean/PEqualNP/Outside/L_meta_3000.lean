import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3000 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ x9 ∉ x7, ∃ (x11 : Fin x2), x3 x11 x9 ∧ ∀ x12 ∈ x7, ¬x3 x11 x12 := by
  intro q n inc _ hcard huniq S hS l hl
  set A : Finset (Fin n) := Finset.univ.filter (fun p => inc p l) with hAdef
  have hA : A.card = q + 1 := by
    rw [hAdef, ← Fintype.card_subtype]
    exact hcard l
  set B : Finset (Fin n) := Finset.univ.filter (fun p => inc p l ∧ ∃ l' ∈ S, inc p l') with hBdef
  have hBsub : B ⊆ S.biUnion (fun l' => Finset.univ.filter (fun p => inc p l ∧ inc p l')) := by
    intro p hp
    simp only [hBdef, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hpl, l', hl'S, hpl'⟩ := hp
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l', hl'S, hpl, hpl'⟩
  have hpiece : ∀ l' ∈ S, (Finset.univ.filter (fun p => inc p l ∧ inc p l')).card ≤ 1 := by
    intro l' hl'
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    have hne : l' ≠ l := by
      intro h
      subst h
      exact hl hl'
    obtain ⟨m, hm, huniq'⟩ := huniq a b hab
    have h1 : l = m := huniq' l ⟨ha.1, hb.1⟩
    have h2 : l' = m := huniq' l' ⟨ha.2, hb.2⟩
    exact hne (h2.trans h1.symm)
  have hBcard : B.card ≤ q := by
    calc B.card ≤ (S.biUnion (fun l' => Finset.univ.filter (fun p => inc p l ∧ inc p l'))).card :=
          Finset.card_le_card hBsub
      _ ≤ ∑ l' ∈ S, (Finset.univ.filter (fun p => inc p l ∧ inc p l')).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ l' ∈ S, (1 : ℕ) := Finset.sum_le_sum (fun l' hl' => hpiece l' hl')
      _ = S.card := by simp
      _ ≤ q := hS
  have hlt : B.card < A.card := by
    rw [hA]
    omega
  obtain ⟨p, hpA, hpB⟩ := Finset.exists_mem_not_mem_of_card_lt_card hlt
  have hpl : inc p l := by
    simp only [hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at hpA
    exact hpA
  refine ⟨p, hpl, ?_⟩
  intro l' hl'
  by_contra hpl'
  apply hpB
  simp only [hBdef, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hpl, l', hl', hpl'⟩
