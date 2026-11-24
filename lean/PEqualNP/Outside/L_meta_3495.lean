import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3495

lemma line_inter_le_one {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (huniq : ∀ p q : Fin N, p ≠ q → ∃! l : Fin N, I p l ∧ I q l)
    (l l' : Fin N) (hne : l ≠ l') :
    (Finset.univ.filter fun p : Fin N => I p l ∧ I p l').card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  by_contra hpq
  obtain ⟨m, _, hm⟩ := huniq p q hpq
  have h1 : l = m := hm l ⟨hp.1, hq.1⟩
  have h2 : l' = m := hm l' ⟨hp.2, hq.2⟩
  exact hne (h1.trans h2.symm)

lemma main_proof (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p q' : Fin N, p ≠ q' → ∃! l : Fin N, I p l ∧ I q' l)
    (S : Finset (Fin N)) (hScard : S.card ≤ q)
    (A B : Fin N → Prop)
    (hcov : ∀ p l : Fin N, I p l → A p ∨ B l)
    (hAsub : ∀ p : Fin N, A p → ∃ l ∈ S, I p l)
    (hBdisj : ∀ l ∈ S, ¬ B l) :
    (∀ p : Fin N, A p ↔ ∃ l ∈ S, I p l) ∧ (∀ l : Fin N, B l ↔ l ∉ S) := by
  constructor
  · intro p
    constructor
    · exact hAsub p
    · rintro ⟨l, hlS, hI⟩
      rcases hcov p l hI with hA | hB
      · exact hA
      · exact absurd hB (hBdisj l hlS)
  · intro l
    constructor
    · intro hB hlS
      exact hBdisj l hlS hB
    · intro hlnotS
      let L : Finset (Fin N) := Finset.univ.filter (fun p => I p l)
      let hit : Finset (Fin N) := S.biUnion (fun l' => Finset.univ.filter (fun p => I p l ∧ I p l'))
      have hLcard : L.card = q + 1 := by
        rw [← Fintype.card_subtype]
        exact hdeg l
      have hhitCard : hit.card ≤ q := by
        calc hit.card ≤ ∑ l' ∈ S, (Finset.univ.filter (fun p : Fin N => I p l ∧ I p l')).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _l' ∈ S, 1 := by
              refine Finset.sum_le_sum (fun l' hl' => ?_)
              have hne : l ≠ l' := fun e => hlnotS (e ▸ hl')
              exact line_inter_le_one I huniq l l' hne
          _ = S.card := by simp
          _ ≤ q := hScard
      have hne_sdiff : (L \ hit).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : L ⊆ hit := Finset.sdiff_eq_empty_iff_subset.mp hemp
        have hle := Finset.card_le_card hsub
        omega
      obtain ⟨p, hp⟩ := hne_sdiff
      rw [Finset.mem_sdiff] at hp
      have hIpl : I p l := (Finset.mem_filter.mp hp.1).2
      have hnotA : ¬ A p := by
        intro hAp
        obtain ⟨l', hl'S, hIpl'⟩ := hAsub p hAp
        apply hp.2
        simp only [hit, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l', hl'S, hIpl, hIpl'⟩
      rcases hcov p l hIpl with hAp | hBl
      · exact absurd hAp hnotA
      · exact hBl

end PEqualNP.Outside.L_meta_3495

theorem PEqualNP.Outside.L_meta_3495 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ (x9 x10 : Fin x2 → Prop), (∀ (x11 x12 : Fin x2), x3 x11 x12 → x9 x11 ∨ x10 x12) → (∀ (x12 : Fin x2), x9 x12 → ∃ x14 ∈ x7, x3 x12 x14) → (∀ x13 ∈ x7, ¬x10 x13) → (∀ (x14 : Fin x2), x9 x14 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ ∀ (x14 : Fin x2), x10 x14 ↔ x14 ∉ x7 := by
  intro x1 x2 x3 _ hdeg huniq x7 hcard x9 x10 hcov hAsub hBdisj
  exact PEqualNP.Outside.L_meta_3495.main_proof x1 x2 x3 hdeg huniq x7 hcard x9 x10 hcov hAsub hBdisj
