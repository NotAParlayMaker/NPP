import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_469 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  intro m k H T T' hT'
  classical
  have hsplit : T'.card = (T'.filter (fun x => x.val < m)).card + (T'.filter (fun x => ¬ x.val < m)).card :=
    (Finset.card_filter_add_card_filter_not (s := T') (fun x => x.val < m)).symm
  have hA : (T'.filter (fun x => x.val < m)).card = T.card := by
    symm
    refine Finset.card_bij (fun u _ => (⟨u.val, by omega⟩ : Fin (m + 2 * k * (m * m)))) ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_filter]
      refine ⟨(hT' _).2 (Or.inl ⟨u, hu, rfl⟩), u.isLt⟩
    · intro u₁ _ u₂ _ h
      exact Fin.ext (Fin.mk.inj h)
    · intro x hx
      rw [Finset.mem_filter] at hx
      rcases (hT' x).1 hx.1 with ⟨u, hu, hxu⟩ | ⟨u, v, i, _, _, _, hxv, _⟩
      · exact ⟨u, hu, Fin.ext hxu.symm⟩
      · omega
  let E_ord : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  have hE : E_ord.card = H.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card' H.edgeSet]
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [E_ord, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [Set.mem_toFinset]
      exact hp.2
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [E_ord, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        exact lt_asymm hp₁.1 (h1 ▸ h2 ▸ hp₂.1)
    · intro e he
      rw [Set.mem_toFinset] at he
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : H.Adj u v := he
        have hne : u ≠ v := H.ne_of_adj hadj
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · refine ⟨(u, v), ?_, rfl⟩
          simp [E_ord, hlt, hadj]
        · refine ⟨(v, u), ?_, Sym2.eq_swap⟩
          simp [E_ord, hlt, (H.adj_comm u v).mp hadj]
  have hB : (T'.filter (fun x => ¬ x.val < m)).card = (Finset.range k ×ˢ E_ord).card := by
    symm
    refine Finset.card_bij
      (fun q hq =>
        (⟨m + 2 * k * (q.2.1.val * m + q.2.2.val) + (if q.2.1 ∈ T then 2 * q.1 + 1 else 2 * q.1), by
          rw [Finset.mem_product, Finset.mem_range] at hq
          have huv : q.2.1.val * m + q.2.2.val + 1 ≤ m * m := by
            nlinarith [q.2.1.isLt, q.2.2.isLt]
          have hmul : 2 * k * (q.2.1.val * m + q.2.2.val) + 2 * k ≤ 2 * k * (m * m) := by
            nlinarith
          have hi : (if q.2.1 ∈ T then 2 * q.1 + 1 else 2 * q.1) < 2 * k := by
            split_ifs <;> omega
          omega⟩ : Fin (m + 2 * k * (m * m))))
      ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_product, Finset.mem_range] at hq
      simp only [E_ord, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [Finset.mem_filter]
      refine ⟨(hT' _).2 (Or.inr ⟨q.2.1, q.2.2, if q.2.1 ∈ T then 2 * q.1 + 1 else 2 * q.1, ?_, hq.2.1, hq.2.2, rfl, ?_⟩), by dsimp; omega⟩
      · split_ifs <;> omega
      · split_ifs with hmem
        · simp [hmem]
        · simp [hmem]
    · intro q₁ hq₁ q₂ hq₂ heq
      rw [Finset.mem_product, Finset.mem_range] at hq₁ hq₂
      have hval := congrArg Fin.val heq
      dsimp only at hval
      set i₁ := if q₁.2.1 ∈ T then 2 * q₁.1 + 1 else 2 * q₁.1
      set i₂ := if q₂.2.1 ∈ T then 2 * q₂.1 + 1 else 2 * q₂.1
      have hi₁ : i₁ < 2 * k := by dsimp [i₁]; split_ifs <;> omega
      have hi₂ : i₂ < 2 * k := by dsimp [i₂]; split_ifs <;> omega
      have hqeq : q₁.2.1.val * m + q₁.2.2.val = q₂.2.1.val * m + q₂.2.2.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have : q₁.2.1.val * m + q₁.2.2.val + 1 ≤ q₂.2.1.val * m + q₂.2.2.val := hlt
          nlinarith
        · have : q₂.2.1.val * m + q₂.2.2.val + 1 ≤ q₁.2.1.val * m + q₁.2.2.val := hlt
          nlinarith
      have hieq : i₁ = i₂ := by
        rw [hqeq] at hval
        omega
      have huval : q₁.2.1.val = q₂.2.1.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have : q₁.2.1.val + 1 ≤ q₂.2.1.val := hlt
          nlinarith [q₁.2.2.isLt, q₂.2.2.isLt]
        · have : q₂.2.1.val + 1 ≤ q₁.2.1.val := hlt
          nlinarith [q₁.2.2.isLt, q₂.2.2.isLt]
      have hu : q₁.2.1 = q₂.2.1 := Fin.ext huval
      have hvval : q₁.2.2.val = q₂.2.2.val := by
        rw [huval] at hqeq
        omega
      have hv : q₁.2.2 = q₂.2.2 := Fin.ext hvval
      have hj : q₁.1 = q₂.1 := by
        dsimp [i₁, i₂] at hieq
        rw [hu] at hieq
        split_ifs at hieq <;> omega
      exact Prod.ext hj (Prod.ext hu hv)
    · intro x hx
      rw [Finset.mem_filter] at hx
      rcases (hT' x).1 hx.1 with ⟨u, _, hxu⟩ | ⟨u, v, i, hik, huv, hadj, hxv, hpar⟩
      · exfalso
        exact hx.2 (hxu ▸ u.isLt)
      · refine ⟨(i / 2, (u, v)), ?_, ?_⟩
        · rw [Finset.mem_product, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          simp [E_ord, huv, hadj]
        · apply Fin.ext
          dsimp only
          have hi : (if u ∈ T then 2 * (i / 2) + 1 else 2 * (i / 2)) = i := by
            split_ifs with hmem
            · have : i % 2 = 1 := hpar.2 hmem
              omega
            · have : i % 2 ≠ 1 := fun h => hmem (hpar.1 h)
              omega
          omega
  rw [hsplit, hA, hB, Finset.card_product, Finset.card_range, hE]
