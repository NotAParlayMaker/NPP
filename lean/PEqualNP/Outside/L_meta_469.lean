import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_469 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  classical
  intro m k H T T' hT'
  have hdec : ∀ K B1 B2 r1 r2 : ℕ, r1 < K → r2 < K → K * B1 + r1 = K * B2 + r2 → B1 = B2 := by
    intro K B1 B2 r1 r2 h1 h2 h
    have hK : 0 < K := by omega
    have e1 : (K * B1 + r1) / K = B1 := by
      rw [Nat.mul_add_div hK, Nat.div_eq_of_lt h1]
      simp
    have e2 : (K * B2 + r2) / K = B2 := by
      rw [Nat.mul_add_div hK, Nat.div_eq_of_lt h2]
      simp
    rw [h] at e1
    omega
  have hbound : ∀ a b : Fin m, m + 2 * k * (a.val * m + b.val) + 2 * k ≤ m + 2 * k * (m * m) := by
    intro a b
    have ha := a.isLt
    have hb := b.isLt
    have h0 : (a.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m ha
    have h1 : a.val * m + b.val + 1 ≤ m * m := by
      have h2 : (a.val + 1) * m = a.val * m + m := by ring
      omega
    have h3 : 2 * k * (a.val * m + b.val + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left (2 * k) h1
    have h4 : 2 * k * (a.val * m + b.val + 1) = 2 * k * (a.val * m + b.val) + 2 * k := by ring
    omega
  let P : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  have hP : ∀ p : Fin m × Fin m, p ∈ P ↔ p.1 < p.2 ∧ H.Adj p.1 p.2 := by
    intro p
    simp [P]
  have hE : H.edgeSet.ncard = P.card := by
    have h1 : H.edgeSet = ((P.image (fun p : Fin m × Fin m => s(p.1, p.2)) : Finset (Sym2 (Fin m))) : Set (Sym2 (Fin m))) := by
      ext e
      induction e using Sym2.ind with
      | _ a b =>
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        constructor
        · intro h
          have hab : H.Adj a b := (SimpleGraph.mem_edgeSet H).1 h
          rcases lt_or_gt_of_ne (H.ne_of_adj hab) with h2 | h2
          · exact ⟨(a, b), (hP _).2 ⟨h2, hab⟩, rfl⟩
          · exact ⟨(b, a), (hP _).2 ⟨h2, hab.symm⟩, Sym2.eq_swap⟩
        · rintro ⟨p, hp, h4⟩
          rw [← h4]
          exact (SimpleGraph.mem_edgeSet H).2 ((hP p).1 hp).2
    rw [h1, Set.ncard_coe_finset, Finset.card_image_of_injOn]
    rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
    have hp' := (hP _).1 (Finset.mem_coe.1 hp)
    have hq' := (hP _).1 (Finset.mem_coe.1 hq)
    have h' : s(a, b) = s(c, d) := h
    rcases Sym2.eq_iff.1 h' with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [h2, h3]
    · exfalso
      have h5 : a < b := hp'.1
      have h6 : c < d := hq'.1
      rw [h2, h3] at h5
      exact lt_asymm h5 h6
  let c : Fin m → ℕ := fun u => if u ∈ T then 1 else 0
  have hc : ∀ u : Fin m, c u ≤ 1 ∧ (c u = 1 ↔ u ∈ T) := by
    intro u
    by_cases h : u ∈ T <;> simp [c, h]
  let g : (Fin m × Fin m) × ℕ → ℕ := fun q => m + 2 * k * (q.1.1.val * m + q.1.2.val) + (2 * q.2 + c q.1.1)
  have hg : ∀ (u v : Fin m) (j : ℕ), g ((u, v), j) = m + 2 * k * (u.val * m + v.val) + (2 * j + c u) := by
    intro u v j
    rfl
  have hval : T'.image Fin.val = T.image Fin.val ∪ (P ×ˢ Finset.range k).image g := by
    ext n
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases (hT' x).1 hx with ⟨u, hu, hxu⟩ | ⟨u, v, i, hi, huv, hadj, hxv, hpar⟩
      · exact Or.inl ⟨u, hu, hxu.symm⟩
      · refine Or.inr ⟨((u, v), i / 2), Finset.mem_product.2 ⟨(hP _).2 ⟨huv, hadj⟩, Finset.mem_range.2 (by omega)⟩, ?_⟩
        rw [hg]
        have h1 := (hc u).1
        have h3 : i % 2 = 1 ↔ c u = 1 := hpar.trans (hc u).2.symm
        omega
    · rintro (⟨u, hu, rfl⟩ | ⟨⟨⟨u, v⟩, j⟩, hq, rfl⟩)
      · exact ⟨Fin.castLE (Nat.le_add_right _ _) u, (hT' _).2 (Or.inl ⟨u, hu, rfl⟩), rfl⟩
      · have hq1 := Finset.mem_product.1 hq
        have huv := (hP _).1 hq1.1
        have hj : j < k := Finset.mem_range.1 hq1.2
        have h1 := (hc u).1
        have h2 := (hc u).2
        have hb : g ((u, v), j) < m + 2 * k * (m * m) := by
          rw [hg]
          have := hbound u v
          omega
        refine ⟨⟨g ((u, v), j), hb⟩, (hT' _).2 (Or.inr ⟨u, v, 2 * j + c u, by omega, huv.1, huv.2, hg u v j, ?_⟩), rfl⟩
        rw [← h2]
        omega
  have hinj : Set.InjOn g ↑(P ×ˢ Finset.range k) := by
    rintro ⟨⟨u1, v1⟩, j1⟩ h1 ⟨⟨u2, v2⟩, j2⟩ h2 h
    have hj1 : j1 < k := Finset.mem_range.1 (Finset.mem_product.1 (Finset.mem_coe.1 h1)).2
    have hj2 : j2 < k := Finset.mem_range.1 (Finset.mem_product.1 (Finset.mem_coe.1 h2)).2
    rw [hg, hg] at h
    have c1 := (hc u1).1
    have c2 := (hc u2).1
    have e := hdec (2 * k) (u1.val * m + v1.val) (u2.val * m + v2.val) (2 * j1 + c u1) (2 * j2 + c u2) (by omega) (by omega) (by omega)
    have e' := hdec m u1.val u2.val v1.val v2.val v1.isLt v2.isLt (by rw [Nat.mul_comm m u1.val, Nat.mul_comm m u2.val]; exact e)
    have hu : u1 = u2 := Fin.ext e'
    subst hu
    have hv : v1 = v2 := Fin.ext (by omega)
    subst hv
    have hj : j1 = j2 := by omega
    subst hj
    rfl
  have hdisj : Disjoint (T.image Fin.val) ((P ×ˢ Finset.range k).image g) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    rcases Finset.mem_image.1 h1 with ⟨u, _, rfl⟩
    rcases Finset.mem_image.1 h2 with ⟨⟨⟨a, b⟩, j⟩, _, hq⟩
    rw [hg] at hq
    have := u.isLt
    omega
  calc T'.card = (T'.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = (T.image Fin.val).card + ((P ×ˢ Finset.range k).image g).card := by
        rw [hval, Finset.card_union_of_disjoint hdisj]
    _ = T.card + k * H.edgeSet.ncard := by
        rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range, hE, Nat.mul_comm]
