import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_288 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k → (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ F : Finset (Fin (m + 2 * k * m * m)), (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T)) → (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ F ∨ y ∈ F) ∧ F.card = T.card + k * H.edgeSet.ncard := by
  classical
  intro k m H T hk hT S hS F hF
  constructor
  · have hrel : ∀ x y : Fin (m + 2 * k * m * m),
        (∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
          x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
          ((i.val = 0 ∧ y.val = u.val) ∨
           (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
           (i.val + 1 = 2 * k ∧ y.val = v.val))) →
        x ∈ F ∨ y ∈ F := by
      rintro x y ⟨u, v, huv, hadj, i, hx, hcase⟩
      rcases hcase with ⟨hi0, hy⟩ | ⟨hilt, hy⟩ | ⟨hieq, hy⟩
      · by_cases hu : u ∈ T
        · exact Or.inr ((hF y).2 (Or.inl ⟨u, hu, hy⟩))
        · exact Or.inl ((hF x).2 (Or.inr ⟨u, v, i, huv, hadj, hx, by simp [hi0, hu]⟩))
      · by_cases hp : i.val % 2 = 1 ↔ u ∈ T
        · exact Or.inl ((hF x).2 (Or.inr ⟨u, v, i, huv, hadj, hx, hp⟩))
        · refine Or.inr ((hF y).2 (Or.inr ⟨u, v, ⟨i.val + 1, hilt⟩, huv, hadj, ?_, ?_⟩))
          · dsimp only
            omega
          · by_cases hu : u ∈ T <;> simp [hu] at hp ⊢ <;> omega
      · by_cases hu : u ∈ T
        · refine Or.inl ((hF x).2 (Or.inr ⟨u, v, i, huv, hadj, hx, ?_⟩))
          simp only [hu, iff_true]
          omega
        · have hv : v ∈ T := (hT u v hadj).resolve_left hu
          exact Or.inr ((hF y).2 (Or.inl ⟨v, hv, hy⟩))
    intro x y hxy
    rw [hS, SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with h | h
    · exact hrel x y h
    · exact (hrel y x h).symm
  · have hbound : ∀ (u v : Fin m) (i : Fin (2 * k)),
        m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
      intro u v i
      have h1 : u.val * m + v.val + 1 ≤ m * m := by
        have hu : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m u.isLt
        have hv : v.val + 1 ≤ m := v.isLt
        rw [Nat.add_mul, Nat.one_mul] at hu
        omega
      have h2 : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
        Nat.mul_le_mul_left (2 * k) h1
      have h3 : 2 * k * (u.val * m + v.val + 1) = 2 * k * (u.val * m + v.val) + 2 * k := by
        rw [Nat.mul_add, Nat.mul_one]
      have h4 : 2 * k * m * m = 2 * k * (m * m) := Nat.mul_assoc _ _ _
      have hi : i.val < 2 * k := i.isLt
      omega
    let fA : Fin m → Fin (m + 2 * k * m * m) := fun u => ⟨u.val, by have := u.isLt; omega⟩
    let A : Finset (Fin (m + 2 * k * m * m)) := T.image fA
    have hfA_inj : Function.Injective fA := by
      intro u₁ u₂ h
      have h0 := congrArg Fin.val h
      exact Fin.ext h0
    have hA_card : A.card = T.card := Finset.card_image_of_injective T hfA_inj
    let E : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
    let idx : Fin m → Fin k → Fin (2 * k) :=
      fun u t => ⟨2 * t.val + if u ∈ T then 1 else 0, by have := t.isLt; split_ifs <;> omega⟩
    let fB : (Fin m × Fin m) × Fin k → Fin (m + 2 * k * m * m) :=
      fun p => ⟨m + 2 * k * (p.1.1.val * m + p.1.2.val) + (idx p.1.1 p.2).val,
        hbound p.1.1 p.1.2 (idx p.1.1 p.2)⟩
    let B : Finset (Fin (m + 2 * k * m * m)) :=
      (E ×ˢ (Finset.univ : Finset (Fin k))).image fB
    have hfB_inj : Function.Injective fB := by
      rintro ⟨⟨u₁, v₁⟩, t₁⟩ ⟨⟨u₂, v₂⟩, t₂⟩ h
      have hval : 2 * k * (u₁.val * m + v₁.val) + (idx u₁ t₁).val =
          2 * k * (u₂.val * m + v₂.val) + (idx u₂ t₂).val := by
        have h0 := congrArg Fin.val h
        dsimp only [fB] at h0
        omega
      have hpos2k : 0 < 2 * k := by omega
      have hq1 : u₁.val * m + v₁.val = u₂.val * m + v₂.val := by
        have hdiv := congrArg (· / (2 * k)) hval
        rw [Nat.mul_add_div hpos2k, Nat.mul_add_div hpos2k,
          Nat.div_eq_of_lt (idx u₁ t₁).isLt, Nat.div_eq_of_lt (idx u₂ t₂).isLt] at hdiv
        omega
      have hi_eq : (idx u₁ t₁).val = (idx u₂ t₂).val := by
        rw [hq1] at hval
        omega
      have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) v₁.isLt
      have hu_eq : u₁.val = u₂.val := by
        have hdiv := congrArg (· / m) hq1
        rw [Nat.mul_comm u₁.val m, Nat.mul_comm u₂.val m,
          Nat.mul_add_div hm, Nat.mul_add_div hm,
          Nat.div_eq_of_lt v₁.isLt, Nat.div_eq_of_lt v₂.isLt] at hdiv
        omega
      have hv_eq : v₁.val = v₂.val := by
        rw [hu_eq] at hq1
        omega
      have hu : u₁ = u₂ := Fin.ext hu_eq
      have hv : v₁ = v₂ := Fin.ext hv_eq
      subst hu
      subst hv
      have ht_eq : t₁.val = t₂.val := by
        dsimp only [idx] at hi_eq
        omega
      exact congrArg (Prod.mk (u₁, v₁)) (Fin.ext ht_eq)
    have hB_card : B.card = k * E.card := by
      calc B.card = (E ×ˢ (Finset.univ : Finset (Fin k))).card :=
            Finset.card_image_of_injective _ hfB_inj
        _ = E.card * (Finset.univ : Finset (Fin k)).card := Finset.card_product _ _
        _ = E.card * k := by simp
        _ = k * E.card := Nat.mul_comm _ _
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro j hjA hjB
      rcases Finset.mem_image.1 hjA with ⟨u, -, rfl⟩
      rcases Finset.mem_image.1 hjB with ⟨⟨⟨u', v'⟩, t⟩, -, h⟩
      have h0 := congrArg Fin.val h
      dsimp only [fA, fB] at h0
      have hu : u.val < m := u.isLt
      omega
    have hFAB : F = A ∪ B := by
      ext j
      rw [hF j, Finset.mem_union]
      constructor
      · rintro (⟨u, huT, hj⟩ | ⟨u, v, i, huv, hadj, hj, hpar⟩)
        · left
          refine Finset.mem_image.2 ⟨u, huT, ?_⟩
          exact Fin.ext hj.symm
        · right
          let t : Fin k := ⟨i.val / 2, by have := i.isLt; omega⟩
          refine Finset.mem_image.2 ⟨((u, v), t), ?_, ?_⟩
          · exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, hadj⟩,
              Finset.mem_univ _⟩
          · apply Fin.ext
            dsimp only [fB, idx, t]
            by_cases hu : u ∈ T <;> simp [hu] at hpar ⊢ <;> omega
      · rintro (hjA | hjB)
        · left
          rcases Finset.mem_image.1 hjA with ⟨u, huT, rfl⟩
          exact ⟨u, huT, rfl⟩
        · right
          rcases Finset.mem_image.1 hjB with ⟨⟨⟨u, v⟩, t⟩, hp, rfl⟩
          have hpE : (u, v) ∈ E := (Finset.mem_product.1 hp).1
          rcases (Finset.mem_filter.1 hpE).2 with ⟨huv, hadj⟩
          refine ⟨u, v, idx u t, huv, hadj, rfl, ?_⟩
          dsimp only [idx]
          by_cases hu : u ∈ T <;> simp [hu]
    have hE_card : E.card = H.edgeSet.ncard := by
      let g : Fin m × Fin m → Sym2 (Fin m) := fun p => s(p.1, p.2)
      have hg_inj : Set.InjOn g (E : Set (Fin m × Fin m)) := by
        rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ h
        have hlt₁ : u₁ < v₁ := (Finset.mem_filter.1 h₁).2.1
        have hlt₂ : u₂ < v₂ := (Finset.mem_filter.1 h₂).2.1
        rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact absurd (lt_trans hlt₁ hlt₂) (lt_irrefl _)
      have himg : E.image g = H.edgeSet.toFinset := by
        ext e
        induction e using Sym2.ind with
        | _ a b =>
          rw [Set.mem_toFinset, SimpleGraph.mem_edgeSet, Finset.mem_image]
          constructor
          · rintro ⟨⟨u, v⟩, hp, heq⟩
            have hadj : H.Adj u v := (Finset.mem_filter.1 hp).2.2
            rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hadj
            · exact hadj.symm
          · intro hadj
            rcases lt_or_gt_of_ne (H.ne_of_adj hadj) with hlt | hlt
            · exact ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt, hadj⟩, rfl⟩
            · exact ⟨(b, a), Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt, hadj.symm⟩,
                Sym2.eq_swap⟩
      rw [Set.ncard_eq_toFinset_card', ← himg, Finset.card_image_of_injOn hg_inj]
    rw [hFAB, Finset.card_union_of_disjoint hdisj, hA_card, hB_card, hE_card]
