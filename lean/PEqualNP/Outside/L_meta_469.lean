import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

theorem PEqualNP.Outside.L_meta_469 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  intro m k H T T' hT'
  classical
  have hbound : ∀ (u v : Fin m) (i : ℕ), i < 2 * k →
      m + 2 * k * (u.val * m + v.val) + i < m + 2 * k * (m * m) := by
    intro u v i hi
    have h1 : u.val * m + v.val + 1 ≤ m * m := by
      have hu : u.val + 1 ≤ m := u.isLt
      have hv : v.val + 1 ≤ m := v.isLt
      calc u.val * m + v.val + 1
          ≤ u.val * m + m := by omega
        _ = (u.val + 1) * m := by rw [Nat.succ_mul]
        _ ≤ m * m := Nat.mul_le_mul_right m hu
    have h2 : 2 * k * (u.val * m + v.val) + 2 * k ≤ 2 * k * (m * m) := by
      calc 2 * k * (u.val * m + v.val) + 2 * k
          = 2 * k * (u.val * m + v.val + 1) := by rw [Nat.mul_succ]
        _ ≤ 2 * k * (m * m) := Nat.mul_le_mul_left (2 * k) h1
    omega
  have hdiv : ∀ (d a b r s : ℕ), r < d → s < d → d * a + r = d * b + s → a = b ∧ r = s := by
    intro d a b r s hr hs h
    have hab : a = b := by
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exfalso
        have h1 : d * a + d ≤ d * b := by
          calc d * a + d = d * (a + 1) := by rw [Nat.mul_succ]
            _ ≤ d * b := Nat.mul_le_mul_left d hlt
        omega
      · exact heq
      · exfalso
        have h1 : d * b + d ≤ d * a := by
          calc d * b + d = d * (b + 1) := by rw [Nat.mul_succ]
            _ ≤ d * a := Nat.mul_le_mul_left d hgt
        omega
    subst hab
    exact ⟨rfl, by omega⟩
  let E : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  let f₁ : Fin m → Fin (m + 2 * k * (m * m)) :=
    fun u => ⟨u.val, by omega⟩
  let f₂ : (Fin m × Fin m) × Fin k → Fin (m + 2 * k * (m * m)) :=
    fun p =>
      ⟨m + 2 * k * (p.1.1.val * m + p.1.2.val) + (2 * p.2.val + if p.1.1 ∈ T then 1 else 0),
       hbound p.1.1 p.1.2 _ (by have := p.2.isLt; split_ifs <;> omega)⟩
  have hf₁ : Function.Injective f₁ := by
    intro u₁ u₂ h
    have hval := congrArg Fin.val h
    exact Fin.ext hval
  have hf₂ : Function.Injective f₂ := by
    intro ⟨⟨u₁, v₁⟩, j₁⟩ ⟨⟨u₂, v₂⟩, j₂⟩ h
    have hval : m + 2 * k * (u₁.val * m + v₁.val) + (2 * j₁.val + if u₁ ∈ T then 1 else 0) =
        m + 2 * k * (u₂.val * m + v₂.val) + (2 * j₂.val + if u₂ ∈ T then 1 else 0) :=
      congrArg Fin.val h
    have hi₁ : 2 * j₁.val + (if u₁ ∈ T then 1 else 0) < 2 * k := by
      have := j₁.isLt; split_ifs <;> omega
    have hi₂ : 2 * j₂.val + (if u₂ ∈ T then 1 else 0) < 2 * k := by
      have := j₂.isLt; split_ifs <;> omega
    have h1 := hdiv (2 * k) (u₁.val * m + v₁.val) (u₂.val * m + v₂.val) _ _ hi₁ hi₂ (by omega)
    have h2 := hdiv m u₁.val u₂.val v₁.val v₂.val v₁.isLt v₂.isLt (by
      rw [Nat.mul_comm m u₁.val, Nat.mul_comm m u₂.val]
      exact h1.1)
    have hu : u₁ = u₂ := Fin.ext h2.1
    have hv : v₁ = v₂ := Fin.ext h2.2
    subst hu
    subst hv
    have hj : j₁ = j₂ := by
      ext
      have := h1.2
      split_ifs at this <;> omega
    subst hj
    rfl
  have hEq : T' = T.image f₁ ∪ (E ×ˢ (Finset.univ : Finset (Fin k))).image f₂ := by
    ext x
    rw [hT', Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (⟨u, hu, hxu⟩ | ⟨u, v, i, hi, huv, hadj, hxi, hmod⟩)
      · left
        exact ⟨u, hu, Fin.ext hxu.symm⟩
      · right
        refine ⟨((u, v), ⟨i / 2, by omega⟩), ?_, ?_⟩
        · rw [Finset.mem_product]
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, Finset.mem_univ _⟩
        · ext
          dsimp [f₂]
          rw [hxi]
          by_cases hu : u ∈ T
          · have : i % 2 = 1 := hmod.mpr hu
            simp only [hu, ↓reduceIte]
            omega
          · have : i % 2 ≠ 1 := fun h => hu (hmod.mp h)
            simp only [hu, ↓reduceIte]
            omega
    · rintro (⟨u, hu, hfx⟩ | ⟨⟨⟨u, v⟩, j⟩, hmem, hfx⟩)
      · left
        exact ⟨u, hu, (congrArg Fin.val hfx).symm⟩
      · right
        rw [Finset.mem_product] at hmem
        have hE := (Finset.mem_filter.mp hmem.1).2
        refine ⟨u, v, 2 * j.val + if u ∈ T then 1 else 0, ?_, hE.1, hE.2, (congrArg Fin.val hfx).symm, ?_⟩
        · have := j.isLt; split_ifs <;> omega
        · by_cases hu : u ∈ T
          · simp only [hu, ↓reduceIte, iff_true]
            omega
          · simp only [hu, ↓reduceIte, iff_false]
            omega
  have hDisj : Disjoint (T.image f₁) ((E ×ˢ (Finset.univ : Finset (Fin k))).image f₂) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨u, _, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨⟨⟨a, b⟩, j⟩, _, hfx⟩
    have hval := congrArg Fin.val hfx
    dsimp [f₁, f₂] at hval
    have := u.isLt
    omega
  have hEcard : E.card = H.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      rw [Set.mem_toFinset]
      exact (Finset.mem_filter.mp hp).2.2
    · intro p₁ hp₁ p₂ hp₂ heq
      have h1 := (Finset.mem_filter.mp hp₁).2.1
      have h2 := (Finset.mem_filter.mp hp₂).2.1
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Prod.ext ha hb
      · exfalso
        rw [ha, hb] at h1
        exact lt_asymm h1 h2
    · intro e he
      rw [Set.mem_toFinset] at he
      induction e using Sym2.ind with
      | _ a b =>
        have hadj : H.Adj a b := he
        have hne : a ≠ b := H.ne_of_adj hadj
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hadj⟩, rfl⟩
        · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, hadj.symm⟩, Sym2.eq_swap⟩
  rw [hEq, Finset.card_union_of_disjoint hDisj,
    Finset.card_image_of_injective T hf₁,
    Finset.card_image_of_injective _ hf₂,
    Finset.card_product, Finset.card_univ, Fintype.card_fin,
    hEcard, Nat.mul_comm]
