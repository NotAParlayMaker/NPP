import Mathlib
import PEqualNP.Defs

private lemma subdivision_address_unique (stride a b x y : ℕ)
    (hx : x < stride) (hy : y < stride)
    (h : stride * a + x = stride * b + y) : a = b ∧ x = y := by
  have ordered (p q i j : ℕ) (hpq : p < q) (hi : i < stride) :
      stride * p + i < stride * q + j := by
    have hmul := Nat.mul_le_mul_left stride (show p + 1 ≤ q by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hab : a = b := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ordered a b x y hlt hx).ne h
    · exact (ordered b a y x hgt hy).ne h.symm
  subst b
  exact ⟨rfl, by omega⟩

theorem PEqualNP.Outside.L_meta_291 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k →
      (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) →
      (∀ t ∈ T, ∃ w : Fin m, H.Adj t w ∧ w ∉ T) →
      ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
        S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
            x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
              ((i.val = 0 ∧ y.val = u.val) ∨
               (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
               (i.val + 1 = 2 * k ∧ y.val = v.val))) →
        ∀ F : Finset (Fin (m + 2 * k * m * m)),
          (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨
            ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧
              j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T)) →
          ∀ x ∈ F, ∃ y : Fin (m + 2 * k * m * m), S.Adj x y ∧ y ∉ F := by
  classical
  intro k m H T hk _ privateNeighbor S hS F hF x hx
  let B := 2 * k
  have hB : 0 < B := by dsimp [B]; omega
  have hBeven : B % 2 = 0 := by dsimp [B]; omega
  let N := m + B * m * m
  let base (u v : Fin m) := m + B * (u.val * m + v.val)
  have base_ge (u v : Fin m) : m ≤ base u v := Nat.le_add_right _ _
  let outer (t : Fin m) : Fin N := ⟨t.val, lt_of_lt_of_le t.isLt (Nat.le_add_right _ _)⟩
  let inner (u v : Fin m) (i : Fin B) : Fin N := ⟨base u v + i.val, by
    have hu := Nat.mul_le_mul_right m (show u.val + 1 ≤ m by have := u.isLt; omega)
    rw [Nat.add_mul, Nat.one_mul] at hu
    have hv := v.isLt
    have hc : u.val * m + v.val + 1 ≤ m * m := by omega
    have hm := Nat.mul_le_mul_left B hc
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hm
    have hi := i.isLt
    dsimp [base, N]
    omega⟩
  have outer_mem (t : Fin m) : outer t ∈ F ↔ t ∈ T := by
    constructor
    · intro ht
      rcases (hF _).mp ht with ⟨a, ha, he⟩ | ⟨a, b, j, _, _, he, _⟩
      · have e : t = a := Fin.ext he
        simpa [e] using ha
      · change t.val = base a b + j.val at he
        have := base_ge a b
        have := t.isLt
        omega
    · intro ht
      exact (hF _).mpr (Or.inl ⟨t, ht, rfl⟩)
  have inner_mem (u v : Fin m) (huv : u < v) (he : H.Adj u v) (i : Fin B) :
      inner u v i ∈ F ↔ (i.val % 2 = 1 ↔ u ∈ T) := by
    constructor
    · intro hi
      rcases (hF _).mp hi with ⟨a, _, hval⟩ | ⟨a, b, j, _, _, hval, hp⟩
      · change base u v + i.val = a.val at hval
        have := base_ge u v
        have := a.isLt
        omega
      · change base u v + i.val = base a b + j.val at hval
        have hc : B * (u.val * m + v.val) + i.val =
            B * (a.val * m + b.val) + j.val := by dsimp [base] at hval; omega
        obtain ⟨hcode, hindex⟩ := subdivision_address_unique B _ _ _ _ i.isLt j.isLt hc
        rw [Nat.mul_comm u.val m, Nat.mul_comm a.val m] at hcode
        obtain ⟨hfirst, _⟩ := subdivision_address_unique m _ _ _ _ v.isLt b.isLt hcode
        have hhead : u = a := Fin.ext hfirst
        simpa [hindex, hhead] using hp
    · intro hp
      exact (hF _).mpr (Or.inr ⟨u, v, i, huv, he, rfl, hp⟩)
  have along (u v : Fin m) (huv : u < v) (he : H.Adj u v) (i : Fin B)
      (y : Fin N) (hy : (i.val = 0 ∧ y.val = u.val) ∨
        (i.val + 1 < B ∧ y.val = base u v + i.val + 1) ∨
        (i.val + 1 = B ∧ y.val = v.val)) : S.Adj (inner u v i) y := by
    rw [hS, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨u, v, huv, he, i, rfl, hy⟩⟩
    intro hEq
    have hv : base u v + i.val = y.val := congrArg Fin.val hEq
    have hb := base_ge u v
    have hu := u.isLt
    have hv' := v.isLt
    rcases hy with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  rcases (hF x).mp hx with ⟨t, ht, hxt⟩ | ⟨u, v, i, huv, he, hxi, hp⟩
  · have hxOuter : x = outer t := Fin.ext hxt
    subst x
    obtain ⟨w, htw, hw⟩ := privateNeighbor t ht
    have hne : t ≠ w := fun h => hw (h ▸ ht)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let i : Fin B := ⟨0, hB⟩
      refine ⟨inner t w i, (along t w hlt htw i (outer t) (Or.inl ⟨rfl, rfl⟩)).symm, ?_⟩
      intro h
      have hbad := ((inner_mem t w hlt htw i).mp h).mpr ht
      change 0 % 2 = 1 at hbad
      omega
    · let i : Fin B := ⟨B - 1, by omega⟩
      have hi : i.val + 1 = B := by change B - 1 + 1 = B; omega
      have hodd : i.val % 2 = 1 := by change (B - 1) % 2 = 1; omega
      refine ⟨inner w t i, (along w t hgt htw.symm i (outer t) (Or.inr (Or.inr ⟨hi, rfl⟩))).symm, ?_⟩
      exact fun h => hw (((inner_mem w t hgt htw.symm i).mp h).mp hodd)
  · have hxInner : x = inner u v i := Fin.ext hxi
    subst x
    have hi := i.isLt
    by_cases ht : u ∈ T
    · have hodd := hp.mpr ht
      let j : Fin B := ⟨i.val - 1, by omega⟩
      have hj : j.val + 1 = i.val := by change i.val - 1 + 1 = i.val; omega
      have hadj : S.Adj (inner u v j) (inner u v i) := by
        apply along u v huv he j
        exact Or.inr (Or.inl ⟨by omega, by change base u v + i.val = base u v + j.val + 1; omega⟩)
      refine ⟨inner u v j, hadj.symm, ?_⟩
      intro h
      have hbad := ((inner_mem u v huv he j).mp h).mpr ht
      omega
    · have hnotOdd : i.val % 2 ≠ 1 := fun h => ht (hp.mp h)
      have hnext : i.val + 1 < B := by omega
      let j : Fin B := ⟨i.val + 1, hnext⟩
      have hadj : S.Adj (inner u v i) (inner u v j) := by
        apply along u v huv he i
        exact Or.inr (Or.inl ⟨hnext, by change base u v + (i.val + 1) = base u v + i.val + 1; omega⟩)
      refine ⟨inner u v j, hadj, ?_⟩
      have hodd : j.val % 2 = 1 := by change (i.val + 1) % 2 = 1; omega
      exact fun h => ht (((inner_mem u v huv he j).mp h).mp hodd)
