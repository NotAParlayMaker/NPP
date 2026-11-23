import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic
import PEqualNP.Defs

private lemma radixCount {b a a' c c' : ℕ} (hc : c < b) (hc' : c' < b)
    (h : b * a + c = b * a' + c') : a = a' ∧ c = c' := by
  have ha : a = a' := by
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · have hle := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hlt)
      simp only [Nat.succ_eq_add_one, mul_add, mul_one] at hle
      omega
    · exact heq
    · have hle := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hgt)
      simp only [Nat.succ_eq_add_one, mul_add, mul_one] at hle
      omega
  exact ⟨ha, by rw [ha] at h; omega⟩

private lemma normalizedCard {m : ℕ} (H : SimpleGraph (Fin m))
    (E : Finset (Fin m × Fin m)) (hmem : ∀ e, e ∈ E ↔ e.1 < e.2 ∧ H.Adj e.1 e.2) :
    E.card = H.edgeSet.ncard := by
  classical
  let f (e : Fin m × Fin m) := s(e.1, e.2)
  have hI : Set.InjOn f (↑E : Set _) := by
    intro a ha b hb h
    have hA := ((hmem a).mp ha).1
    have hB := ((hmem b).mp hb).1
    rcases Sym2.eq_iff.mp h with h₁ | h₂
    · exact Prod.ext h₁.1 h₁.2
    · exact False.elim (lt_asymm hA (by simpa only [← h₂.1, ← h₂.2] using hB))
  have hE : E.image f = H.edgeFinset := by
    ext z
    induction z using Sym2.inductionOn with
    | _ u v =>
      rw [Finset.mem_image, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨e, he, hz⟩
        have heA := ((hmem e).mp he).2
        rcases Sym2.eq_iff.mp hz with h₁ | h₂
        · simpa only [h₁.1, h₁.2] using heA
        · exact H.adj_symm (by simpa only [h₂.1, h₂.2] using heA)
      · intro huv
        rcases lt_or_gt_of_ne (H.ne_of_adj huv) with huv' | hvu
        · exact ⟨(u,v), (hmem _).mpr ⟨huv',huv⟩, rfl⟩
        · exact ⟨(v,u), (hmem _).mpr ⟨hvu,H.adj_symm huv⟩,
            Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)⟩
  change E.card = H.edgeSet.ncard
  rw [← Finset.card_image_of_injOn hI, hE]
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

theorem PEqualNP.Outside.L_meta_304 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ c : ℕ, (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → c ≤ R.card) → ∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card := by
  intro m k H Q S hk hQ hS c hc U hU
  classical
  let N := m + 2 * k * (m * m)
  let base (u : Fin m) : Fin N := ⟨u.val, by dsimp [N]; omega⟩
  let E := (Finset.univ : Finset (Fin m × Fin m)).filter
    (fun e => e.1 < e.2 ∧ H.Adj e.1 e.2)
  let bad (e : E) : Prop := base e.val.1 ∉ U ∧ base e.val.2 ∉ U
  let B : Finset E := Finset.univ.filter bad
  let O : Finset (Fin m) := Finset.univ.filter (fun u => base u ∈ U)
  let R := O ∪ B.image (fun e : E => e.val.1)
  have hor (u v : Fin m) (hlt : u < v) (hadj : H.Adj u v) : u ∈ R ∨ v ∈ R := by
    by_cases hu : base u ∈ U
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩))
    by_cases hv : base v ∈ U
    · exact Or.inr (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩))
    let e : E := ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hadj⟩⟩
    exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu,hv⟩,rfl⟩))
  have hcR : c ≤ R.card := hc R (fun u v hv => by
    rcases lt_or_gt_of_ne (H.ne_of_adj hv) with h | h
    · exact hor u v h hv
    · exact (hor v u h (H.adj_symm hv)).symm)
  have hR : R.card ≤ O.card + B.card := calc
    R.card ≤ O.card + (B.image (fun e : E => e.val.1)).card := Finset.card_union_le _ _
    _ ≤ O.card + B.card := Nat.add_le_add_left Finset.card_image_le _
  have hslot (u v : Fin m) : u.val * m + v.val + 1 ≤ m * m := by
    have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt u.isLt)
    simp only [Nat.succ_eq_add_one, add_mul, one_mul] at h
    have hv := v.isLt
    omega
  have qExists (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) : ∃ x, Q u v p x := by
    by_cases hp0 : p = 0
    · exact ⟨base u,(hQ _ _ _ _).mpr (Or.inl ⟨hp0,rfl⟩)⟩
    by_cases hpEnd : p = 2 * k + 1
    · exact ⟨base v,(hQ _ _ _ _).mpr (Or.inr (Or.inl ⟨hpEnd,rfl⟩))⟩
    have hp' : p ≤ 2 * k := by omega
    have hlim := Nat.mul_le_mul_left (2 * k) (hslot u v)
    rw [Nat.mul_add, Nat.mul_one] at hlim
    let x : Fin N := ⟨m + 2 * k * (u.val * m + v.val) + p - 1, by dsimp [N]; omega⟩
    exact ⟨x,(hQ _ _ _ _).mpr (Or.inr (Or.inr ⟨by omega,hp',by dsimp [x]; omega⟩))⟩
  let J (e : E) : Type := Fin (k + if bad e then 1 else 0)
  let start (e : E) (j : J e) : ℕ := 2 * j.val + if bad e then 0 else 1
  have point (e : E) (j : J e) :
      ∃ x ∈ U, ∃ p, (p = start e j ∨ p = start e j + 1) ∧
        1 ≤ p ∧ p ≤ 2 * k ∧
        x.val + 1 = m + 2 * k * (e.val.1.val * m + e.val.2.val) + p := by
    have hj := j.isLt
    change j.val < k + (if bad e then 1 else 0) at hj
    have hp : start e j ≤ 2 * k := by
      by_cases he : bad e <;> simp [start,he] at * <;> omega
    obtain ⟨x,hx⟩ := qExists e.val.1 e.val.2 (start e j) (by omega)
    obtain ⟨y,hy⟩ := qExists e.val.1 e.val.2 (start e j + 1) (by omega)
    have he := (Finset.mem_filter.mp e.prop).2
    have hxy := (hS x y).mpr ⟨e.val.1,e.val.2,he.1,he.2,start e j,hp,Or.inl ⟨hx,hy⟩⟩
    have clean (z : Fin N) (p : ℕ) (hp' : p = start e j ∨ p = start e j + 1)
        (hz : z ∈ U) (hq : Q e.val.1 e.val.2 p z) :
        1 ≤ p ∧ p ≤ 2 * k ∧
          z.val + 1 = m + 2 * k * (e.val.1.val * m + e.val.2.val) + p := by
      rcases (hQ _ _ _ _).mp hq with ⟨h0,hz0⟩ | ⟨hend,hze⟩ | h
      · by_cases he : bad e
        · exact False.elim (he.1 ((Fin.ext hz0 : z = base e.val.1) ▸ hz))
        · simp [start,he] at hp'
          omega
      · by_cases he : bad e
        · exact False.elim (he.2 ((Fin.ext hze : z = base e.val.2) ▸ hz))
        · simp [he] at hj
          simp [start,he] at hp'
          omega
      · exact h
    rcases hU x y hxy with hxu | hyu
    · exact ⟨x,hxu,_,Or.inl rfl,clean x _ (Or.inl rfl) hxu hx⟩
    · exact ⟨y,hyu,_,Or.inr rfl,clean y _ (Or.inr rfl) hyu hy⟩
  let pt (e : E) (j : J e) : Fin N := Classical.choose (point e j)
  have ptSpec (e : E) (j : J e) :
      pt e j ∈ U ∧ ∃ p, (p = start e j ∨ p = start e j + 1) ∧
        1 ≤ p ∧ p ≤ 2 * k ∧
        (pt e j).val + 1 = m + 2 * k * (e.val.1.val * m + e.val.2.val) + p :=
    Classical.choose_spec (point e j)
  let F : O ⊕ (Σ e : E, J e) → U := fun z =>
    match z with
    | Sum.inl u => ⟨base u.val,(Finset.mem_filter.mp u.prop).2⟩
    | Sum.inr a => ⟨pt a.1 a.2,(ptSpec a.1 a.2).1⟩
  have hF : Function.Injective F := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hval := congrArg (fun x : U => x.val.val) hab
        change a.val.val = b.val.val at hval
        exact congrArg Sum.inl (Subtype.ext (Fin.ext hval))
      | inr b =>
        have hval := congrArg (fun x : U => x.val.val) hab
        change a.val.val = (pt b.1 b.2).val at hval
        obtain ⟨p,_,hlo,_,hv⟩ := (ptSpec b.1 b.2).2
        have := a.val.isLt
        omega
    | inr a =>
      cases b with
      | inl b =>
        have hval := congrArg (fun x : U => x.val.val) hab
        change (pt a.1 a.2).val = b.val.val at hval
        obtain ⟨p,_,hlo,_,hv⟩ := (ptSpec a.1 a.2).2
        have := b.val.isLt
        omega
      | inr b =>
        obtain ⟨a,i⟩ := a
        obtain ⟨b,j⟩ := b
        have hval := congrArg (fun x : U => x.val.val) hab
        change (pt a i).val = (pt b j).val at hval
        obtain ⟨p,hp,hpl,hpu,hv⟩ := (ptSpec a i).2
        obtain ⟨q,hq,hql,hqu,hw⟩ := (ptSpec b j).2
        have hindex : 2 * k * (a.val.1.val * m + a.val.2.val) + (p - 1) =
            2 * k * (b.val.1.val * m + b.val.2.val) + (q - 1) := by omega
        have hs := radixCount (show p - 1 < 2 * k by omega)
          (show q - 1 < 2 * k by omega) hindex
        have hm : m * a.val.1.val + a.val.2.val = m * b.val.1.val + b.val.2.val := by
          simpa only [mul_comm m] using hs.1
        have he := radixCount a.val.2.isLt b.val.2.isLt hm
        have heq : a = b := Subtype.ext (Prod.ext (Fin.ext he.1) (Fin.ext he.2))
        subst b
        have hpq : p = q := by have := hs.2; omega
        have hij : i = j := by
          apply Fin.ext
          rcases hp with hp | hp <;> rcases hq with hq | hq <;>
            simp only [start] at hp hq <;> omega
        subst j
        rfl
  have hcount := Fintype.card_le_of_injective F hF
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_coe, Fintype.card_coe] at hcount
  have hsum (e : E) : Fintype.card (J e) = k + if bad e then 1 else 0 := Fintype.card_fin _
  simp only [hsum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_coe] at hcount
  have hB : (∑ e : E, if bad e then 1 else 0) = B.card := by
    rw [← Finset.sum_filter]
    simp [B]
  have hEC := normalizedCard H E (by intro e; simp [E])
  rw [hB, hEC] at hcount
  calc
    c + k * H.edgeSet.ncard ≤ O.card + (H.edgeSet.ncard * k + B.card) := by
      rw [Nat.mul_comm H.edgeSet.ncard k]
      omega
    _ ≤ U.card := hcount
