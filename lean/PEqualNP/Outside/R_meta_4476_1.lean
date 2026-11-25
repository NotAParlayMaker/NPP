import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_4476_1
  (overlapping : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
    let m (F : Set (Finset ℕ)) : Set (Finset ℕ) :=
      {C | C ∈ F ∧ ∀ J ∈ F, J ⊆ C → J = C}
    200 ≤ q → n = q^2+q+1 →
    (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (g o : ℕ) (W : ℕ → Set (Finset ℕ)),
      let step (i : Fin g) (a b : ℕ) (u : Bool) :=
        max a b < n+n+i.val ∧
          if u then W (n+n+i.val) = m (W a ∪ W b)
          else W (n+n+i.val) ∈ [m (Set.image2 (· ∪ ·) (W a) (W b)), W a, {∅}]
      let clean (i : Fin g) := ∃ a b u, step i a b u ∧
        (u = true → ∀ A ∈ W a, ∀ B ∈ W b, Disjoint A B)
      o < n+n+g → (∀ i < n+n, W i = {{i}}) →
      (∀ i, ∃ a b u, step i a b u) →
      (∀ i < n+n+g, m (W i) = W i) →
      (∀ C ∈ W o, ∀ p l : Fin n, I p l → p.val ∈ C ∨ n+l.val ∈ C) →
      (∀ Y : Finset (Fin n), Y.card ≤ q → ∃ C ∈ W o, ∀ p : Fin n,
        (p.val ∈ C ↔ ∃ l ∈ Y, I p l) ∧ (n+p.val ∈ C ↔ p ∉ Y)) →
      (∃ i, ¬clean i) →
      n*q ≤ 100*g)
  (disjoint : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
    let m (F : Set (Finset ℕ)) : Set (Finset ℕ) :=
      {C | C ∈ F ∧ ∀ J ∈ F, J ⊆ C → J = C}
    200 ≤ q → n = q^2+q+1 →
    (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (g o : ℕ) (W : ℕ → Set (Finset ℕ)),
      let step (i : Fin g) (a b : ℕ) (u : Bool) :=
        max a b < n+n+i.val ∧
          if u then W (n+n+i.val) = m (W a ∪ W b)
          else W (n+n+i.val) ∈ [m (Set.image2 (· ∪ ·) (W a) (W b)), W a, {∅}]
      let clean (i : Fin g) := ∃ a b u, step i a b u ∧
        (u = true → ∀ A ∈ W a, ∀ B ∈ W b, Disjoint A B)
      o < n+n+g → (∀ i < n+n, W i = {{i}}) →
      (∀ i, ∃ a b u, step i a b u) →
      (∀ i < n+n+g, m (W i) = W i) →
      (∀ C ∈ W o, ∀ p l : Fin n, I p l → p.val ∈ C ∨ n+l.val ∈ C) →
      (∀ Y : Finset (Fin n), Y.card ≤ q → ∃ C ∈ W o, ∀ p : Fin n,
        (p.val ∈ C ↔ ∃ l ∈ Y, I p l) ∧ (n+p.val ∈ C ↔ p ∉ Y)) →
      (∀ i, clean i) →
      n*q ≤ 100*g)
  : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
    (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
    (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
    ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 →
    (∀ x13 < x2 + x2, x11 x13 = {{x13}}) →
    (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) →
    (∃ x15 < x9, ∃ x16 < x2 + x2 + x15, ∃ x17 < x2 + x2 + x15, x11 (x2 + x2 + x15) = x11 x16 ∪ x11 x17 ∧ ∃ x18 ∈ x11 x16, ∃ x19 ∈ x11 x17, ¬Disjoint x18 x19) →
    (∀ x16 ∈ x11 x10, ∀ (x18 x19 : Fin x2), x3 x18 x19 → ↑x18 ∈ x16 ∨ x2 + ↑x19 ∈ x16) →
    (∀ (x17 : Finset (Fin x2)), x17.card ≤ x1 → ∃ x19 ∈ x11 x10, ∀ (x20 : Fin x2), (↑x20 ∈ x19 ↔ ∃ x21 ∈ x17, x3 x20 x21) ∧ (x2 + ↑x20 ∈ x19 ↔ x20 ∉ x17)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  have canonicalCoverMinimal (n q : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I]
      (hLine : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
      (join : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
      (Y : Finset (Fin n)) (hY : Y.card ≤ q) (K B : Finset ℕ)
      (rangeK : K ⊆ Finset.range (n + n))
      (low : ∀ p : Fin n, p.val ∈ K ↔ ∃ l ∈ Y, I p l)
      (high : ∀ l : Fin n, n + l.val ∈ K ↔ l ∉ Y)
      (sub : B ⊆ K)
      (cover : ∀ p l, I p l → p.val ∈ B ∨ n + l.val ∈ B) :
      B = K := by
    let points (l : Fin n) : Finset (Fin n) := Finset.univ.filter (fun p => I p l)
    have memPoints (p l : Fin n) : p ∈ points l ↔ I p l := by
      simp [points]
    have intersectionBound (l a : Fin n) (hne : l ≠ a) :
        ((points l) ∩ (points a)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp p' hp'
      by_contra hpp'
      obtain ⟨c, _, unique⟩ := join p p' hpp'
      have pl := Finset.mem_inter.mp hp
      have pl' := Finset.mem_inter.mp hp'
      have lc : l = c := unique l ⟨(memPoints p l).mp pl.1, (memPoints p' l).mp pl'.1⟩
      have ac : a = c := unique a ⟨(memPoints p a).mp pl.2, (memPoints p' a).mp pl'.2⟩
      exact hne (lc.trans ac.symm)

    have privatePoint (l : Fin n) (hl : l ∉ Y) : ∃ p, I p l ∧ p.val ∉ K := by
      let hit := Y.biUnion (fun a => (points l) ∩ (points a))
      have hitBound : hit.card ≤ q := calc
        hit.card ≤ ∑ a ∈ Y, ((points l) ∩ (points a)).card := Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ Y, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro a ha
          exact intersectionBound l a (fun e => hl (e.symm ▸ ha))
        _ = Y.card := by simp
        _ ≤ q := hY
      by_contra noPrivate
      have contained : points l ⊆ hit := by
        intro p hp
        by_contra absent
        apply noPrivate
        refine ⟨p, (memPoints p l).mp hp, ?_⟩
        intro hpK
        obtain ⟨a, ha, hpa⟩ := (low p).mp hpK
        exact absent (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_inter.mpr
          ⟨hp, (memPoints p a).mpr hpa⟩⟩)
      have hcard : (points l).card = q + 1 := hLine l
      have hle := Finset.card_le_card contained
      omega

    apply Finset.Subset.antisymm sub
    intro k hk
    have hkRange := Finset.mem_range.mp (rangeK hk)
    by_cases hkLow : k < n
    · let p : Fin n := ⟨k, hkLow⟩
      obtain ⟨l, hl, hpl⟩ := (low p).mp hk
      exact (cover p l hpl).resolve_right (fun hlB => (high l).mp (sub hlB) hl)
    · let l : Fin n := ⟨k - n, by omega⟩
      have lWire : n + l.val = k := by
        dsimp [l]
        omega
      rw [← lWire] at hk ⊢
      obtain ⟨p, hpl, hpK⟩ := privatePoint l ((high l).mp hk)
      exact (cover p l hpl).resolve_left (fun hpB => hpK (sub hpB))
  intro q n I inst hq hn line join g o W ho raw step _oldOverlap coverage sparse
  classical
  let m (F : Set (Finset ℕ)) : Set (Finset ℕ) :=
    {C | C ∈ F ∧ ∀ J ∈ F, J ⊆ C → J = C}
  have memberMin (F : Set (Finset ℕ)) (C : Finset ℕ) (hC : C ∈ F) :
      ∃ A ∈ m F, A ⊆ C := by
    let sizes (k : ℕ) := ∃ A ∈ F, A ⊆ C ∧ A.card = k
    have existsSize : ∃ k, sizes k := ⟨C.card, C, hC, Finset.Subset.refl _, rfl⟩
    obtain ⟨A, hA, sub, hcard⟩ := Nat.find_spec existsSize
    refine ⟨A, ⟨hA, ?_⟩, sub⟩
    intro J hj hsub
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
    exact Nat.find_min' existsSize ⟨J, hj, hsub.trans sub, rfl⟩
  let refines (F G : Set (Finset ℕ)) := ∀ C ∈ F, ∃ A ∈ G, A ⊆ C
  have minCongr (F G : Set (Finset ℕ)) (fg : refines F G) (gf : refines G F) :
      m F = m G := by
    have transfer (P Q : Set (Finset ℕ)) (pq : refines P Q) (qp : refines Q P)
        (C : Finset ℕ) (hC : C ∈ m P) : C ∈ m Q := by
      have minimum (J : Finset ℕ) (hj : J ∈ Q) (sub : J ⊆ C) : J = C := by
        obtain ⟨A, hA, hsub⟩ := qp J hj
        have same := hC.2 A hA (hsub.trans sub)
        exact Finset.Subset.antisymm sub (same ▸ hsub)
      obtain ⟨J, hj, sub⟩ := pq C hC.1
      exact ⟨(minimum J hj sub) ▸ hj, minimum⟩
    exact Set.ext fun C => ⟨transfer F G fg gf C, transfer G F gf fg C⟩
  have smaller (F : Set (Finset ℕ)) : refines (m F) F :=
    fun C h => ⟨C, h.1, Finset.Subset.refl _⟩
  have ownMin (F : Set (Finset ℕ)) : m (m F) = m F :=
    minCongr (m F) F (smaller F) (memberMin F)
  have minSingleton (A : Finset ℕ) : m {A} = {A} := by
    ext C
    constructor
    · intro h
      exact h.1
    · intro h
      refine ⟨h, fun J j _ => ?_⟩
      exact (Set.mem_singleton_iff.mp j).trans (Set.mem_singleton_iff.mp h).symm
  have minUnion (F G : Set (Finset ℕ)) : m (F ∪ G) = m (m F ∪ m G) := by
    apply minCongr
    · intro C h
      rcases h with h | h
      · obtain ⟨A, ha, hs⟩ := memberMin F C h
        exact ⟨A, Or.inl ha, hs⟩
      · obtain ⟨A, ha, hs⟩ := memberMin G C h
        exact ⟨A, Or.inr ha, hs⟩
    · intro C h
      exact ⟨C, h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1), Finset.Subset.refl _⟩
  have minProduct (F G : Set (Finset ℕ)) :
      m (Set.image2 (· ∪ ·) F G) = m (Set.image2 (· ∪ ·) (m F) (m G)) := by
    apply minCongr
    · intro C h
      obtain ⟨A, ha, B, hb, rfl⟩ := Set.mem_image2.mp h
      obtain ⟨A', hA', aSub⟩ := memberMin F A ha
      obtain ⟨B', hB', bSub⟩ := memberMin G B hb
      exact ⟨A' ∪ B', Set.mem_image2.mpr ⟨A',hA',B',hB',rfl⟩, Finset.union_subset_union aSub bSub⟩
    · intro C h
      obtain ⟨A, ha, B, hb, rfl⟩ := Set.mem_image2.mp h
      exact ⟨A ∪ B, Set.mem_image2.mpr ⟨A,ha.1,B,hb.1,rfl⟩, Finset.Subset.refl _⟩
  let V (i : ℕ) := m (W i)
  have choice (i : Fin g) : ∃ a b : ℕ, ∃ u : Bool,
      max a b < n+n+i.val ∧
        if u then V (n+n+i.val) = m (V a ∪ V b)
        else V (n+n+i.val) ∈ [m (Set.image2 (· ∪ ·) (V a) (V b)), V a, {∅}] := by
    obtain ⟨a, ha, b, hb, h⟩ := step i.val i.isLt
    have bounds := max_lt_iff.mpr ⟨ha,hb⟩
    rcases h with product | copy | zero | union
    · refine ⟨a,b,false,bounds,List.mem_cons.mpr (Or.inl ?_)⟩
      exact (congrArg m product).trans (minProduct _ _)
    · refine ⟨a,b,false,bounds,?_⟩
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl (congrArg m copy))))
    · refine ⟨a,b,false,bounds,?_⟩
      have eq := (congrArg m zero).trans (minSingleton ∅)
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr eq))))
    · exact ⟨a,b,true,bounds,(congrArg m union).trans (minUnion _ _)⟩
  have support (i : ℕ) (hi : i < n+n+g) :
      ∀ C ∈ W i, C ⊆ Finset.range (n+n) := by
    induction i using Nat.strongRecOn with
    | ind i ih =>
      intro C hC
      by_cases base : i < n+n
      · rw [raw i base] at hC
        rw [Set.mem_singleton_iff.mp hC]
        exact Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr base)
      have k : i - (n+n) < g := by omega
      obtain ⟨x,hx,y,hy,f⟩ := step _ k
      have eq : n+n+(i-(n+n)) = i := by omega
      rw [eq] at hx hy f
      rcases f with prod | copy | empty | union
      · rw [prod] at hC
        obtain ⟨A,hA,B,hB,rfl⟩ := Set.mem_image2.mp hC
        exact Finset.union_subset (ih x hx (hx.trans hi) A hA) (ih y hy (hy.trans hi) B hB)
      · rw [copy] at hC
        exact ih x hx (hx.trans hi) C hC
      · rw [empty] at hC
        rw [Set.mem_singleton_iff.mp hC]
        exact Finset.empty_subset _
      · rw [union] at hC
        exact hC.elim (ih x hx (hx.trans hi) C) (ih y hy (hy.trans hi) C)
  have vRaw (i : ℕ) (hi : i < n+n) : V i = {{i}} :=
    (congrArg m (raw i hi)).trans (minSingleton {i})
  have vMin (i : ℕ) (_ : i < n+n+g) : m (V i) = V i := ownMin (W i)
  have vCover (C : Finset ℕ) (hC : C ∈ V o) := coverage C hC.1
  have vSparse (Y : Finset (Fin n)) (hY : Y.card ≤ q) :
      ∃ C ∈ V o, ∀ p : Fin n,
        (p.val ∈ C ↔ ∃ l ∈ Y, I p l) ∧ (n+p.val ∈ C ↔ p ∉ Y) := by
    obtain ⟨C, hc, desc⟩ := sparse Y hY
    have hline (l : Fin n) : (Finset.univ.filter fun p => I p l).card = q+1 :=
      (Fintype.card_subtype (fun p => I p l)).symm.trans (line l)
    refine ⟨C, ⟨hc, ?_⟩, desc⟩
    intro J hj sub
    exact canonicalCoverMinimal n q I hline join Y hY C J (support o ho C hc)
      (fun p => (desc p).1) (fun l => (desc l).2) sub (coverage J hj)
  let clean (i : Fin g) := ∃ a b : ℕ, ∃ u : Bool,
    (max a b < n+n+i.val ∧
      if u then V (n+n+i.val) = m (V a ∪ V b)
      else V (n+n+i.val) ∈ [m (Set.image2 (· ∪ ·) (V a) (V b)), V a, {∅}]) ∧
    (u = true → ∀ A ∈ V a, ∀ B ∈ V b, Disjoint A B)
  by_cases impossible : ∃ i, ¬clean i
  · exact overlapping q n I hq hn line join g o V ho vRaw choice vMin vCover vSparse impossible
  · apply disjoint q n I hq hn line join g o V ho vRaw choice vMin vCover vSparse
    intro i
    by_contra h
    exact impossible ⟨i,h⟩
