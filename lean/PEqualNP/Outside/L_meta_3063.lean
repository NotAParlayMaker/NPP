import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3063

theorem ul {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (Q : ℕ → Prop) [DecidablePred Q]
    (J : Finset α) (N0 s : ℕ) (c1 c2 : ℕ → ℕ)
    (hin : ∀ w < N0, (S w).card ≤ 1)
    (hg : ∀ g, N0 ≤ g → g < N0 + s → c1 g < g ∧ c2 g < g ∧ S g = S (c1 g) ∪ S (c2 g) ∧
      (Q g → Q (c1 g) ∧ Q (c2 g))) :
    ∀ N, ∀ W : Finset ℕ, (∀ w ∈ W, w < N ∧ w < N0 + s ∧ Q w) →
    (J ∩ W.biUnion S).card ≤ ((Finset.range N).filter (fun g => N0 ≤ g ∧ g < N0 + s ∧ Q g ∧
      2 ≤ (S g ∩ J).card)).card + W.card := by
  intro N
  induction N with
  | zero =>
    intro W hW
    have : W = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by have := hW w hw; omega)
    subst this; simp
  | succ N ih =>
    intro W hW
    have hcnt : ((Finset.range N).filter (fun g => N0 ≤ g ∧ g < N0 + s ∧ Q g ∧
        2 ≤ (S g ∩ J).card)).card ≤ ((Finset.range (N+1)).filter (fun g => N0 ≤ g ∧ g < N0 + s ∧ Q g ∧
        2 ≤ (S g ∩ J).card)).card := by
      apply Finset.card_le_card
      intro g hg'
      simp only [Finset.mem_filter, Finset.mem_range] at hg' ⊢
      exact ⟨by omega, hg'.2⟩
    by_cases hN : N ∈ W
    · have hWe : W = insert N (W.erase N) := (Finset.insert_erase hN).symm
      have hcardW : W.card = (W.erase N).card + 1 := (Finset.card_erase_add_one hN).symm
      have hW' : ∀ w ∈ W.erase N, w < N ∧ w < N0 + s ∧ Q w := by
        intro w hw
        have h1 := Finset.ne_of_mem_erase hw
        have h2 := hW w (Finset.mem_of_mem_erase hw)
        exact ⟨by omega, h2.2⟩
      have hNW := hW N hN
      by_cases hp : N0 ≤ N ∧ 2 ≤ (S N ∩ J).card
      · obtain ⟨h1, h2, hS, hQ⟩ := hg N hp.1 hNW.2.1
        have hQ' := hQ hNW.2.2
        have hW'' : ∀ w ∈ insert (c1 N) (insert (c2 N) (W.erase N)), w < N ∧ w < N0 + s ∧ Q w := by
          intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with rfl | rfl | hw
          · exact ⟨h1, by omega, hQ'.1⟩
          · exact ⟨h2, by omega, hQ'.2⟩
          · exact hW' w hw
        have I := ih _ hW''
        have hsub : J ∩ W.biUnion S ⊆ J ∩ (insert (c1 N) (insert (c2 N) (W.erase N))).biUnion S := by
          intro x hx
          rw [hWe] at hx
          simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_insert] at hx ⊢
          obtain ⟨hxJ, w, hw, hxw⟩ := hx
          refine ⟨hxJ, ?_⟩
          rcases hw with rfl | hw
          · rw [hS, Finset.mem_union] at hxw
            rcases hxw with h | h
            · exact ⟨c1 w, Or.inl rfl, h⟩
            · exact ⟨c2 w, Or.inr (Or.inl rfl), h⟩
          · exact ⟨w, Or.inr (Or.inr hw), hxw⟩
        have hc2 : (insert (c1 N) (insert (c2 N) (W.erase N))).card ≤ (W.erase N).card + 2 := by
          have := Finset.card_insert_le (c1 N) (insert (c2 N) (W.erase N))
          have := Finset.card_insert_le (c2 N) (W.erase N)
          omega
        have hcnt2 : ((Finset.range (N+1)).filter (fun g => N0 ≤ g ∧ g < N0 + s ∧ Q g ∧
            2 ≤ (S g ∩ J).card)).card = ((Finset.range N).filter (fun g => N0 ≤ g ∧ g < N0 + s ∧ Q g ∧
            2 ≤ (S g ∩ J).card)).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert, if_pos ⟨hp.1, hNW.2.1, hNW.2.2, hp.2⟩]
          rw [Finset.card_insert_of_notMem]
          simp
        have := Finset.card_le_card hsub
        omega
      · have hle : (S N ∩ J).card ≤ 1 := by
          by_cases h0 : N0 ≤ N
          · have : ¬ 2 ≤ (S N ∩ J).card := fun h => hp ⟨h0, h⟩
            omega
          · exact le_trans (Finset.card_le_card Finset.inter_subset_left) (hin N (by omega))
        have I := ih _ hW'
        have hsub : J ∩ W.biUnion S ⊆ (S N ∩ J) ∪ (J ∩ (W.erase N).biUnion S) := by
          intro x hx
          rw [hWe] at hx
          simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union] at hx ⊢
          obtain ⟨hxJ, w, hw, hxw⟩ := hx
          rcases hw with rfl | hw
          · exact Or.inl ⟨hxw, hxJ⟩
          · exact Or.inr ⟨hxJ, w, hw, hxw⟩
        have := Finset.card_le_card hsub
        have := Finset.card_union_le (S N ∩ J) (J ∩ (W.erase N).biUnion S)
        omega
    · have hW' : ∀ w ∈ W, w < N ∧ w < N0 + s ∧ Q w := by
        intro w hw
        have h2 := hW w hw
        have : w ≠ N := fun h => hN (h ▸ hw)
        exact ⟨by omega, h2.2⟩
      have := ih W hW'
      omega

def F {α β : Type*} [DecidableEq α] [DecidableEq β] (S : ℕ → Finset α) (S' : ℕ → Finset β)
    (N0 s : ℕ) (Z J : Finset α) : Finset ℕ :=
  (Finset.range (N0 + s)).filter (fun g => N0 ≤ g ∧ g < N0 + s ∧ (S' g = ∅ ∧ S g ⊆ Z) ∧
    2 ≤ (S g ∩ J).card)

theorem ul2 {α β : Type*} [DecidableEq α] [DecidableEq β] (S : ℕ → Finset α) (S' : ℕ → Finset β)
    (N0 s : ℕ) (c1 c2 : ℕ → ℕ) (hin : ∀ w < N0, (S w).card ≤ 1)
    (hg : ∀ g, N0 ≤ g → g < N0 + s → c1 g < g ∧ c2 g < g ∧ S g = S (c1 g) ∪ S (c2 g) ∧
      S' g = S' (c1 g) ∪ S' (c2 g))
    (Z J : Finset α) (W : Finset ℕ) (hW : ∀ w ∈ W, w < N0 + s ∧ S' w = ∅ ∧ S w ⊆ Z) :
    (J ∩ W.biUnion S).card ≤ (F S S' N0 s Z J).card + W.card := by
  have := ul S (fun g => S' g = ∅ ∧ S g ⊆ Z) J N0 s c1 c2 hin (by
    intro g h1 h2
    obtain ⟨e1, e2, e3, e4⟩ := hg g h1 h2
    refine ⟨e1, e2, e3, ?_⟩
    rintro ⟨q1, q2⟩
    rw [e4, Finset.union_eq_empty] at q1
    rw [e3, Finset.union_subset_iff] at q2
    exact ⟨⟨q1.1, q2.1⟩, ⟨q1.2, q2.2⟩⟩) (N0 + s) W (fun w hw => ⟨(hW w hw).1, (hW w hw).1, (hW w hw).2⟩)
  exact this

section
variable {n m k : ℕ}

def Wq (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
    (q : Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun t => 2 ≤ (B t).card ∧ q ∈ A t ∧ ∀ l ∈ B t, inc q l = true)

def Vf (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
    (f : Fin m) : Finset (Fin k) :=
  Finset.univ.filter (fun t => 2 ≤ (A t).card ∧ f ∈ B t ∧ ∀ p ∈ A t, inc p f = true)

def Uq (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
    (q : Fin n) : Finset (Fin m) := (Wq inc A B q).biUnion B

def Uf (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
    (f : Fin m) : Finset (Fin n) := (Vf inc A B f).biUnion A

def Xs (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)) :
    Finset (Fin n × Fin m) :=
  Finset.univ.filter (fun q => inc q.1 q.2 = true ∧ ∃ i j : Fin k, i ≠ j ∧ q.1 ∈ A i ∧ q.2 ∈ B i ∧
    q.1 ∈ A j ∧ q.2 ∈ B j)

def XR (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)) :
    Finset (Fin n × Fin m) :=
  (Xs inc A B).filter (fun q => q.2 ∉ Uq inc A B q.1 ∧ q.1 ∉ Uf inc A B q.2 ∧
    ¬ ∃ t, A t = {q.1} ∧ B t = {q.2})

theorem res (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
    (S1 : ∀ (p : Fin n) (i j : Fin k) (l1 l2 : Fin m), i ≠ j → p ∈ A i → p ∈ A j → l1 ∈ B i →
      l2 ∈ B j → inc p l1 = false → inc p l2 = false → False)
    (S2 : ∀ (l : Fin m) (i j : Fin k) (q1 q2 : Fin n), i ≠ j → l ∈ B i → l ∈ B j → q1 ∈ A i →
      q2 ∈ A j → inc q1 l = false → inc q2 l = false → False)
    (p : Fin n) (l : Fin m) (h : (p, l) ∈ XR inc A B) :
    (∃ u, B u = {l} ∧ p ∈ A u ∧ ∃ q ∈ A u, inc q l = false) ∧
    (∃ v, A v = {p} ∧ l ∈ B v ∧ ∃ l' ∈ B v, inc p l' = false) := by
  simp only [XR, Xs, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨⟨hinc, i, j, hij, hpi, hli, hpj, hlj⟩, hU, hV, hS⟩ := h
  have key1 : ∀ u, p ∈ A u → l ∈ B u → (∀ l' ∈ B u, inc p l' = true) →
      B u = {l} ∧ ∃ q ∈ A u, inc q l = false := by
    intro u hpu hlu hgood
    have hBu : B u = {l} := by
      have : (B u).card < 2 := by
        by_contra hc
        push_neg at hc
        apply hU
        simp only [Uq, Wq, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, ⟨hc, hpu, hgood⟩, hlu⟩
      exact Finset.eq_singleton_iff_unique_mem.2
        ⟨hlu, fun x hx => Finset.card_le_one.1 (by omega) x hx l hlu⟩
    refine ⟨hBu, ?_⟩
    by_contra hc
    push_neg at hc
    have hc' : ∀ q ∈ A u, inc q l = true := fun q hq => by simpa using hc q hq
    have hA : (A u).card < 2 := by
      by_contra hc2
      push_neg at hc2
      apply hV
      simp only [Uf, Vf, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, ⟨hc2, hlu, hc'⟩, hpu⟩
    have hAu : A u = {p} := Finset.eq_singleton_iff_unique_mem.2
        ⟨hpu, fun x hx => Finset.card_le_one.1 (by omega) x hx p hpu⟩
    exact hS ⟨u, hAu, hBu⟩
  have key2 : ∀ v, p ∈ A v → l ∈ B v → (∀ q ∈ A v, inc q l = true) →
      A v = {p} ∧ ∃ l' ∈ B v, inc p l' = false := by
    intro u hpu hlu hgood
    have hAu : A u = {p} := by
      have : (A u).card < 2 := by
        by_contra hc
        push_neg at hc
        apply hV
        simp only [Uf, Vf, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, ⟨hc, hlu, hgood⟩, hpu⟩
      exact Finset.eq_singleton_iff_unique_mem.2
        ⟨hpu, fun x hx => Finset.card_le_one.1 (by omega) x hx p hpu⟩
    refine ⟨hAu, ?_⟩
    by_contra hc
    push_neg at hc
    have hc' : ∀ l' ∈ B u, inc p l' = true := fun q hq => by simpa using hc q hq
    have hB : (B u).card < 2 := by
      by_contra hc2
      push_neg at hc2
      apply hU
      simp only [Uq, Wq, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, ⟨hc2, hpu, hc'⟩, hlu⟩
    have hBu : B u = {l} := Finset.eq_singleton_iff_unique_mem.2
        ⟨hlu, fun x hx => Finset.card_le_one.1 (by omega) x hx l hlu⟩
    exact hS ⟨u, hAu, hBu⟩
  have pg : (∀ l' ∈ B i, inc p l' = true) ∨ (∀ l' ∈ B j, inc p l' = true) := by
    by_contra hc
    push_neg at hc
    obtain ⟨⟨l1, h1, e1⟩, ⟨l2, h2, e2⟩⟩ := hc
    exact S1 p i j l1 l2 hij hpi hpj h1 h2 (by simpa using e1) (by simpa using e2)
  have lg : (∀ q ∈ A i, inc q l = true) ∨ (∀ q ∈ A j, inc q l = true) := by
    by_contra hc
    push_neg at hc
    obtain ⟨⟨l1, h1, e1⟩, ⟨l2, h2, e2⟩⟩ := hc
    exact S2 l i j l1 l2 hij hli hlj h1 h2 (by simpa using e1) (by simpa using e2)
  constructor
  · rcases pg with g | g
    · exact ⟨i, (key1 i hpi hli g).1, hpi, (key1 i hpi hli g).2⟩
    · exact ⟨j, (key1 j hpj hlj g).1, hpj, (key1 j hpj hlj g).2⟩
  · rcases lg with g | g
    · exact ⟨i, (key2 i hpi hli g).1, hli, (key2 i hpi hli g).2⟩
    · exact ⟨j, (key2 j hpj hlj g).1, hlj, (key2 j hpj hlj g).2⟩

theorem classes (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n))
    (B : Fin k → Finset (Fin m)) :
    (Finset.univ.biUnion (Wq inc A B)).card + (Finset.univ.biUnion (Vf inc A B)).card +
      (Finset.univ.filter (fun t => (A t).card = 1 ∧ (B t).card = 1)).card +
      (Finset.univ.filter (fun t => (A t).card = 1 ∧ 2 ≤ (B t).card ∧
        ∀ q ∈ A t, ∃ l ∈ B t, inc q l = false)).card ≤
    k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card := by
  set CA := Finset.univ.biUnion (Wq inc A B)
  set CB := Finset.univ.biUnion (Vf inc A B)
  set CS := (Finset.univ.filter (fun t => (A t).card = 1 ∧ (B t).card = 1))
  set CR := (Finset.univ.filter (fun t => (A t).card = 1 ∧ 2 ≤ (B t).card ∧
        ∀ q ∈ A t, ∃ l ∈ B t, inc q l = false))
  set D := ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true)))
  have h1 := Finset.card_union_add_card_inter CA CB
  have h2 : CA ∩ CB ⊆ D := by
    intro t ht
    simp only [CA, CB, D, Wq, Vf, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht ⊢
    obtain ⟨⟨q, hB2, hq, hql⟩, ⟨f, hA2, hf, hpf⟩⟩ := ht
    exact ⟨⟨q, hB2, hql⟩, ⟨f, hf, hA2, hpf⟩⟩
  have hd1 : Disjoint (CA ∪ CB) CS := by
    rw [Finset.disjoint_left]
    intro t ht hs
    simp only [CA, CB, CS, Wq, Vf, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht hs
    rcases ht with ⟨q, h, _⟩ | ⟨q, h, _⟩ <;> omega
  have hd2 : Disjoint (CA ∪ CB ∪ CS) CR := by
    rw [Finset.disjoint_left]
    intro t ht hs
    simp only [CA, CB, CS, CR, Wq, Vf, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht hs
    rcases ht with (⟨q, h, hq, hql⟩ | ⟨q, h, _⟩) | h
    · obtain ⟨l, hl, hf⟩ := hs.2.2 q hq
      rw [hql l hl] at hf
      exact Bool.noConfusion hf
    · omega
    · omega
  have h3 := Finset.card_union_of_disjoint hd1
  have h4 := Finset.card_union_of_disjoint hd2
  have h5 := Finset.card_le_univ (CA ∪ CB ∪ CS ∪ CR)
  have h6 := Finset.card_le_card h2
  simp only [Fintype.card_fin] at h5
  omega

theorem Uq_inc (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n))
    (B : Fin k → Finset (Fin m)) (q : Fin n) (l : Fin m) (h : l ∈ Uq inc A B q) : inc q l = true := by
  simp only [Uq, Wq, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨t, ⟨_, _, h⟩, hl⟩ := h
  exact h l hl

theorem Uf_inc (inc : Fin n → Fin m → Bool) (A : Fin k → Finset (Fin n))
    (B : Fin k → Finset (Fin m)) (f : Fin m) (p : Fin n) (h : p ∈ Uf inc A B f) : inc p f = true := by
  simp only [Uf, Vf, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨t, ⟨_, _, h⟩, hl⟩ := h
  exact h p hl

theorem two_of {α : Type*} [DecidableEq α] {S J : Finset α} (h : 2 ≤ (S ∩ J).card) :
    ∃ x y, x ≠ y ∧ x ∈ S ∧ x ∈ J ∧ y ∈ S ∧ y ∈ J := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < (S ∩ J).card)
  rw [Finset.mem_inter] at hx hy
  exact ⟨x, y, hxy, hx.1, hx.2, hy.1, hy.2⟩

theorem core (s N0 : ℕ) (inc : Fin n → Fin m → Bool)
    (hlin : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)) (hk : 1 ≤ k)
    (SP : ℕ → Finset (Fin n)) (SL : ℕ → Finset (Fin m)) (c1 c2 : ℕ → ℕ) (a b : Fin k → ℕ)
    (hinP : ∀ w < N0, (SP w).card ≤ 1) (hinL : ∀ w < N0, (SL w).card ≤ 1)
    (hg : ∀ g, N0 ≤ g → g < N0 + s → c1 g < g ∧ c2 g < g ∧ SP g = SP (c1 g) ∪ SP (c2 g) ∧
      SL g = SL (c1 g) ∪ SL (c2 g))
    (ha : ∀ i, a i < N0 + s ∧ SP (a i) = A i ∧ SL (a i) = ∅)
    (hb : ∀ i, b i < N0 + s ∧ SP (b i) = ∅ ∧ SL (b i) = B i)
    (S1 : ∀ (p : Fin n) (i j : Fin k) (l1 l2 : Fin m), i ≠ j → p ∈ A i → p ∈ A j → l1 ∈ B i →
      l2 ∈ B j → inc p l1 = false → inc p l2 = false → False)
    (S2 : ∀ (l : Fin m) (i j : Fin k) (q1 q2 : Fin n), i ≠ j → l ∈ B i → l ∈ B j → q1 ∈ A i →
      q2 ∈ A j → inc q1 l = false → inc q2 l = false → False) :
    (Xs inc A B).card ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card := by
  have hcl2 := classes inc A B
  have hgL : ∀ g, N0 ≤ g → g < N0 + s → c1 g < g ∧ c2 g < g ∧ SL g = SL (c1 g) ∪ SL (c2 g) ∧
      SP g = SP (c1 g) ∪ SP (c2 g) := fun g h1 h2 =>
    ⟨(hg g h1 h2).1, (hg g h1 h2).2.1, (hg g h1 h2).2.2.2, (hg g h1 h2).2.2.1⟩
  have hgP : ∀ g, N0 ≤ g → g < N0 + s → c1 g < g ∧ c2 g < g ∧ SP g = SP (c1 g) ∪ SP (c2 g) ∧
      SL g = SL (c1 g) ∪ SL (c2 g) := hg
  set CS := (Finset.univ.filter (fun t => (A t).card = 1 ∧ (B t).card = 1)) with hCS
  set CR := (Finset.univ.filter (fun t => (A t).card = 1 ∧ 2 ≤ (B t).card ∧
        ∀ q ∈ A t, ∃ l ∈ B t, inc q l = false)) with hCR
  set X := Xs inc A B with hXdef
  set XA := X.filter (fun q => q.2 ∈ Uq inc A B q.1) with hXA'
  set XB := X.filter (fun q => q.1 ∈ Uf inc A B q.2) with hXB'
  set XS := X.filter (fun q => ∃ t, A t = {q.1} ∧ B t = {q.2}) with hXS'
  set R := XR inc A B with hR'
  have hsplit : X.card ≤ XA.card + XB.card + XS.card + R.card := by
    have hsub : X ⊆ XA ∪ XB ∪ XS ∪ R := by
      intro q hq
      simp only [XA, XB, XS, R, XR, Finset.mem_union, Finset.mem_filter]
      by_cases h1 : q.2 ∈ Uq inc A B q.1
      · exact Or.inl (Or.inl (Or.inl ⟨hq, h1⟩))
      by_cases h2 : q.1 ∈ Uf inc A B q.2
      · exact Or.inl (Or.inl (Or.inr ⟨hq, h2⟩))
      by_cases h3 : ∃ t, A t = {q.1} ∧ B t = {q.2}
      · exact Or.inl (Or.inr ⟨hq, h3⟩)
      · exact Or.inr ⟨hq, h1, h2, h3⟩
    have := Finset.card_le_card hsub
    have := Finset.card_union_le (XA ∪ XB ∪ XS) R
    have := Finset.card_union_le (XA ∪ XB) XS
    have := Finset.card_union_le XA XB
    omega
  have hXA : XA.card ≤ ∑ q, ((F SL SP N0 s (Uq inc A B q) (Uq inc A B q)).card +
      (Wq inc A B q).card) := by
    have hsub : XA ⊆ Finset.univ.biUnion (fun q => (Uq inc A B q).image (fun l => (q, l))) := by
      intro x hx
      simp only [XA, Finset.mem_filter] at hx
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨x.1, x.2, hx.2, rfl⟩
    refine le_trans (Finset.card_le_card hsub)
      (le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_))
    intro q _
    refine le_trans Finset.card_image_le ?_
    have := ul2 SL SP N0 s c1 c2 hinL hgL (Uq inc A B q) (Uq inc A B q)
      ((Wq inc A B q).image b) (by
        intro w hw
        simp only [Finset.mem_image] at hw
        obtain ⟨t, ht, rfl⟩ := hw
        refine ⟨(hb t).1, (hb t).2.1, ?_⟩
        rw [(hb t).2.2]
        intro l hl
        simp only [Uq, Finset.mem_biUnion]
        exact ⟨t, ht, hl⟩)
    have e : Uq inc A B q ∩ ((Wq inc A B q).image b).biUnion SL = Uq inc A B q := by
      apply Finset.inter_eq_left.2
      intro l hl
      simp only [Uq, Finset.mem_biUnion] at hl
      obtain ⟨t, ht, hl⟩ := hl
      simp only [Finset.mem_biUnion, Finset.mem_image]
      exact ⟨b t, ⟨t, ht, rfl⟩, by rw [(hb t).2.2]; exact hl⟩
    rw [e] at this
    have := Finset.card_image_le (s := Wq inc A B q) (f := b)
    omega
  have hXB : XB.card ≤ ∑ f, ((F SP SL N0 s (Uf inc A B f) (Uf inc A B f)).card +
      (Vf inc A B f).card) := by
    have hsub : XB ⊆ Finset.univ.biUnion (fun f => (Uf inc A B f).image (fun p => (p, f))) := by
      intro x hx
      simp only [XB, Finset.mem_filter] at hx
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨x.2, x.1, hx.2, rfl⟩
    refine le_trans (Finset.card_le_card hsub)
      (le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_))
    intro f _
    refine le_trans Finset.card_image_le ?_
    have := ul2 SP SL N0 s c1 c2 hinP hgP (Uf inc A B f) (Uf inc A B f)
      ((Vf inc A B f).image a) (by
        intro w hw
        simp only [Finset.mem_image] at hw
        obtain ⟨t, ht, rfl⟩ := hw
        refine ⟨(ha t).1, (ha t).2.2, ?_⟩
        rw [(ha t).2.1]
        intro l hl
        simp only [Uf, Finset.mem_biUnion]
        exact ⟨t, ht, hl⟩)
    have e : Uf inc A B f ∩ ((Vf inc A B f).image a).biUnion SP = Uf inc A B f := by
      apply Finset.inter_eq_left.2
      intro l hl
      simp only [Uf, Finset.mem_biUnion] at hl
      obtain ⟨t, ht, hl⟩ := hl
      simp only [Finset.mem_biUnion, Finset.mem_image]
      exact ⟨a t, ⟨t, ht, rfl⟩, by rw [(ha t).2.1]; exact hl⟩
    rw [e] at this
    have := Finset.card_image_le (s := Vf inc A B f) (f := a)
    omega
  have hXS : XS.card ≤ CS.card := by
    have hsub : XS ⊆ CS.biUnion (fun t => A t ×ˢ B t) := by
      intro x hx
      simp only [XS, Finset.mem_filter] at hx
      obtain ⟨t, hA, hB⟩ := hx.2
      simp only [Finset.mem_biUnion, CS, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product]
      exact ⟨t, ⟨by rw [hA, Finset.card_singleton], by rw [hB, Finset.card_singleton]⟩,
        by rw [hA]; exact Finset.mem_singleton_self _, by rw [hB]; exact Finset.mem_singleton_self _⟩
    have h1 := Finset.card_biUnion_le_card_mul CS (fun t => A t ×ˢ B t) 1 (by
      intro t ht
      simp only [CS, Finset.mem_filter] at ht
      rw [Finset.card_product, ht.2.1, ht.2.2])
    have := Finset.card_le_card hsub
    omega
  have hJX : ∀ p l, (p, l) ∈ R → inc p l = true ∧ l ∉ Uq inc A B p := by
    intro p l h
    simp only [R, XR, Xs, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact ⟨h.1.1, h.2.1⟩
  have hβ : ∀ p, ∃ v : Fin k, (Finset.univ.filter (fun l => (p, l) ∈ R)).Nonempty →
      A v = {p} ∧ Finset.univ.filter (fun l => (p, l) ∈ R) ⊆ B v ∧ v ∈ CR := by
    intro p
    by_cases hne : (Finset.univ.filter (fun l => (p, l) ∈ R)).Nonempty
    · obtain ⟨l0, hl0⟩ := hne
      have hr0 : (p, l0) ∈ R := by simpa using hl0
      obtain ⟨v, hAv, hl0v, l', hl', hpl'⟩ := (res inc A B S1 S2 p l0 hr0).2
      refine ⟨v, fun _ => ⟨hAv, ?_, ?_⟩⟩
      · intro l hl
        have hr : (p, l) ∈ R := by simpa using hl
        obtain ⟨v', hAv', hlv', l'', hl'', hpl''⟩ := (res inc A B S1 S2 p l hr).2
        by_cases hvv : v = v'
        · rw [hvv]; exact hlv'
        · exact (S1 p v v' l' l'' hvv (by rw [hAv]; exact Finset.mem_singleton_self _)
            (by rw [hAv']; exact Finset.mem_singleton_self _) hl' hl'' hpl' hpl'').elim
      · simp only [CR, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨by rw [hAv, Finset.card_singleton], ?_, ?_⟩
        · have hi0 := (hJX p l0 hr0).1
          have : l0 ≠ l' := by
            intro h
            rw [h, hpl'] at hi0
            exact Bool.noConfusion hi0
          exact Finset.one_lt_card.2 ⟨l0, hl0v, l', hl', this⟩
        · intro q hq
          rw [hAv, Finset.mem_singleton] at hq
          subst hq
          exact ⟨l', hl', hpl'⟩
    · exact ⟨⟨0, hk⟩, fun h => absurd h hne⟩
  choose β hβ using hβ
  have hXR : R.card ≤ ∑ p, ((F SL SP N0 s (B (β p)) (Finset.univ.filter (fun l => (p, l) ∈ R))).card
      + if (Finset.univ.filter (fun l => (p, l) ∈ R)).Nonempty then 1 else 0) := by
    have hsub : R ⊆ Finset.univ.biUnion
        (fun p => (Finset.univ.filter (fun l => (p, l) ∈ R)).image (fun l => (p, l))) := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_filter]
      exact ⟨x.1, x.2, hx, rfl⟩
    refine le_trans (Finset.card_le_card hsub)
      (le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_))
    intro p _
    refine le_trans Finset.card_image_le ?_
    by_cases hne : (Finset.univ.filter (fun l => (p, l) ∈ R)).Nonempty
    · rw [if_pos hne]
      obtain ⟨hAv, hsub, hCR⟩ := hβ p hne
      have := ul2 SL SP N0 s c1 c2 hinL hgL (B (β p)) (Finset.univ.filter (fun l => (p, l) ∈ R))
        {b (β p)} (by
          intro w hw
          rw [Finset.mem_singleton] at hw
          subst hw
          exact ⟨(hb _).1, (hb _).2.1, (hb _).2.2.subset⟩)
      rw [Finset.singleton_biUnion, (hb _).2.2, Finset.inter_eq_left.2 hsub,
        Finset.card_singleton] at this
      exact this
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
      simp
  have hCRc : (∑ p : Fin n, if (Finset.univ.filter (fun l => (p, l) ∈ R)).Nonempty then 1 else 0)
      ≤ CR.card := by
    rw [← Finset.card_filter]
    apply Finset.card_le_card_of_injOn β
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      rw [Finset.mem_coe]
      exact (hβ p hp.2).2.2
    · intro p hp p' hp' he
      rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
      have h1 := (hβ p hp.2).1
      have h2 := (hβ p' hp'.2).1
      rw [he, h2] at h1
      exact (Finset.singleton_inj.1 h1).symm
  have hcl : ∀ p p' l, (Finset.univ.filter (fun l => (p, l) ∈ R)).Nonempty → (p', l) ∈ R →
      l ∈ B (β p) → inc p l = true := by
    intro p p' l hne hr hlB
    obtain ⟨u, hBu, -, q, hq, hql⟩ := (res inc A B S1 S2 p' l hr).1
    obtain ⟨hAv, -, hCRm⟩ := hβ p hne
    by_contra hc
    have hc' : inc p l = false := by simpa using hc
    have hne' : u ≠ β p := by
      intro h
      simp only [CR, Finset.mem_filter] at hCRm
      rw [← h, hBu, Finset.card_singleton] at hCRm
      omega
    exact S2 l u (β p) q p hne' (by rw [hBu]; exact Finset.mem_singleton_self _) hlB hq
      (by rw [hAv]; exact Finset.mem_singleton_self _) hql hc'
  set GA : Fin n → Finset ℕ := fun q => F SL SP N0 s (Uq inc A B q) (Uq inc A B q) with hGA
  set GB : Fin m → Finset ℕ := fun f => F SP SL N0 s (Uf inc A B f) (Uf inc A B f) with hGB
  set GR : Fin n → Finset ℕ := fun p =>
    F SL SP N0 s (B (β p)) (Finset.univ.filter (fun l => (p, l) ∈ R)) with hGR
  have dAA : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint GA := by
    intro q _ q' _ hqq'
    rw [Function.onFun, Finset.disjoint_left]
    intro g h1 h2
    simp only [GA, F, Finset.mem_filter] at h1 h2
    obtain ⟨x, y, hxy, hx, -, hy, -⟩ := two_of h1.2.2.2.2
    exact hlin q q' x y hqq' hxy (Uq_inc _ _ _ _ _ (h1.2.2.2.1.2 hx))
      (Uq_inc _ _ _ _ _ (h2.2.2.2.1.2 hx)) (Uq_inc _ _ _ _ _ (h1.2.2.2.1.2 hy))
      (Uq_inc _ _ _ _ _ (h2.2.2.2.1.2 hy))
  have dBB : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint GB := by
    intro f _ f' _ hff'
    rw [Function.onFun, Finset.disjoint_left]
    intro g h1 h2
    simp only [GB, F, Finset.mem_filter] at h1 h2
    obtain ⟨x, y, hxy, hx, -, hy, -⟩ := two_of h1.2.2.2.2
    exact hlin x y f f' hxy hff' (Uf_inc _ _ _ _ _ (h1.2.2.2.1.2 hx))
      (Uf_inc _ _ _ _ _ (h1.2.2.2.1.2 hy)) (Uf_inc _ _ _ _ _ (h2.2.2.2.1.2 hx))
      (Uf_inc _ _ _ _ _ (h2.2.2.2.1.2 hy))
  have dRR : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint GR := by
    intro p _ p' _ hpp'
    rw [Function.onFun, Finset.disjoint_left]
    intro g h1 h2
    simp only [GR, F, Finset.mem_filter] at h1 h2
    obtain ⟨z, -, -, -, hz, -, -⟩ := two_of h1.2.2.2.2
    have hne : (Finset.univ.filter (fun l => (p, l) ∈ R)).Nonempty := ⟨z, hz⟩
    obtain ⟨x, y, hxy, hx, hx', hy, hy'⟩ := two_of h2.2.2.2.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' hy'
    exact hlin p p' x y hpp' hxy (hcl p p' x hne hx' (h1.2.2.2.1.2 hx)) (hJX p' x hx').1
      (hcl p p' y hne hy' (h1.2.2.2.1.2 hy)) (hJX p' y hy').1
  have cA : (Finset.univ.biUnion GA).card =
      ∑ q, (F SL SP N0 s (Uq inc A B q) (Uq inc A B q)).card := Finset.card_biUnion dAA
  have cB : (Finset.univ.biUnion GB).card =
      ∑ f, (F SP SL N0 s (Uf inc A B f) (Uf inc A B f)).card := Finset.card_biUnion dBB
  have cR : (Finset.univ.biUnion GR).card =
      ∑ p, (F SL SP N0 s (B (β p)) (Finset.univ.filter (fun l => (p, l) ∈ R))).card :=
    Finset.card_biUnion dRR
  have d1 : Disjoint (Finset.univ.biUnion GA) (Finset.univ.biUnion GB) := by
    rw [Finset.disjoint_left]
    intro g h1 h2
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨q, h1⟩ := h1
    obtain ⟨f, h2⟩ := h2
    simp only [GA, GB, F, Finset.mem_filter] at h1 h2
    obtain ⟨x, y, -, hx, -, -, -⟩ := two_of h2.2.2.2.2
    rw [h1.2.2.2.1.1] at hx
    simp at hx
  have d2 : Disjoint (Finset.univ.biUnion GA ∪ Finset.univ.biUnion GB)
      (Finset.univ.biUnion GR) := by
    rw [Finset.disjoint_left]
    intro g h1 h2
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨p, h2⟩ := h2
    simp only [GR, F, Finset.mem_filter] at h2
    obtain ⟨x, y, hxy, hx, hx', hy, hy'⟩ := two_of h2.2.2.2.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' hy'
    rcases h1 with ⟨q, h1⟩ | ⟨f, h1⟩
    · simp only [GA, F, Finset.mem_filter] at h1
      have hxq := h1.2.2.2.1.2 hx
      have hyq := h1.2.2.2.1.2 hy
      by_cases hqp : q = p
      · subst hqp
        exact (hJX q x hx').2 hxq
      · exact hlin q p x y hqp hxy (Uq_inc _ _ _ _ _ hxq) (hJX p x hx').1
          (Uq_inc _ _ _ _ _ hyq) (hJX p y hy').1
    · simp only [GB, F, Finset.mem_filter] at h1
      rw [h1.2.2.2.1.1] at hx
      simp at hx
  have hsubI : Finset.univ.biUnion GA ∪ Finset.univ.biUnion GB ∪ Finset.univ.biUnion GR ⊆
      Finset.Ico N0 (N0 + s) := by
    intro g hg'
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hg'
    rw [Finset.mem_Ico]
    rcases hg' with (⟨q, h⟩ | ⟨q, h⟩) | ⟨q, h⟩
    · simp only [GA, F, Finset.mem_filter] at h
      exact ⟨h.2.1, h.2.2.1⟩
    · simp only [GB, F, Finset.mem_filter] at h
      exact ⟨h.2.1, h.2.2.1⟩
    · simp only [GR, F, Finset.mem_filter] at h
      exact ⟨h.2.1, h.2.2.1⟩
  have e1 := Finset.card_union_of_disjoint d1
  have e2 := Finset.card_union_of_disjoint d2
  have e3 := Finset.card_le_card hsubI
  rw [Nat.card_Ico] at e3
  have wA : (Finset.univ.biUnion (Wq inc A B)).card = ∑ q, (Wq inc A B q).card :=
    Finset.card_biUnion (by
      intro q _ q' _ hqq'
      rw [Function.onFun, Finset.disjoint_left]
      intro t h1 h2
      simp only [Wq, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by have := h1.1; omega : 1 < (B t).card)
      exact hlin q q' x y hqq' hxy (h1.2.2 x hx) (h2.2.2 x hx) (h1.2.2 y hy) (h2.2.2 y hy))
  have wB : (Finset.univ.biUnion (Vf inc A B)).card = ∑ f, (Vf inc A B f).card :=
    Finset.card_biUnion (by
      intro f _ f' _ hff'
      rw [Function.onFun, Finset.disjoint_left]
      intro t h1 h2
      simp only [Vf, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by have := h1.1; omega : 1 < (A t).card)
      exact hlin x y f f' hxy hff' (h1.2.2 x hx) (h1.2.2 y hy) (h2.2.2 x hx) (h2.2.2 y hy))
  rw [Finset.sum_add_distrib] at hXA hXB hXR
  omega

end

section
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepF, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem getD_foldl_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl stepF w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepF]; omega)]
    exact List.getD_append _ _ _ _ h

theorem wire_in (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_foldl_lt C.gates x i h

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (g : j < C.gates.length)
    (hr : ∀ i ∈ (gateAt C j).inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  let w := (C.gates.take j).foldl stepF x
  let b := C.gates.drop (j + 1)
  have c : C.gates = C.gates.take j ++ C.gates[j] :: b :=
    (List.take_append_drop j C.gates).symm.trans
      (congrArg (C.gates.take j ++ ·) (List.drop_eq_getElem_cons (l := C.gates) g))
  have e : w.length = x.length + j := by simp [w, len_foldl, Nat.min_eq_left g.le]
  have d : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ g
  have a : C.wires x = b.foldl stepF (stepF w C.gates[j]) := by
    show C.gates.foldl stepF x = _
    conv_lhs => rw [c]
    rw [List.foldl_append, List.foldl_cons]
  have hpre : ∀ i < x.length + j, w.getD i false = (C.wires x).getD i false := by
    intro i k
    rw [a, getD_foldl_lt b (stepF w C.gates[j]) i (by simp [stepF, e]; omega)]
    exact (List.getD_append w _ false i (by omega)).symm
  have hv : (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w.getD i false) := by
    rw [a, getD_foldl_lt b (stepF w C.gates[j]) (x.length + j) (by simp [stepF, e]), d]
    unfold stepF
    rw [List.getD_append_right _ _ _ _ (by omega), e, Nat.sub_self]
    rfl
  rw [hv]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hpre i (hr i hi)

theorem getD_ofFn_left (f : Fin n → Bool) (g : Fin m → Bool) (u : Fin n) :
    (List.ofFn f ++ List.ofFn g).getD u.val false = f u := by
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem getD_ofFn_right (f : Fin n → Bool) (g : Fin m → Bool) (v : Fin m) :
    (List.ofFn f ++ List.ofFn g).getD (n + v.val) false = g v := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem getD_ofFn_cases (f : Fin n → Bool) (g : Fin m → Bool) (w : ℕ) (hw : w < n + m) :
    (∃ u : Fin n, w = u.val ∧ (List.ofFn f ++ List.ofFn g).getD w false = f u) ∨
    (∃ v : Fin m, w = n + v.val ∧ (List.ofFn f ++ List.ofFn g).getD w false = g v) := by
  by_cases h : w < n
  · exact Or.inl ⟨⟨w, h⟩, rfl, getD_ofFn_left f g ⟨w, h⟩⟩
  · refine Or.inr ⟨⟨w - n, by omega⟩, by simp; omega, ?_⟩
    have := getD_ofFn_right f g ⟨w - n, by omega⟩
    simp only at this
    rw [show n + (w - n) = w by omega] at this
    exact this

end

end PEqualNP.Outside.L_meta_3063

theorem PEqualNP.Outside.L_meta_3063 : ∀ (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
  (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
  (∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
    inc p l' = true → inc p' l' = true → False) →
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  C.size = s + k + T → 1 ≤ k →
  (∀ j < s, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) →
  (∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).inputs = [a i, b i] ∧
    ∀ x : List Bool, x.length = n + m →
      ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
       (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true))) →
  (∀ x : List Bool, x.length = n + m →
    C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
      (C.wires x).getD (n + m + s + j1.val) false = true)) →
  (∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
    ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
    (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
    C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) →
  ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
    ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card ∧
  (k ≤ T + 1 →
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun r => inc r.1 r.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = r.1)) ++ List.ofFn (fun v : Fin m => decide (v = r.2))) = true)).card
    ≤ C.size + 1) := by
  intro n m inc C s k T a b A B hlin _hmono hrb hsize hk hor hrect hout hsound
  have hlen : ∀ (f : Fin n → Bool) (g : Fin m → Bool), (List.ofFn f ++ List.ofFn g).length = n + m := by
    intro f g
    simp
  have hgl : C.gates.length = s + k + T := hsize
  have hand : ∀ (f : Fin n → Bool) (g : Fin m → Bool) (i : Fin k),
      (C.wires (List.ofFn f ++ List.ofFn g)).getD (n + m + s + i.val) false =
      (decide (∃ pa ∈ A i, f pa = true) && decide (∃ lb ∈ B i, g lb = true)) := by
    intro f g i
    obtain ⟨_, _, _, _, hop, hin, hval⟩ := hrect i
    have hj : s + i.val < C.gates.length := by
      have := i.isLt
      omega
    have hw := PEqualNP.Outside.L_meta_3063.wire_gate C (List.ofFn f ++ List.ofFn g) (s + i.val) hj
      (by rw [hlen]; exact hrb _ hj)
    rw [hlen] at hw
    rw [show n + m + s + i.val = n + m + (s + i.val) by omega, hw, hop, hin]
    obtain ⟨h1, h2⟩ := hval _ (hlen f g)
    simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval, h1, h2,
      PEqualNP.Outside.L_meta_3063.getD_ofFn_left, PEqualNP.Outside.L_meta_3063.getD_ofFn_right]
    simp
  have heval : ∀ (f : Fin n → Bool) (g : Fin m → Bool),
      C.eval (List.ofFn f ++ List.ofFn g) = true ↔
      ∃ i j : Fin k, i ≠ j ∧ ((∃ pa ∈ A i, f pa = true) ∧ (∃ lb ∈ B i, g lb = true)) ∧
        ((∃ pa ∈ A j, f pa = true) ∧ (∃ lb ∈ B j, g lb = true)) := by
    intro f g
    rw [hout _ (hlen f g)]
    simp only [hand, decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨i, j, hij, h1, h2⟩
      exact ⟨i, j, ne_of_lt hij, h1, h2⟩
    · rintro ⟨i, j, hij, h1, h2⟩
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨i, j, h, h1, h2⟩
      · exact ⟨j, i, h, h2, h1⟩
  have S1 : ∀ (p : Fin n) (i j : Fin k) (l1 l2 : Fin m), i ≠ j → p ∈ A i → p ∈ A j →
      l1 ∈ B i → l2 ∈ B j → inc p l1 = false → inc p l2 = false → False := by
    intro p i j l1 l2 hij hpi hpj hl1 hl2 e1 e2
    have hs := hsound {p} {l1, l2} (Or.inl ⟨Finset.card_singleton p, Finset.card_le_two⟩) (by
      intro p' hp' l hl
      rw [Finset.mem_singleton] at hp'
      subst hp'
      rw [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl <;> assumption)
    have := (heval (fun u => decide (u ∈ ({p} : Finset (Fin n))))
      (fun v => decide (v ∈ ({l1, l2} : Finset (Fin m))))).2
      ⟨i, j, hij, ⟨⟨p, hpi, by simp⟩, ⟨l1, hl1, by simp⟩⟩, ⟨⟨p, hpj, by simp⟩, ⟨l2, hl2, by simp⟩⟩⟩
    rw [hs] at this
    exact Bool.noConfusion this
  have S2 : ∀ (l : Fin m) (i j : Fin k) (q1 q2 : Fin n), i ≠ j → l ∈ B i → l ∈ B j →
      q1 ∈ A i → q2 ∈ A j → inc q1 l = false → inc q2 l = false → False := by
    intro l i j q1 q2 hij hli hlj hq1 hq2 e1 e2
    have hs := hsound {q1, q2} {l} (Or.inr ⟨Finset.card_le_two, Finset.card_singleton l⟩) (by
      intro p' hp' l' hl'
      rw [Finset.mem_singleton] at hl'
      subst hl'
      rw [Finset.mem_insert, Finset.mem_singleton] at hp'
      rcases hp' with rfl | rfl <;> assumption)
    have := (heval (fun u => decide (u ∈ ({q1, q2} : Finset (Fin n))))
      (fun v => decide (v ∈ ({l} : Finset (Fin m))))).2
      ⟨i, j, hij, ⟨⟨q1, hq1, by simp⟩, ⟨l, hli, by simp⟩⟩, ⟨⟨q2, hq2, by simp⟩, ⟨l, hlj, by simp⟩⟩⟩
    rw [hs] at this
    exact Bool.noConfusion this
  let SP : ℕ → Finset (Fin n) := fun w => Finset.univ.filter (fun p =>
    (C.wires (List.ofFn (fun u : Fin n => decide (u = p)) ++ List.ofFn (fun _ : Fin m => false))).getD
      w false = true)
  let SL : ℕ → Finset (Fin m) := fun w => Finset.univ.filter (fun l =>
    (C.wires (List.ofFn (fun _ : Fin n => false) ++ List.ofFn (fun v : Fin m => decide (v = l)))).getD
      w false = true)
  let c1 : ℕ → ℕ := fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C (g - (n + m))).inputs.getD 0 0
  let c2 : ℕ → ℕ := fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C (g - (n + m))).inputs.getD 1 0
  have hor2 : ∀ (f : Fin n → Bool) (g : Fin m → Bool) (w : ℕ), n + m ≤ w → w < n + m + s →
      c1 w < w ∧ c2 w < w ∧ (C.wires (List.ofFn f ++ List.ofFn g)).getD w false =
      ((C.wires (List.ofFn f ++ List.ofFn g)).getD (c1 w) false ||
        (C.wires (List.ofFn f ++ List.ofFn g)).getD (c2 w) false) := by
    intro f g w h1 h2
    obtain ⟨hop, hl2⟩ := hor (w - (n + m)) (by omega)
    have hj : w - (n + m) < C.gates.length := by omega
    obtain ⟨x, y, hxy⟩ := List.length_eq_two.1 hl2
    have hr := hrb _ hj
    rw [hxy] at hr
    have hx : x < w := by have := hr x (by simp); omega
    have hy : y < w := by have := hr y (by simp); omega
    have hc1 : c1 w = x := by simp [c1, hxy]
    have hc2 : c2 w = y := by simp [c2, hxy]
    refine ⟨by rw [hc1]; exact hx, by rw [hc2]; exact hy, ?_⟩
    have hw := PEqualNP.Outside.L_meta_3063.wire_gate C (List.ofFn f ++ List.ofFn g) (w - (n + m)) hj
      (by rw [hlen]; exact hrb _ hj)
    rw [hlen, show n + m + (w - (n + m)) = w by omega, hop, hxy] at hw
    rw [hw, hc1, hc2]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have hg : ∀ g, n + m ≤ g → g < n + m + s → c1 g < g ∧ c2 g < g ∧
      SP g = SP (c1 g) ∪ SP (c2 g) ∧ SL g = SL (c1 g) ∪ SL (c2 g) := by
    intro g h1 h2
    obtain ⟨e1, e2, _⟩ := hor2 (fun _ => false) (fun _ => false) g h1 h2
    refine ⟨e1, e2, ?_, ?_⟩
    · ext p
      simp only [SP, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hor2 _ _ g h1 h2).2.2, Bool.or_eq_true]
    · ext l
      simp only [SL, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hor2 _ _ g h1 h2).2.2, Bool.or_eq_true]
  have hinP : ∀ w < n + m, (SP w).card ≤ 1 := by
    intro w hw
    rw [Finset.card_le_one]
    intro p1 hp1 p2 hp2
    simp only [SP, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    rw [PEqualNP.Outside.L_meta_3063.wire_in _ _ _ (by rw [hlen]; exact hw)] at hp1 hp2
    rcases PEqualNP.Outside.L_meta_3063.getD_ofFn_cases (fun _ : Fin n => false) (fun _ : Fin m => false) w hw
      with ⟨u, hu, -⟩ | ⟨v, hv, -⟩
    · subst hu
      rw [PEqualNP.Outside.L_meta_3063.getD_ofFn_left] at hp1 hp2
      simp only [decide_eq_true_eq] at hp1 hp2
      rw [← hp1, ← hp2]
    · subst hv
      rw [PEqualNP.Outside.L_meta_3063.getD_ofFn_right] at hp1
      exact Bool.noConfusion hp1
  have hinL : ∀ w < n + m, (SL w).card ≤ 1 := by
    intro w hw
    rw [Finset.card_le_one]
    intro p1 hp1 p2 hp2
    simp only [SL, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    rw [PEqualNP.Outside.L_meta_3063.wire_in _ _ _ (by rw [hlen]; exact hw)] at hp1 hp2
    rcases PEqualNP.Outside.L_meta_3063.getD_ofFn_cases (fun _ : Fin n => false) (fun _ : Fin m => false) w hw
      with ⟨u, hu, -⟩ | ⟨v, hv, -⟩
    · subst hu
      rw [PEqualNP.Outside.L_meta_3063.getD_ofFn_left] at hp1
      exact Bool.noConfusion hp1
    · subst hv
      rw [PEqualNP.Outside.L_meta_3063.getD_ofFn_right] at hp1 hp2
      simp only [decide_eq_true_eq] at hp1 hp2
      rw [← hp1, ← hp2]
  have ha : ∀ i, a i < n + m + s ∧ SP (a i) = A i ∧ SL (a i) = ∅ := by
    intro i
    obtain ⟨_, _, hai, _, _, _, hval⟩ := hrect i
    refine ⟨hai, ?_, ?_⟩
    · ext p
      simp only [SP, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hval _ (hlen _ _)).1]
      simp only [PEqualNP.Outside.L_meta_3063.getD_ofFn_left]
      simp
    · ext l
      simp only [SL, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hval _ (hlen _ _)).1]
      simp only [PEqualNP.Outside.L_meta_3063.getD_ofFn_left]
      simp
  have hb : ∀ i, b i < n + m + s ∧ SP (b i) = ∅ ∧ SL (b i) = B i := by
    intro i
    obtain ⟨_, _, _, hbi, _, _, hval⟩ := hrect i
    refine ⟨hbi, ?_, ?_⟩
    · ext p
      simp only [SP, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hval _ (hlen _ _)).2]
      simp only [PEqualNP.Outside.L_meta_3063.getD_ofFn_right]
      simp
    · ext l
      simp only [SL, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hval _ (hlen _ _)).2]
      simp only [PEqualNP.Outside.L_meta_3063.getD_ofFn_right]
      simp
  have hc := PEqualNP.Outside.L_meta_3063.core s (n + m) inc hlin A B hk SP SL c1 c2 a b hinP hinL hg ha hb S1 S2
  have hX : (Finset.univ.filter (fun q : Fin n × Fin m => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++
        List.ofFn (fun v : Fin m => decide (v = q.2))) = true)) = PEqualNP.Outside.L_meta_3063.Xs inc A B := by
    unfold PEqualNP.Outside.L_meta_3063.Xs
    apply Finset.filter_congr
    intro q _
    rw [heval]
    simp [and_assoc]
  rw [hX]
  refine ⟨hc, fun hkT => ?_⟩
  have hD := Finset.card_le_univ ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true)))
  rw [Fintype.card_fin] at hD
  have hsz : C.size = s + k + T := hsize
  omega
