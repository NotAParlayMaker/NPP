import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1619_aux

open PEqualNP.CircuitLowerBounds

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wval {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl wstep (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [wstep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem wval_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    wval [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold wval
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem wval_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    wval (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => wval gs x j)
      else wval gs x i := by
  unfold wval
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, wstep]
  have hl : (gs.foldl wstep (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem wval_old {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i ≠ n + gs.length) : wval (gs ++ [g]) x i = wval gs x i := by
  rw [wval_snoc, ite_eq_right hi]

theorem wval_new {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wval (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map fun j => wval gs x j) := by
  rw [wval_snoc, ite_eq_left rfl]

theorem wval_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (h : wval gs x i = true) : i < n + gs.length := by
  by_contra hc
  have hl : (gs.foldl wstep (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  unfold wval at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

theorem wval_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    wval gs x i = x ⟨i, h⟩ := by
  induction gs using List.reverseRecOn with
  | nil => rw [wval_nil, dite_eq_left h]
  | append_singleton gs g ih =>
    rw [wval_old gs g x i (by omega)]
    exact ih

theorem wval_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gs[k]? = some g) :
    wval gs x (n + k) =
      g.op.eval (g.inputs.map fun j => if j < n + k then wval gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g0 ih =>
    obtain ⟨hklt, hkg⟩ := List.getElem?_eq_some_iff.mp hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hklt
    by_cases hkl : k = gs.length
    · have hgg : g0 = g := by
        rw [hkl] at hk
        simpa using hk
      subst hgg
      rw [hkl, wval_new]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [ite_eq_left hj, wval_old gs g0 x j (by omega)]
      · rw [ite_eq_right hj]
        cases hv : wval gs x j with
        | false => rfl
        | true => exact absurd (wval_lt gs x j hv) hj
    · have hk' : gs[k]? = some g := by
        rw [List.getElem?_append_left (by omega)] at hk
        exact hk
      rw [wval_old gs g0 x (n + k) (by omega), ih hk']
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [ite_eq_left hj, ite_eq_left hj, wval_old gs g0 x j (by omega)]
      · rw [ite_eq_right hj, ite_eq_right hj]

def sx (u : Fin 13) : Fin 13 → Bool := fun v => decide (v = u)

def Pg (gs : List Gate) (k : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter fun u => wval gs (sx u) (13 + k) = true

def Av (P : ℕ → Finset (Fin 13)) (k : ℕ) (A : Finset (Fin 13)) : Prop :=
  A.card ≤ 1 ∨ ∃ c, c < k ∧ A = P c

def Es (gs : List Gate) (k j : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter fun u => (if j < 13 + k then wval gs (sx u) j else false) = true

theorem es_av (gs : List Gate) (k j : ℕ) : Av (Pg gs) k (Es gs k j) := by
  by_cases h1 : j < 13
  · left
    have hsub : Es gs k j ⊆ {⟨j, h1⟩} := by
      intro u hu
      simp only [Es, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [ite_eq_left (by omega), wval_input gs (sx u) j h1] at hu
      simp only [sx, decide_eq_true_eq] at hu
      rw [Finset.mem_singleton]
      exact hu.symm
    calc (Es gs k j).card ≤ ({⟨j, h1⟩} : Finset (Fin 13)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  · by_cases h2 : j < 13 + k
    · right
      refine ⟨j - 13, by omega, ?_⟩
      ext u
      simp only [Es, Pg, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ite_eq_left h2]
      have h3 : 13 + (j - 13) = j := by omega
      rw [h3]
    · left
      have h3 : Es gs k j = ∅ := by
        ext u
        simp [Es, h2]
      rw [h3]
      simp

theorem gp (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gs.length) :
    Pg gs k = Finset.univ ∨ ∃ A B, Av (Pg gs) k A ∧ Av (Pg gs) k B ∧
      (Pg gs k = A ∩ B ∨ Pg gs k = A ∪ B) := by
  have hget : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
  have hmem : gs[k] ∈ gs := List.getElem_mem hk
  obtain ⟨hop, hlen⟩ := hg _ hmem
  have hval : ∀ u : Fin 13, wval gs (sx u) (13 + k) = gs[k].op.eval
      (gs[k].inputs.map fun j => if j < 13 + k then wval gs (sx u) j else false) :=
    fun u => wval_gate gs (sx u) k gs[k] hget
  generalize gs[k] = g at hop hlen hval
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hval
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rcases hop with rfl | rfl
    · left
      ext u
      simp [Pg, hval, GateOp.eval]
    · right
      refine ⟨∅, ∅, Or.inl (by simp), Or.inl (by simp), Or.inl ?_⟩
      ext u
      simp [Pg, hval, GateOp.eval]
  · right
    refine ⟨Es gs k a, Es gs k a, es_av gs k a, es_av gs k a, Or.inl ?_⟩
    ext u
    rcases hop with rfl | rfl <;> simp [Pg, Es, hval, GateOp.eval]
  · right
    refine ⟨Es gs k a, Es gs k b, es_av gs k a, es_av gs k b, ?_⟩
    rcases hop with rfl | rfl
    · left
      ext u
      simp [Pg, Es, hval, GateOp.eval]
    · right
      ext u
      simp [Pg, Es, hval, GateOp.eval]
  · simp at hlen

theorem out_gate (gs : List Gate) (o : ℕ) (X : Finset (Fin 13)) (hX : 2 ≤ X.card)
    (ho : ∀ u : Fin 13, wval gs (sx u) o = true ↔ u ∈ X) :
    ∃ k, k < gs.length ∧ Pg gs k = X := by
  have h13 : 13 ≤ o := by
    by_contra hc
    have hlt : o < 13 := by omega
    have hsub : X ⊆ {⟨o, hlt⟩} := by
      intro u hu
      have h1 := (ho u).mpr hu
      rw [wval_input gs (sx u) o hlt] at h1
      simp only [sx, decide_eq_true_eq] at h1
      rw [Finset.mem_singleton]
      exact h1.symm
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h2
    omega
  obtain ⟨u, hu⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
  have hlt := wval_lt gs (sx u) o ((ho u).mpr hu)
  refine ⟨o - 13, by omega, ?_⟩
  ext v
  simp only [Pg, Finset.mem_filter, Finset.mem_univ, true_and]
  have h3 : 13 + (o - 13) = o := by omega
  rw [h3]
  exact ho v

def S1 (pts : Fin 13 → Finset (Fin 13)) (n : ℕ) (P : ℕ → Finset (Fin 13)) (l : Fin 13) :
    Finset ℕ :=
  (Finset.range n).filter fun k => 2 ≤ (P k).card ∧ P k ⊆ pts l

def S2 (n : ℕ) (P : ℕ → Finset (Fin 13)) : Finset ℕ :=
  (Finset.range n).filter fun k => 5 ≤ (P k).card ∧ (P k).card ≤ 12

theorem card_le13 (A : Finset (Fin 13)) : A.card ≤ 13 := by
  have h := Finset.card_le_univ A
  simpa using h

theorem dich (pts : Fin 13 → Finset (Fin 13)) (hcard : ∀ l, (pts l).card = 4)
    (n : ℕ) (P : ℕ → Finset (Fin 13))
    (hGP : ∀ k, k < n → P k = Finset.univ ∨ ∃ A B, Av P k A ∧ Av P k B ∧
      (P k = A ∩ B ∨ P k = A ∪ B))
    (l : Fin 13) (k : ℕ) (hk : k < n) (hPk : P k = pts l) :
    2 ≤ (S1 pts n P l).card ∨
      ∃ a b, a ∈ S2 n P ∧ b ∈ S2 n P ∧ a ≠ b ∧ P a ∩ P b = pts l := by
  have hkS : k ∈ S1 pts n P l := by
    simp only [S1, Finset.mem_filter, Finset.mem_range]
    refine ⟨hk, ?_, ?_⟩
    · rw [hPk, hcard]
      norm_num
    · rw [hPk]
  have two : ∀ c, c < k → 2 ≤ (P c).card → P c ⊆ pts l → 2 ≤ (S1 pts n P l).card := by
    intro c hc h2 hsub
    have hcS : c ∈ S1 pts n P l := by
      simp only [S1, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h2, hsub⟩
    have hne : c ≠ k := by omega
    have hsub2 : ({c, k} : Finset ℕ) ⊆ S1 pts n P l := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hcS
      · exact hkS
    calc 2 = ({c, k} : Finset ℕ).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub2
  rcases hGP k hk with hU | ⟨A, B, hA, hB, hAB | hAB⟩
  · exfalso
    have h13 : (P k).card = 13 := by
      rw [hU]
      simp
    rw [hPk, hcard] at h13
    omega
  · have hAsup : pts l ⊆ A := by
      rw [← hPk, hAB]
      exact Finset.inter_subset_left
    have hBsup : pts l ⊆ B := by
      rw [← hPk, hAB]
      exact Finset.inter_subset_right
    have hA4 : 4 ≤ A.card := by
      rw [← hcard l]
      exact Finset.card_le_card hAsup
    have hB4 : 4 ≤ B.card := by
      rw [← hcard l]
      exact Finset.card_le_card hBsup
    rcases hA with hA1 | ⟨a, ha, rfl⟩
    · omega
    rcases hB with hB1 | ⟨b, hb, rfl⟩
    · omega
    by_cases ha4 : (P a).card = 4
    · left
      have h1 : P a = pts l :=
        (Finset.eq_of_subset_of_card_le hAsup (by rw [ha4, hcard])).symm
      exact two a ha (by omega) (by rw [h1])
    by_cases hb4 : (P b).card = 4
    · left
      have h1 : P b = pts l :=
        (Finset.eq_of_subset_of_card_le hBsup (by rw [hb4, hcard])).symm
      exact two b hb (by omega) (by rw [h1])
    right
    have ha13 := card_le13 (P a)
    have hb13 := card_le13 (P b)
    have ha12 : (P a).card ≠ 13 := by
      intro h
      have hu : P a = Finset.univ := Finset.eq_univ_of_card _ (by simpa using h)
      apply hb4
      rw [hu, Finset.univ_inter] at hAB
      rw [← hAB, hPk, hcard]
    have hb12 : (P b).card ≠ 13 := by
      intro h
      have hu : P b = Finset.univ := Finset.eq_univ_of_card _ (by simpa using h)
      apply ha4
      rw [hu, Finset.inter_univ] at hAB
      rw [← hAB, hPk, hcard]
    have hab : a ≠ b := by
      rintro rfl
      apply ha4
      rw [Finset.inter_self] at hAB
      rw [← hAB, hPk, hcard]
    refine ⟨a, b, ?_, ?_, hab, ?_⟩
    · simp only [S2, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, by omega⟩
    · simp only [S2, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, by omega⟩
    · rw [← hAB, hPk]
  · left
    have hAsub : A ⊆ pts l := by
      rw [← hPk, hAB]
      exact Finset.subset_union_left
    have hBsub : B ⊆ pts l := by
      rw [← hPk, hAB]
      exact Finset.subset_union_right
    have hsum : 4 ≤ A.card + B.card := by
      have h1 := Finset.card_union_le A B
      rw [← hAB, hPk, hcard] at h1
      exact h1
    by_cases hA2 : 2 ≤ A.card
    · rcases hA with hA1 | ⟨a, ha, rfl⟩
      · omega
      · exact two a ha hA2 hAsub
    · have hB2 : 2 ≤ B.card := by omega
      rcases hB with hB1 | ⟨b, hb, rfl⟩
      · omega
      · exact two b hb hB2 hBsub

theorem gate_zero (n : ℕ) (P : ℕ → Finset (Fin 13))
    (hGP : ∀ k, k < n → P k = Finset.univ ∨ ∃ A B, Av P k A ∧ Av P k B ∧
      (P k = A ∩ B ∨ P k = A ∪ B))
    (hn : 0 < n) : (P 0).card = 13 ∨ (P 0).card ≤ 2 := by
  rcases hGP 0 hn with hU | ⟨A, B, hA, hB, hAB | hAB⟩
  · left
    rw [hU]
    simp
  · right
    have hA1 : A.card ≤ 1 := by
      rcases hA with h | ⟨c, hc, -⟩
      · exact h
      · omega
    have h1 := Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
    rw [hAB]
    omega
  · right
    have hA1 : A.card ≤ 1 := by
      rcases hA with h | ⟨c, hc, -⟩
      · exact h
      · omega
    have hB1 : B.card ≤ 1 := by
      rcases hB with h | ⟨c, hc, -⟩
      · exact h
      · omega
    have h1 := Finset.card_union_le A B
    rw [hAB]
    omega

theorem sum_ge (B : Finset (Fin 13)) (f : Fin 13 → ℕ) (hf : ∀ l, 1 ≤ f l) :
    (B.filter (fun l => ¬ 2 ≤ f l)).card + 2 * (B.filter (fun l => 2 ≤ f l)).card
      ≤ ∑ l ∈ B, f l := by
  have h1 : ∑ l ∈ B, (if 2 ≤ f l then 2 else 1) ≤ ∑ l ∈ B, f l := by
    apply Finset.sum_le_sum
    intro l _
    split_ifs with h
    · exact h
    · exact hf l
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at h1
  omega

def pairMap (fa fb : Fin 13 → ℕ) (q : Fin 13 × Bool) : ℕ × ℕ :=
  cond q.2 (fa q.1, fb q.1) (fb q.1, fa q.1)

theorem pair_count (pts : Fin 13 → Finset (Fin 13))
    (hinj : ∀ l l', pts l = pts l' → l = l')
    (P : ℕ → Finset (Fin 13)) (W : Finset ℕ) (B1 : Finset (Fin 13))
    (hpair : ∀ l ∈ B1, ∃ a b, a ∈ W ∧ b ∈ W ∧ a ≠ b ∧ P a ∩ P b = pts l) :
    2 * B1.card + W.card ≤ W.card * W.card := by
  have hex : ∀ l : Fin 13, ∃ a b : ℕ, l ∈ B1 →
      (a ∈ W ∧ b ∈ W ∧ a ≠ b ∧ P a ∩ P b = pts l) := by
    intro l
    by_cases hl : l ∈ B1
    · obtain ⟨a, b, h⟩ := hpair l hl
      exact ⟨a, b, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hl⟩
  choose fa fb hf using hex
  have hmaps : ∀ q ∈ B1 ×ˢ (Finset.univ : Finset Bool), pairMap fa fb q ∈ W.offDiag := by
    rintro ⟨l, s⟩ hq
    have hl : l ∈ B1 := (Finset.mem_product.mp hq).1
    obtain ⟨ha, hb, hab, -⟩ := hf l hl
    rw [Finset.mem_offDiag]
    cases s
    · exact ⟨hb, ha, fun h => hab h.symm⟩
    · exact ⟨ha, hb, hab⟩
  have hinjOn : Set.InjOn (pairMap fa fb)
      ((B1 ×ˢ (Finset.univ : Finset Bool) : Finset (Fin 13 × Bool)) : Set (Fin 13 × Bool)) := by
    rintro ⟨l, s⟩ hq ⟨l', s'⟩ hq' heq
    have hl : l ∈ B1 := (Finset.mem_product.mp (Finset.mem_coe.mp hq)).1
    have hl' : l' ∈ B1 := (Finset.mem_product.mp (Finset.mem_coe.mp hq')).1
    obtain ⟨-, -, hab, hP⟩ := hf l hl
    obtain ⟨-, -, hab', hP'⟩ := hf l' hl'
    have hll : l = l' := by
      apply hinj
      rw [← hP, ← hP']
      cases s <;> cases s'
      · have h1 : (fb l, fa l) = (fb l', fa l') := heq
        rw [Prod.mk.injEq] at h1
        rw [h1.1, h1.2]
      · have h1 : (fb l, fa l) = (fa l', fb l') := heq
        rw [Prod.mk.injEq] at h1
        rw [h1.1, h1.2, Finset.inter_comm]
      · have h1 : (fa l, fb l) = (fb l', fa l') := heq
        rw [Prod.mk.injEq] at h1
        rw [h1.1, h1.2, Finset.inter_comm]
      · have h1 : (fa l, fb l) = (fa l', fb l') := heq
        rw [Prod.mk.injEq] at h1
        rw [h1.1, h1.2]
    subst hll
    cases s <;> cases s'
    · rfl
    · have h1 : (fb l, fa l) = (fa l, fb l) := heq
      rw [Prod.mk.injEq] at h1
      exact absurd h1.1.symm hab
    · have h1 : (fa l, fb l) = (fb l, fa l) := heq
      rw [Prod.mk.injEq] at h1
      exact absurd h1.1 hab
    · rfl
  have h1 := Finset.card_le_card_of_injOn (pairMap fa fb) hmaps hinjOn
  rw [Finset.card_product, Finset.offDiag_card, Finset.card_univ, Fintype.card_bool] at h1
  have h2 : W.card ≤ W.card * W.card := Nat.le_mul_self _
  omega

theorem arith (m o w h u n b : ℕ) (h1 : m + o = b) (h2 : b ≤ 13) (h3 : m + 2 * o ≤ u)
    (h4 : h + u + w ≤ n) (h5 : 2 * m + w ≤ w * w) (h6 : m = 13 → h + u + w + 1 ≤ n) :
    3 * b + 2 * h ≤ 2 * n := by
  by_cases hw : w ≤ 6
  · by_cases hm : m = 13
    · have h7 := h6 hm
      interval_cases w <;> omega
    · interval_cases w <;> omega
  · omega

theorem count_main (pts : Fin 13 → Finset (Fin 13))
    (hcard : ∀ l, (pts l).card = 4)
    (huniq : ∀ (X : Finset (Fin 13)) (l l' : Fin 13), 2 ≤ X.card → X ⊆ pts l → X ⊆ pts l' →
      l = l')
    (n : ℕ) (P : ℕ → Finset (Fin 13))
    (hGP : ∀ k, k < n → P k = Finset.univ ∨ ∃ A B, Av P k A ∧ Av P k B ∧
      (P k = A ∩ B ∨ P k = A ∪ B))
    (hout : ∀ l, ∃ k, k < n ∧ P k = pts l)
    (B : Finset (Fin 13)) (H : Finset ℕ) (hHn : H ⊆ Finset.range n)
    (hH : ∀ k ∈ H, 2 ≤ (P k).card ∧ ∃ l, l ∉ B ∧ P k ⊆ pts l) :
    3 * B.card + 2 * H.card ≤ 2 * n := by
  have d11 : ∀ l l', l ≠ l' → Disjoint (S1 pts n P l) (S1 pts n P l') := by
    intro l l' hne
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [S1, Finset.mem_filter, Finset.mem_range] at hk hk'
    exact hne (huniq (P k) l l' hk.2.1 hk.2.2 hk'.2.2)
  have d1H : ∀ l ∈ B, Disjoint (S1 pts n P l) H := by
    intro l hl
    rw [Finset.disjoint_left]
    intro k hk hkH
    simp only [S1, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨-, l', hl', hsub⟩ := hH k hkH
    have h1 := huniq (P k) l l' hk.2.1 hk.2.2 hsub
    exact hl' (h1 ▸ hl)
  have d12 : ∀ l, Disjoint (S1 pts n P l) (S2 n P) := by
    intro l
    rw [Finset.disjoint_left]
    intro k hk hk2
    simp only [S1, S2, Finset.mem_filter, Finset.mem_range] at hk hk2
    have h1 := Finset.card_le_card hk.2.2
    rw [hcard] at h1
    omega
  have dH2 : Disjoint H (S2 n P) := by
    rw [Finset.disjoint_left]
    intro k hkH hk2
    simp only [S2, Finset.mem_filter, Finset.mem_range] at hk2
    obtain ⟨-, l', -, hsub⟩ := hH k hkH
    have h1 := Finset.card_le_card hsub
    rw [hcard] at h1
    omega
  have hU1card : (B.biUnion (S1 pts n P)).card = ∑ l ∈ B, (S1 pts n P l).card :=
    Finset.card_biUnion (fun l _ l' _ hne => d11 l l' hne)
  have dHU1 : Disjoint H (B.biUnion (S1 pts n P)) := by
    rw [Finset.disjoint_biUnion_right]
    intro l hl
    exact (d1H l hl).symm
  have dU2 : Disjoint (H ∪ B.biUnion (S1 pts n P)) (S2 n P) := by
    rw [Finset.disjoint_union_left]
    refine ⟨dH2, ?_⟩
    rw [Finset.disjoint_biUnion_left]
    intro l _
    exact d12 l
  have hsubR : (H ∪ B.biUnion (S1 pts n P)) ∪ S2 n P ⊆ Finset.range n := by
    intro k hk
    simp only [Finset.mem_union] at hk
    rcases hk with (hk | hk) | hk
    · exact hHn hk
    · rw [Finset.mem_biUnion] at hk
      obtain ⟨l, -, hk⟩ := hk
      exact (Finset.mem_filter.mp hk).1
    · exact (Finset.mem_filter.mp hk).1
  have hcardU : ((H ∪ B.biUnion (S1 pts n P)) ∪ S2 n P).card =
      H.card + (B.biUnion (S1 pts n P)).card + (S2 n P).card := by
    rw [Finset.card_union_of_disjoint dU2, Finset.card_union_of_disjoint dHU1]
  have htot : H.card + (B.biUnion (S1 pts n P)).card + (S2 n P).card ≤ n := by
    rw [← hcardU]
    have h1 := Finset.card_le_card hsubR
    rwa [Finset.card_range] at h1
  have hBsplit : (B.filter (fun l => ¬ 2 ≤ (S1 pts n P l).card)).card +
      (B.filter (fun l => 2 ≤ (S1 pts n P l).card)).card = B.card := by
    rw [add_comm]
    exact Finset.card_filter_add_card_filter_not _
  have hB13 : B.card ≤ 13 := card_le13 B
  have hkS : ∀ l k, k < n → P k = pts l → k ∈ S1 pts n P l := by
    intro l k hk hPk
    simp only [S1, Finset.mem_filter, Finset.mem_range]
    refine ⟨hk, ?_, ?_⟩
    · rw [hPk, hcard]
      norm_num
    · rw [hPk]
  have hS1pos : ∀ l, 1 ≤ (S1 pts n P l).card := by
    intro l
    obtain ⟨k, hk, hPk⟩ := hout l
    exact Finset.card_pos.mpr ⟨k, hkS l k hk hPk⟩
  have hU1ge := sum_ge B (fun l => (S1 pts n P l).card) hS1pos
  rw [← hU1card] at hU1ge
  have hpair : ∀ l ∈ B.filter (fun l => ¬ 2 ≤ (S1 pts n P l).card),
      ∃ a b, a ∈ S2 n P ∧ b ∈ S2 n P ∧ a ≠ b ∧ P a ∩ P b = pts l := by
    intro l hl
    rw [Finset.mem_filter] at hl
    obtain ⟨k, hk, hPk⟩ := hout l
    rcases dich pts hcard n P hGP l k hk hPk with h | h
    · exact absurd h hl.2
    · exact h
  have hinj : ∀ l l', pts l = pts l' → l = l' := by
    intro l l' h
    refine huniq (pts l) l l' ?_ (Finset.Subset.refl _) ?_
    · rw [hcard]
      norm_num
    · rw [h]
  have hpc := pair_count pts hinj P (S2 n P) _ hpair
  have hspecial : (B.filter (fun l => ¬ 2 ≤ (S1 pts n P l).card)).card = 13 →
      H.card + (B.biUnion (S1 pts n P)).card + (S2 n P).card + 1 ≤ n := by
    intro h13
    have hB1univ : B.filter (fun l => ¬ 2 ≤ (S1 pts n P l).card) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h13)
    have hall : ∀ l, l ∈ B ∧ ¬ 2 ≤ (S1 pts n P l).card := by
      intro l
      have h1 : l ∈ B.filter (fun l => ¬ 2 ≤ (S1 pts n P l).card) := by
        rw [hB1univ]
        exact Finset.mem_univ l
      rw [Finset.mem_filter] at h1
      exact h1
    obtain ⟨k0, hk0, -⟩ := hout 0
    have hn : 0 < n := by omega
    have h0 := gate_zero n P hGP hn
    have h0H : (0 : ℕ) ∉ H := by
      intro h
      obtain ⟨-, l, hl, -⟩ := hH 0 h
      exact hl (hall l).1
    have h0U1 : (0 : ℕ) ∉ B.biUnion (S1 pts n P) := by
      intro h
      rw [Finset.mem_biUnion] at h
      obtain ⟨l, -, h0l⟩ := h
      obtain ⟨k, hk, hPk⟩ := hout l
      have hne : (0 : ℕ) ≠ k := by
        rintro rfl
        rw [hPk, hcard] at h0
        omega
      apply (hall l).2
      have hsub2 : ({0, k} : Finset ℕ) ⊆ S1 pts n P l := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h0l
        · exact hkS l _ hk hPk
      calc 2 = ({0, k} : Finset ℕ).card := (Finset.card_pair hne).symm
        _ ≤ _ := Finset.card_le_card hsub2
    have h0S2 : (0 : ℕ) ∉ S2 n P := by
      intro h
      simp only [S2, Finset.mem_filter, Finset.mem_range] at h
      omega
    have h0not : (0 : ℕ) ∉ (H ∪ B.biUnion (S1 pts n P)) ∪ S2 n P := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨h0H, h0U1⟩, h0S2⟩
    have hsub' : insert 0 ((H ∪ B.biUnion (S1 pts n P)) ∪ S2 n P) ⊆ Finset.range n := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_range.mpr hn
      · exact hsubR hx
    have h1 := Finset.card_le_card hsub'
    rw [Finset.card_insert_of_notMem h0not, hcardU, Finset.card_range] at h1
    exact h1
  exact arith _ _ _ _ _ _ _ hBsplit hB13 hU1ge htot hpc hspecial

end PEqualNP.Outside.L_meta_1619_aux

theorem PEqualNP.Outside.L_meta_1619 : ∀ (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4) → (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (l2 u2 : Fin 13), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2) → ∀ (B : Finset (Fin 13)) (H : Finset (Fin gates.length)), (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin 13 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧ ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) → 3 * B.card + 2 * H.card ≤ 2 * gates.length := by
  intro I _ gates out hI4 hI2 hg hout B H hH
  have huniq : ∀ (X : Finset (Fin 13)) (l l' : Fin 13), 2 ≤ X.card →
      X ⊆ Finset.univ.filter (fun p : Fin 13 => I p l) →
      X ⊆ Finset.univ.filter (fun p : Fin 13 => I p l') → l = l' := by
    intro X l l' hX hl hl'
    obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
    have h1 := (Finset.mem_filter.mp (hl hp1)).2
    have h2 := (Finset.mem_filter.mp (hl hp2)).2
    have h1' := (Finset.mem_filter.mp (hl' hp1)).2
    have h2' := (Finset.mem_filter.mp (hl' hp2)).2
    exact (hI2 p1 p2 hne).unique ⟨h1, h2⟩ ⟨h1', h2'⟩
  have hout' : ∀ l : Fin 13, ∃ k, k < gates.length ∧
      PEqualNP.Outside.L_meta_1619_aux.Pg gates k = Finset.univ.filter (fun p : Fin 13 => I p l) := by
    intro l
    apply PEqualNP.Outside.L_meta_1619_aux.out_gate gates (out l) _ (by rw [hI4]; norm_num)
    intro u
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact hout l u
  have hH' : ∀ k ∈ H.image Fin.val, 2 ≤ (PEqualNP.Outside.L_meta_1619_aux.Pg gates k).card ∧
      ∃ l, l ∉ B ∧ PEqualNP.Outside.L_meta_1619_aux.Pg gates k ⊆ Finset.univ.filter (fun p : Fin 13 => I p l) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨k5, hk5, rfl⟩ := hk
    obtain ⟨h2, l4, hl4, hsub⟩ := hH k5 hk5
    refine ⟨h2, l4, hl4, ?_⟩
    intro u hu
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hsub u (Finset.mem_filter.mp hu).2⟩
  have hHn : H.image Fin.val ⊆ Finset.range gates.length := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨k5, -, rfl⟩ := hk
    exact Finset.mem_range.mpr k5.isLt
  have hHc : (H.image Fin.val).card = H.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have hmain := PEqualNP.Outside.L_meta_1619_aux.count_main (fun l => Finset.univ.filter (fun p : Fin 13 => I p l)) hI4 huniq
    gates.length (PEqualNP.Outside.L_meta_1619_aux.Pg gates) (fun k hk => PEqualNP.Outside.L_meta_1619_aux.gp gates hg k hk) hout' B (H.image Fin.val) hHn hH'
  rw [hHc] at hmain
  exact hmain
