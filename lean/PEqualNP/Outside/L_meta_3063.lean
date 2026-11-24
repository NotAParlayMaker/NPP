import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3063_aux
open PEqualNP.CircuitLowerBounds

-- evaluation toolkit (step, val, val_gate) copied from L_meta_2868, ga / val_ga from L_meta_2855
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

def ga (G : List Gate) (j : ℕ) : Gate := G.getD j ⟨GateOp.or, []⟩

lemma ga_lt (G : List Gate) (j : ℕ) (hj : j < G.length) : ga G j = G[j] := by
  unfold ga
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma ga_ge (G : List Gate) (j : ℕ) (hj : G.length ≤ j) : ga G j = ⟨GateOp.or, []⟩ := by
  unfold ga
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
  rfl

lemma val_ga {n : ℕ} (G : List Gate) (x : Fin n → Bool) (k : ℕ) :
    val G x (n + k) =
      (ga G k).op.eval ((ga G k).inputs.map fun j => if j < n + k then val G x j else false) := by
  by_cases hk : k < G.length
  · rw [ga_lt G k hk]
    exact val_gate G x k hk
  · rw [ga_ge G k (by omega), val_ge G x _ (by omega)]
    rfl

lemma ev_and2 (f : ℕ → Bool) (a b : ℕ) : GateOp.and.eval ([a, b].map f) = (f a && f b) := by
  simp [GateOp.eval]

lemma ev_or2 (f : ℕ → Bool) (a b : ℕ) : GateOp.or.eval ([a, b].map f) = (f a || f b) := by
  simp [GateOp.eval]



-- combinatorial side: supports of the OR wires, rectangles, incidence
structure Side (n m k : ℕ) where
  inc : Fin n → Fin m → Bool
  N : ℕ
  s : ℕ
  SP : ℕ → Finset (Fin n)
  SL : ℕ → Finset (Fin m)
  A : Fin k → Finset (Fin n)
  B : Fin k → Finset (Fin m)

def Side.dual {n m k : ℕ} (D : Side n m k) : Side m n k :=
  ⟨fun l p => D.inc p l, D.N, D.s, D.SL, D.SP, D.B, D.A⟩

structure OK {n m k : ℕ} (D : Side n m k) : Prop where
  c4 : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → D.inc p l = true → D.inc p' l = true →
    D.inc p l' = true → D.inc p' l' = true → False
  gate : ∀ j, j < D.s → ∃ u v, u < D.N + j ∧ v < D.N + j ∧
    D.SP (D.N + j) = D.SP u ∪ D.SP v ∧ D.SL (D.N + j) = D.SL u ∪ D.SL v
  inP : ∀ w, w < D.N → (D.SP w).card ≤ 1
  aw : ∀ t, ∃ w, w < D.N + D.s ∧ D.SP w = D.A t ∧ D.SL w = ∅
  meet : ∀ i j : Fin k, i ≠ j → ∀ p, p ∈ D.A i → p ∈ D.A j →
    (∀ l ∈ D.B i, D.inc p l = true) ∨ (∀ l ∈ D.B j, D.inc p l = true)

variable {n m k : ℕ} {D : Side n m k}

lemma line_eq (h : OK D) {x y : Fin n} {l l' : Fin m} (hxy : x ≠ y) (h1 : D.inc x l = true)
    (h2 : D.inc y l = true) (h3 : D.inc x l' = true) (h4 : D.inc y l' = true) : l = l' := by
  by_contra hl
  exact h.c4 x y l l' hxy hl h1 h2 h3 h4

lemma pt_eq (h : OK D) {x y : Fin n} {l l' : Fin m} (hl : l ≠ l') (h1 : D.inc x l = true)
    (h2 : D.inc x l' = true) (h3 : D.inc y l = true) (h4 : D.inc y l' = true) : x = y := by
  by_contra hxy
  exact h.c4 x y l l' hxy hl h1 h3 h2 h4

def MinK {α : Type} (κ : α → ℕ) (x : α) (S : Finset α) : Prop := ∀ y ∈ S, κ x ≤ κ y

lemma mink_small {α : Type} (κ : α → ℕ) (x : α) (S : Finset α) (hc : S.card ≤ 1) (hx : x ∈ S) :
    MinK κ x S := by
  intro y hy
  rw [Finset.card_le_one] at hc
  rw [hc y hy x hx]

lemma split {α : Type} [DecidableEq α] (κ : α → ℕ) (S1 S2 S : Finset α) (hS : S = S1 ∪ S2) (x : α)
    (hx : x ∈ S) (hn : ¬ MinK κ x S) (h1 : x ∈ S1 → MinK κ x S1) (h2 : x ∈ S2 → MinK κ x S2) :
    ∃ q, κ q < κ x ∧ ((x ∈ S1 ∧ x ∉ S2 ∧ q ∈ S2 ∧ q ∉ S1) ∨ (x ∈ S2 ∧ x ∉ S1 ∧ q ∈ S1 ∧ q ∉ S2)) := by
  unfold MinK at hn
  push_neg at hn
  obtain ⟨q, hq, hlt⟩ := hn
  subst hS
  have hq' := Finset.mem_union.mp hq
  have hx' := Finset.mem_union.mp hx
  refine ⟨q, hlt, ?_⟩
  have a1 : x ∈ S1 → q ∉ S1 := fun hx1 hq1 => absurd (h1 hx1 q hq1) (by omega)
  have a2 : x ∈ S2 → q ∉ S2 := fun hx2 hq2 => absurd (h2 hx2 q hq2) (by omega)
  by_cases c1 : x ∈ S1
  · have q1 := a1 c1
    have q2 : q ∈ S2 := by tauto
    have c2 : x ∉ S2 := fun c2 => a2 c2 q2
    exact Or.inl ⟨c1, c2, q2, q1⟩
  · have c2 : x ∈ S2 := by tauto
    have q2 := a2 c2
    have q1 : q ∈ S1 := by tauto
    exact Or.inr ⟨c2, c1, q1, q2⟩

lemma first_inj {α : Type} [DecidableEq α] (κ : α → ℕ) (hκ : Function.Injective κ)
    (S1 S2 S : Finset α) (hS : S = S1 ∪ S2) (x y : α)
    (hx : x ∈ S) (hnx : ¬ MinK κ x S) (hx1 : x ∈ S1 → MinK κ x S1) (hx2 : x ∈ S2 → MinK κ x S2)
    (hy : y ∈ S) (hny : ¬ MinK κ y S) (hy1 : y ∈ S1 → MinK κ y S1) (hy2 : y ∈ S2 → MinK κ y S2) :
    x = y := by
  obtain ⟨q, hq, hc⟩ := split κ S1 S2 S hS x hx hnx hx1 hx2
  obtain ⟨r, hr, hd⟩ := split κ S1 S2 S hS y hy hny hy1 hy2
  apply hκ
  rcases hc with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ <;>
    rcases hd with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩
  · have e1 := hx1 a1 y b1
    have e2 := hy1 b1 x a1
    omega
  · have e1 := hy2 b1 q a3
    have e2 := hx1 a1 r b3
    omega
  · have e1 := hx2 a1 r b3
    have e2 := hy1 b1 q a3
    omega
  · have e1 := hx2 a1 y b1
    have e2 := hy2 b1 x a1
    omega

def vk {n : ℕ} (x : Fin n) : ℕ := x.val

lemma vk_inj {n : ℕ} : Function.Injective (vk : Fin n → ℕ) := fun _ _ h => Fin.ext h

def kap (D : Side n m k) (l : Fin m) (x : Fin n) : ℕ := if D.inc x l = true then x.val else n + x.val

lemma kap_inj (D : Side n m k) (l : Fin m) : Function.Injective (kap D l) := by
  intro x y hxy
  unfold kap at hxy
  have hx := x.isLt
  have hy := y.isLt
  apply Fin.ext
  split_ifs at hxy <;> omega

def RowG (D : Side n m k) (l : Fin m) (w : ℕ) : Prop :=
  D.SL w = ∅ ∧ 2 ≤ (D.SP w).card ∧ ∀ x ∈ D.SP w, D.inc x l = true

def NoC (D : Side n m k) (p : Fin n) (l : Fin m) : Prop :=
  ∀ j, j < D.s → RowG D l (D.N + j) → p ∈ D.SP (D.N + j) → MinK vk p (D.SP (D.N + j))

def HI (D : Side n m k) (j : ℕ) (p : Fin n) (l : Fin m) : Prop :=
  RowG D l (D.N + j) ∧ p ∈ D.SP (D.N + j) ∧ ¬ MinK vk p (D.SP (D.N + j)) ∧
  ∀ j', j' < j → RowG D l (D.N + j') → p ∈ D.SP (D.N + j') → MinK vk p (D.SP (D.N + j'))

def WG (D : Side n m k) (i : Fin k) (w : ℕ) : Prop :=
  D.SL w = ∅ ∧ D.SP w ⊆ D.A i ∧ ∀ l : Fin m, ¬ ∀ x ∈ D.SP w, D.inc x l = true

def HVg (D : Side n m k) (j : ℕ) (p : Fin n) (l : Fin m) (i : Fin k) : Prop :=
  D.B i = {l} ∧ D.inc p l = true ∧ NoC D p l ∧ WG D i (D.N + j) ∧ p ∈ D.SP (D.N + j) ∧
    ¬ MinK (kap D l) p (D.SP (D.N + j)) ∧
    ∀ j', j' < j → WG D i (D.N + j') → p ∈ D.SP (D.N + j') → MinK (kap D l) p (D.SP (D.N + j'))

def HVr (D : Side n m k) (t : Fin k) (p : Fin n) (l : Fin m) : Prop :=
  D.B t = {l} ∧ p ∈ D.A t ∧ D.inc p l = true ∧ (¬ ∀ g ∈ D.A t, D.inc g l = true) ∧
    ∀ y ∈ D.A t, D.inc y l = true → p ≤ y

def HS (D : Side n m k) (t : Fin k) (p : Fin n) (l : Fin m) : Prop :=
  2 ≤ (D.A t).card ∧ (∀ g ∈ D.A t, D.inc g l = true) ∧ p ∈ D.A t ∧ l ∈ D.B t ∧ ∀ y ∈ D.A t, p ≤ y

lemma preI (h : OK D) (j : ℕ) (p : Fin n) (l : Fin m) (hr : RowG D l (D.N + j))
    (hf : ∀ j', j' < j → RowG D l (D.N + j') → p ∈ D.SP (D.N + j') → MinK vk p (D.SP (D.N + j')))
    (w : ℕ) (hw : w < D.N + j) (hP : D.SP w ⊆ D.SP (D.N + j)) (hL : D.SL w ⊆ D.SL (D.N + j))
    (hp : p ∈ D.SP w) : MinK vk p (D.SP w) := by
  by_cases hc : (D.SP w).card ≤ 1
  · exact mink_small _ _ _ hc hp
  · by_cases hwN : w < D.N
    · exact absurd (h.inP w hwN) hc
    · obtain ⟨j', rfl⟩ : ∃ j', w = D.N + j' := ⟨w - D.N, by omega⟩
      refine hf j' (by omega) ⟨?_, by omega, fun x hx => hr.2.2 x (hP hx)⟩ hp
      rw [hr.1] at hL
      exact Finset.subset_empty.mp hL

lemma HI_inj (h : OK D) (j : ℕ) (hj : j < D.s) (p p' : Fin n) (l l' : Fin m)
    (h1 : HI D j p l) (h2 : HI D j p' l') : p = p' ∧ l = l' := by
  obtain ⟨r1, m1, n1, f1⟩ := h1
  obtain ⟨r2, m2, n2, f2⟩ := h2
  have hl : l = l' := by
    obtain ⟨x, hx, y, hy, hxy⟩ := (Finset.one_lt_card (s := D.SP (D.N + j))).mp
      (by have := r1.2.1; omega)
    exact line_eq h hxy (r1.2.2 x hx) (r1.2.2 y hy) (r2.2.2 x hx) (r2.2.2 y hy)
  subst hl
  obtain ⟨u, v, hu, hv, hP, hL⟩ := h.gate j hj
  have su : D.SP u ⊆ D.SP (D.N + j) := by rw [hP]; exact Finset.subset_union_left
  have sv : D.SP v ⊆ D.SP (D.N + j) := by rw [hP]; exact Finset.subset_union_right
  have tu : D.SL u ⊆ D.SL (D.N + j) := by rw [hL]; exact Finset.subset_union_left
  have tv : D.SL v ⊆ D.SL (D.N + j) := by rw [hL]; exact Finset.subset_union_right
  exact ⟨first_inj vk vk_inj _ _ _ hP p p' m1 n1 (preI h j p l r1 f1 u hu su tu)
    (preI h j p l r1 f1 v hv sv tv) m2 n2 (preI h j p' l r2 f2 u hu su tu)
    (preI h j p' l r2 f2 v hv sv tv), rfl⟩

lemma preV (h : OK D) (j : ℕ) (hj : j < D.s) (p : Fin n) (l : Fin m) (i : Fin k)
    (hv : HVg D j p l i) (w : ℕ) (hw : w < D.N + j) (hP : D.SP w ⊆ D.SP (D.N + j))
    (hL : D.SL w ⊆ D.SL (D.N + j)) (hp : p ∈ D.SP w) : MinK (kap D l) p (D.SP w) := by
  obtain ⟨hB, hpl, hno, hwg, hm, hnm, hf⟩ := hv
  by_cases hc : (D.SP w).card ≤ 1
  · exact mink_small _ _ _ hc hp
  · by_cases hwN : w < D.N
    · exact absurd (h.inP w hwN) hc
    · obtain ⟨j', rfl⟩ : ∃ j', w = D.N + j' := ⟨w - D.N, by omega⟩
      have hLe : D.SL (D.N + j') = ∅ := by
        rw [hwg.1] at hL
        exact Finset.subset_empty.mp hL
      by_cases hwild : ∀ lam : Fin m, ¬ ∀ x ∈ D.SP (D.N + j'), D.inc x lam = true
      · exact hf j' (by omega) ⟨hLe, hP.trans hwg.2.1, hwild⟩ hp
      · push_neg at hwild
        obtain ⟨lam, hlam⟩ := hwild
        intro y hy
        have kp : kap D l p = p.val := by simp [kap, hpl]
        by_cases hyl : D.inc y l = true
        · have ky : kap D l y = y.val := by simp [kap, hyl]
          by_cases hyp : y = p
          · rw [hyp]
          · have e : lam = l := line_eq h hyp (hlam y hy) (hlam p hp) hyl hpl
            subst e
            have hmin := hno j' (by omega) ⟨hLe, by omega, hlam⟩ hp y hy
            have hmin' : p.val ≤ y.val := hmin
            omega
        · have ky : kap D l y = n + y.val := by simp [kap, hyl]
          have := p.isLt
          omega

lemma HVg_inj (h : OK D) (j : ℕ) (hj : j < D.s) (p p' : Fin n) (l : Fin m) (i : Fin k)
    (h1 : HVg D j p l i) (h2 : HVg D j p' l i) : p = p' := by
  obtain ⟨u, v, hu, hv, hP, hL⟩ := h.gate j hj
  have su : D.SP u ⊆ D.SP (D.N + j) := by rw [hP]; exact Finset.subset_union_left
  have sv : D.SP v ⊆ D.SP (D.N + j) := by rw [hP]; exact Finset.subset_union_right
  have tu : D.SL u ⊆ D.SL (D.N + j) := by rw [hL]; exact Finset.subset_union_left
  have tv : D.SL v ⊆ D.SL (D.N + j) := by rw [hL]; exact Finset.subset_union_right
  exact first_inj (kap D l) (kap_inj D l) _ _ _ hP p p' h1.2.2.2.2.1 h1.2.2.2.2.2.1
    (preV h j hj p l i h1 u hu su tu) (preV h j hj p l i h1 v hv sv tv)
    h2.2.2.2.2.1 h2.2.2.2.2.2.1
    (preV h j hj p' l i h2 u hu su tu) (preV h j hj p' l i h2 v hv sv tv)

lemma HVg_rect (h : OK D) (j : ℕ) (p p' : Fin n) (l : Fin m) (i i' : Fin k)
    (h1 : HVg D j p l i) (h2 : HVg D j p' l i') : i = i' := by
  by_contra hne
  apply h1.2.2.2.1.2.2 l
  intro x hx
  rcases h.meet i i' hne x (h1.2.2.2.1.2.1 hx) (h2.2.2.2.1.2.1 hx) with hh | hh
  · exact hh l (by rw [h1.1]; exact Finset.mem_singleton_self l)
  · exact hh l (by rw [h2.1]; exact Finset.mem_singleton_self l)

lemma HVg_split (h : OK D) (j : ℕ) (hj : j < D.s) (u v : ℕ) (hu : u < D.N + j) (hv : v < D.N + j)
    (hP : D.SP (D.N + j) = D.SP u ∪ D.SP v) (hL : D.SL (D.N + j) = D.SL u ∪ D.SL v)
    (p : Fin n) (l : Fin m) (i : Fin k) (h1 : HVg D j p l i) :
    ∃ q, q ∈ D.SP (D.N + j) ∧ D.inc q l = true ∧ q ≠ p ∧ (p ∈ D.SP u ↔ ¬ q ∈ D.SP u) := by
  have su : D.SP u ⊆ D.SP (D.N + j) := by rw [hP]; exact Finset.subset_union_left
  have sv : D.SP v ⊆ D.SP (D.N + j) := by rw [hP]; exact Finset.subset_union_right
  have tu : D.SL u ⊆ D.SL (D.N + j) := by rw [hL]; exact Finset.subset_union_left
  have tv : D.SL v ⊆ D.SL (D.N + j) := by rw [hL]; exact Finset.subset_union_right
  obtain ⟨q, hq, hc⟩ := split (kap D l) _ _ _ hP p h1.2.2.2.2.1 h1.2.2.2.2.2.1
    (preV h j hj p l i h1 u hu su tu) (preV h j hj p l i h1 v hv sv tv)
  have kp : kap D l p = p.val := by simp [kap, h1.2.1]
  have hql : D.inc q l = true := by
    by_contra hql
    have kq : kap D l q = n + q.val := by simp [kap, hql]
    have := p.isLt
    omega
  have hqp : q ≠ p := by
    rintro rfl
    omega
  refine ⟨q, ?_, hql, hqp, ?_⟩
  · rw [hP]
    rcases hc with ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩
    · exact Finset.mem_union_right _ a
    · exact Finset.mem_union_left _ a
  · rcases hc with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · exact ⟨fun _ => a4, fun _ => a1⟩
    · exact ⟨fun hpu => absurd hpu a2, fun hnq => absurd a3 hnq⟩

lemma line_pick (h : OK D) (U : Fin n → Prop) (p q : Fin n) (la lb lc : Fin m)
    (hab : la ≠ lb) (hac : la ≠ lc) (hqp : q ≠ p)
    (hp : D.inc p la = true) (hq : D.inc q la = true) (hU : U p ↔ ¬ U q)
    (cp : D.inc p lb = true ∨ D.inc p lc = true) (cq : D.inc q lb = true ∨ D.inc q lc = true) :
    ∃ x y, D.inc x la = true ∧ D.inc x lb = true ∧ D.inc y la = true ∧ D.inc y lc = true ∧
      (U x ↔ ¬ U y) := by
  rcases cp with pb | pc <;> rcases cq with qb | qc
  · exact absurd (line_eq h hqp hq hp qb pb) hab
  · exact ⟨p, q, hp, pb, hq, qc, hU⟩
  · exact ⟨q, p, hq, qb, hp, pc, by tauto⟩
  · exact absurd (line_eq h hqp hq hp qc pc) hac

lemma tri_key (a b c : Prop) (h1 : a ↔ ¬ b) (h2 : a ↔ ¬ c) (h3 : b ↔ ¬ c) : False := by
  tauto

lemma tri (h : OK D) (U : Fin n → Prop) (p1 q1 p2 q2 p3 q3 : Fin n) (l1 l2 l3 : Fin m)
    (h12 : l1 ≠ l2) (h13 : l1 ≠ l3) (h23 : l2 ≠ l3)
    (e1 : q1 ≠ p1) (e2 : q2 ≠ p2) (e3 : q3 ≠ p3)
    (a1 : D.inc p1 l1 = true) (b1 : D.inc q1 l1 = true)
    (a2 : D.inc p2 l2 = true) (b2 : D.inc q2 l2 = true)
    (a3 : D.inc p3 l3 = true) (b3 : D.inc q3 l3 = true)
    (u1 : U p1 ↔ ¬ U q1) (u2 : U p2 ↔ ¬ U q2) (u3 : U p3 ↔ ¬ U q3)
    (c1 : D.inc p1 l2 = true ∨ D.inc p1 l3 = true) (d1 : D.inc q1 l2 = true ∨ D.inc q1 l3 = true)
    (c2 : D.inc p2 l1 = true ∨ D.inc p2 l3 = true) (d2 : D.inc q2 l1 = true ∨ D.inc q2 l3 = true)
    (c3 : D.inc p3 l1 = true ∨ D.inc p3 l2 = true) (d3 : D.inc q3 l1 = true ∨ D.inc q3 l2 = true) :
    False := by
  obtain ⟨x12, x13, hx1, hx2, hx3, hx4, hxU⟩ := line_pick h U p1 q1 l1 l2 l3 h12 h13 e1 a1 b1 u1 c1 d1
  obtain ⟨y21, y23, hy1, hy2, hy3, hy4, hyU⟩ :=
    line_pick h U p2 q2 l2 l1 l3 h12.symm h23 e2 a2 b2 u2 c2 d2
  obtain ⟨z31, z32, hz1, hz2, hz3, hz4, hzU⟩ :=
    line_pick h U p3 q3 l3 l1 l2 h13.symm h23.symm e3 a3 b3 u3 c3 d3
  have E1 : x12 = y21 := pt_eq h h12 hx1 hx2 hy2 hy1
  have E2 : x13 = z31 := pt_eq h h13 hx3 hx4 hz2 hz1
  have E3 : y23 = z32 := pt_eq h h23 hy3 hy4 hz4 hz3
  rw [← E1] at hyU
  rw [← E2, ← E3] at hzU
  exact tri_key _ _ _ hxU hyU hzU

lemma HVg_three (h : OK D) (j : ℕ) (hj : j < D.s) (p1 p2 p3 : Fin n) (l1 l2 l3 : Fin m)
    (i1 i2 i3 : Fin k) (h1 : HVg D j p1 l1 i1) (h2 : HVg D j p2 l2 i2) (h3 : HVg D j p3 l3 i3) :
    (p1 = p2 ∧ l1 = l2) ∨ (p1 = p3 ∧ l1 = l3) ∨ (p2 = p3 ∧ l2 = l3) := by
  by_cases e12 : l1 = l2
  · subst e12
    have e := HVg_rect h j p1 p2 l1 i1 i2 h1 h2
    subst e
    exact Or.inl ⟨HVg_inj h j hj p1 p2 l1 i1 h1 h2, rfl⟩
  by_cases e13 : l1 = l3
  · subst e13
    have e := HVg_rect h j p1 p3 l1 i1 i3 h1 h3
    subst e
    exact Or.inr (Or.inl ⟨HVg_inj h j hj p1 p3 l1 i1 h1 h3, rfl⟩)
  by_cases e23 : l2 = l3
  · subst e23
    have e := HVg_rect h j p2 p3 l2 i2 i3 h2 h3
    subst e
    exact Or.inr (Or.inr ⟨HVg_inj h j hj p2 p3 l2 i2 h2 h3, rfl⟩)
  exfalso
  obtain ⟨u, v, hu, hv, hP, hL⟩ := h.gate j hj
  obtain ⟨q1, m1, o1, n1, U1⟩ := HVg_split h j hj u v hu hv hP hL p1 l1 i1 h1
  obtain ⟨q2, m2, o2, n2, U2⟩ := HVg_split h j hj u v hu hv hP hL p2 l2 i2 h2
  obtain ⟨q3, m3, o3, n3, U3⟩ := HVg_split h j hj u v hu hv hP hL p3 l3 i3 h3
  have M : ∀ (ia ib : Fin k) (la lb : Fin m), D.B ia = {la} → D.B ib = {lb} → la ≠ lb →
      ∀ x, x ∈ D.A ia → x ∈ D.A ib → D.inc x la = true ∨ D.inc x lb = true := by
    intro ia ib la lb ha hb hne x hxa hxb
    have hi : ia ≠ ib := by
      rintro rfl
      exact hne (Finset.singleton_injective (ha.symm.trans hb))
    rcases h.meet ia ib hi x hxa hxb with hh | hh
    · exact Or.inl (hh la (by rw [ha]; exact Finset.mem_singleton_self la))
    · exact Or.inr (hh lb (by rw [hb]; exact Finset.mem_singleton_self lb))
  have s1 := h1.2.2.2.1.2.1
  have s2 := h2.2.2.2.1.2.1
  have s3 := h3.2.2.2.1.2.1
  have t1 := h1.2.2.2.2.1
  have t2 := h2.2.2.2.2.1
  have t3 := h3.2.2.2.2.1
  exact tri h (fun x => x ∈ D.SP u) p1 q1 p2 q2 p3 q3 l1 l2 l3 e12 e13 e23 n1 n2 n3
    h1.2.1 o1 h2.2.1 o2 h3.2.1 o3 U1 U2 U3
    (M i2 i3 l2 l3 h2.1 h3.1 e23 p1 (s2 t1) (s3 t1)) (M i2 i3 l2 l3 h2.1 h3.1 e23 q1 (s2 m1) (s3 m1))
    (M i1 i3 l1 l3 h1.1 h3.1 e13 p2 (s1 t2) (s3 t2)) (M i1 i3 l1 l3 h1.1 h3.1 e13 q2 (s1 m2) (s3 m2))
    (M i1 i2 l1 l2 h1.1 h2.1 e12 p3 (s1 t3) (s2 t3)) (M i1 i2 l1 l2 h1.1 h2.1 e12 q3 (s1 m3) (s2 m3))

lemma HVr_inj (t : Fin k) (p p' : Fin n) (l l' : Fin m)
    (h1 : HVr D t p l) (h2 : HVr D t p' l') : p = p' ∧ l = l' := by
  have hl : l = l' := Finset.singleton_injective (h1.1.symm.trans h2.1)
  subst hl
  exact ⟨le_antisymm (h1.2.2.2.2 p' h2.2.1 h2.2.2.1) (h2.2.2.2.2 p h1.2.1 h1.2.2.1), rfl⟩

lemma HS_inj (h : OK D) (t : Fin k) (p p' : Fin n) (l l' : Fin m)
    (h1 : HS D t p l) (h2 : HS D t p' l') : p = p' ∧ l = l' := by
  obtain ⟨x, hx, y, hy, hxy⟩ := (Finset.one_lt_card (s := D.A t)).mp (by have := h1.1; omega)
  exact ⟨le_antisymm (h1.2.2.2.2 p' h2.2.2.1) (h2.2.2.2.2 p h1.2.2.1),
    line_eq h hxy (h1.2.1 x hx) (h1.2.1 y hy) (h2.2.1 x hx) (h2.2.1 y hy)⟩

lemma cov1 (p : Fin n) (l : Fin m) (hn : ¬ NoC D p l) : ∃ j, j < D.s ∧ HI D j p l := by
  classical
  unfold NoC at hn
  push_neg at hn
  obtain ⟨j0, a0, b0, c0, d0⟩ := hn
  have hex : ∃ j, j < D.s ∧ RowG D l (D.N + j) ∧ p ∈ D.SP (D.N + j) ∧
      ¬ MinK vk p (D.SP (D.N + j)) := ⟨j0, a0, b0, c0, d0⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1, (Nat.find_spec hex).2.2.1,
    (Nat.find_spec hex).2.2.2, ?_⟩
  intro j' hj' hr hp
  by_contra hm
  exact Nat.find_min hex hj' ⟨by have := (Nat.find_spec hex).1; omega, hr, hp, hm⟩

lemma covS (h : OK D) (t : Fin k) (p : Fin n) (l : Fin m) (hp : p ∈ D.A t) (hl : l ∈ D.B t)
    (h2 : 2 ≤ (D.A t).card) (hr : ∀ g ∈ D.A t, D.inc g l = true) (hno : NoC D p l) :
    HS D t p l := by
  refine ⟨h2, hr, hp, hl, ?_⟩
  obtain ⟨w, hw, hwP, hwL⟩ := h.aw t
  have hwN : ¬ w < D.N := fun hlt => by
    have := h.inP w hlt
    rw [hwP] at this
    omega
  obtain ⟨j, rfl⟩ : ∃ j, w = D.N + j := ⟨w - D.N, by omega⟩
  have hmin := hno j (by omega) ⟨hwL, by rw [hwP]; exact h2, by rw [hwP]; exact hr⟩
    (by rw [hwP]; exact hp)
  intro y hy
  have hy' : vk p ≤ vk y := hmin y (by rw [hwP]; exact hy)
  exact hy'

lemma covV (h : OK D) (i : Fin k) (p : Fin n) (l : Fin m) (hB : D.B i = {l}) (hp : p ∈ D.A i)
    (hpl : D.inc p l = true) (hnr : ¬ ∀ g ∈ D.A i, D.inc g l = true) (hno : NoC D p l) :
    HVr D i p l ∨ ∃ j, j < D.s ∧ HVg D j p l i := by
  classical
  by_cases hmin : ∀ y ∈ D.A i, D.inc y l = true → p ≤ y
  · exact Or.inl ⟨hB, hp, hpl, hnr, hmin⟩
  · right
    push_neg at hmin
    obtain ⟨y, hy, hyl, hyp⟩ := hmin
    obtain ⟨w, hw, hwP, hwL⟩ := h.aw i
    have hne : y ≠ p := ne_of_lt hyp
    have hcard : 1 < (D.A i).card := Finset.one_lt_card.mpr ⟨y, hy, p, hp, hne⟩
    have hwN : ¬ w < D.N := fun hlt => by
      have := h.inP w hlt
      rw [hwP] at this
      omega
    obtain ⟨j0, rfl⟩ : ∃ j, w = D.N + j := ⟨w - D.N, by omega⟩
    have hex : ∃ j, j < D.s ∧ WG D i (D.N + j) ∧ p ∈ D.SP (D.N + j) ∧
        ¬ MinK (kap D l) p (D.SP (D.N + j)) := by
      refine ⟨j0, by omega, ⟨hwL, by rw [hwP], ?_⟩, by rw [hwP]; exact hp, ?_⟩
      · intro lam hlam
        rw [hwP] at hlam
        have e : lam = l := line_eq h hne (hlam y hy) (hlam p hp) hyl hpl
        subst e
        exact hnr hlam
      · intro hm
        have hle := hm y (by rw [hwP]; exact hy)
        have k1 : kap D l p = p.val := by simp [kap, hpl]
        have k2 : kap D l y = y.val := by simp [kap, hyl]
        have hlt : y.val < p.val := hyp
        omega
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, hB, hpl, hno, (Nat.find_spec hex).2.1,
      (Nat.find_spec hex).2.2.1, (Nat.find_spec hex).2.2.2, ?_⟩
    intro j' hj' hwg hpj
    by_contra hm
    exact Nat.find_min hex hj' ⟨by have := (Nat.find_spec hex).1; omega, hwg, hpj, hm⟩

-- the charging relation
def PS (D : Side n m k) (j : ℕ) (p : Fin n) (l : Fin m) (b b0 : Bool) : Prop :=
  HI D j p l ∨ (b = b0 ∧ ∃ i, HVg D j p l i)

def Dst (D : Side n m k) (t : Fin k) : Prop :=
  ∃ c : Fin n, 2 ≤ (D.B t).card ∧ ∀ e ∈ D.B t, D.inc c e = true

def Hit (D : Side n m k) (p : Fin n) (l : Fin m) (b : Bool) : ℕ ⊕ (Fin k ⊕ Fin k) → Prop
  | Sum.inl j => j < D.s ∧ (PS D j p l b false ∨ PS D.dual j l p b true)
  | Sum.inr (Sum.inl t) => HS D.dual t l p ∨ (HS D t p l ∧ ¬ Dst D t) ∨
      (D.A t = {p} ∧ D.B t = {l} ∧ D.inc p l = true) ∨ HVr D t p l ∨ HVr D.dual t l p
  | Sum.inr (Sum.inr t) => HS D t p l ∧ Dst D t

lemma bool3 (b1 b2 b3 : Bool) : b1 = b2 ∨ b1 = b3 ∨ b2 = b3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> simp

lemma same3 {p1 p2 p3 : Fin n} {l1 l2 l3 : Fin m} (b1 b2 b3 : Bool)
    (e12 : p1 = p2 ∧ l1 = l2) (e13 : p1 = p3 ∧ l1 = l3) :
    (p1 = p2 ∧ l1 = l2 ∧ b1 = b2) ∨ (p1 = p3 ∧ l1 = l3 ∧ b1 = b3) ∨
      (p2 = p3 ∧ l2 = l3 ∧ b2 = b3) := by
  rcases bool3 b1 b2 b3 with e | e | e
  · exact Or.inl ⟨e12.1, e12.2, e⟩
  · exact Or.inr (Or.inl ⟨e13.1, e13.2, e⟩)
  · exact Or.inr (Or.inr ⟨e12.1.symm.trans e13.1, e12.2.symm.trans e13.2, e⟩)

lemma PS_three (h : OK D) (j : ℕ) (hj : j < D.s) (b0 : Bool) (p1 p2 p3 : Fin n) (l1 l2 l3 : Fin m)
    (b1 b2 b3 : Bool) (H1 : PS D j p1 l1 b1 b0) (H2 : PS D j p2 l2 b2 b0) (H3 : PS D j p3 l3 b3 b0) :
    (p1 = p2 ∧ l1 = l2 ∧ b1 = b2) ∨ (p1 = p3 ∧ l1 = l3 ∧ b1 = b3) ∨
      (p2 = p3 ∧ l2 = l3 ∧ b2 = b3) := by
  have X : ∀ (p p' : Fin n) (l l' : Fin m) (i : Fin k), HI D j p l → HVg D j p' l' i → False :=
    fun p p' l l' i a c => c.2.2.2.1.2.2 l a.1.2.2
  rcases H1 with a | ⟨eb1, i1, a⟩ <;> rcases H2 with c | ⟨eb2, i2, c⟩ <;>
    rcases H3 with d | ⟨eb3, i3, d⟩
  · exact same3 b1 b2 b3 (HI_inj h j hj _ _ _ _ a c) (HI_inj h j hj _ _ _ _ a d)
  · exact (X _ _ _ _ _ a d).elim
  · exact (X _ _ _ _ _ a c).elim
  · exact (X _ _ _ _ _ a c).elim
  · exact (X _ _ _ _ _ c a).elim
  · exact (X _ _ _ _ _ c a).elim
  · exact (X _ _ _ _ _ d a).elim
  · rcases HVg_three h j hj p1 p2 p3 l1 l2 l3 i1 i2 i3 a c d with e | e | e
    · exact Or.inl ⟨e.1, e.2, eb1.trans eb2.symm⟩
    · exact Or.inr (Or.inl ⟨e.1, e.2, eb1.trans eb3.symm⟩)
    · exact Or.inr (Or.inr ⟨e.1, e.2, eb2.trans eb3.symm⟩)

lemma PS_side (j : ℕ) (p : Fin n) (l : Fin m) (b b0 : Bool) (H : PS D j p l b b0) :
    D.SL (D.N + j) = ∅ ∧ p ∈ D.SP (D.N + j) := by
  rcases H with a | ⟨_, i, a⟩
  · exact ⟨a.1.1, a.2.1⟩
  · exact ⟨a.2.2.2.1.1, a.2.2.2.2.1⟩

lemma PS_cross (j : ℕ) (p p' : Fin n) (l l' : Fin m) (b b' b0 b0' : Bool)
    (H : PS D j p l b b0) (H' : PS D.dual j l' p' b' b0') : False := by
  have h1 := (PS_side j p l b b0 H).2
  have h2 : D.SP (D.N + j) = ∅ := (PS_side j l' p' b' b0' H').1
  rw [h2] at h1
  exact absurd h1 (Finset.notMem_empty p)

lemma sing_card {α : Type} (S : Finset α) (x : α) (h : S = {x}) : ¬ 2 ≤ S.card := by
  subst h
  simp

lemma sing_mem {α : Type} (S : Finset α) (x y : α) (h : S = {x}) (hy : y ∈ S) : y = x := by
  subst h
  exact Finset.mem_singleton.mp hy

lemma sing_all {α : Type} (S : Finset α) (x : α) (P : α → Prop) (h : S = {x}) (hx : P x) :
    ∀ g ∈ S, P g := by
  subst h
  intro g hg
  rw [Finset.mem_singleton.mp hg]
  exact hx

lemma rect_pair (h : OK D) (h' : OK D.dual) (t : Fin k) (p p' : Fin n) (l l' : Fin m) (b b' : Bool)
    (H1 : Hit D p l b (Sum.inr (Sum.inl t))) (H2 : Hit D p' l' b' (Sum.inr (Sum.inl t))) :
    p = p' ∧ l = l' := by
  have x01 : ∀ (p p' : Fin n) (l l' : Fin m), HS D.dual t l p → (HS D t p' l' ∧ ¬ Dst D t) → False :=
    fun p p' l l' a c => c.2 ⟨p, a.1, a.2.1⟩
  have x02 : ∀ (p p' : Fin n) (l l' : Fin m), HS D.dual t l p →
      (D.A t = {p'} ∧ D.B t = {l'} ∧ D.inc p' l' = true) → False :=
    fun p p' l l' a c => sing_card _ _ c.2.1 a.1
  have x03 : ∀ (p p' : Fin n) (l l' : Fin m), HS D.dual t l p → HVr D t p' l' → False :=
    fun p p' l l' a c => sing_card _ _ c.1 a.1
  have x04 : ∀ (p p' : Fin n) (l l' : Fin m), HS D.dual t l p → HVr D.dual t l' p' → False := by
    intro p p' l l' a c
    have e : p = p' := sing_mem _ _ _ c.1 a.2.2.2.1
    subst e
    exact c.2.2.2.1 a.2.1
  have x12 : ∀ (p p' : Fin n) (l l' : Fin m), (HS D t p l ∧ ¬ Dst D t) →
      (D.A t = {p'} ∧ D.B t = {l'} ∧ D.inc p' l' = true) → False :=
    fun p p' l l' a c => sing_card _ _ c.1 a.1.1
  have x13 : ∀ (p p' : Fin n) (l l' : Fin m), (HS D t p l ∧ ¬ Dst D t) → HVr D t p' l' → False := by
    intro p p' l l' a c
    have e : l = l' := sing_mem _ _ _ c.1 a.1.2.2.2.1
    subst e
    exact c.2.2.2.1 a.1.2.1
  have x14 : ∀ (p p' : Fin n) (l l' : Fin m), (HS D t p l ∧ ¬ Dst D t) → HVr D.dual t l' p' → False :=
    fun p p' l l' a c => sing_card _ _ c.1 a.1.1
  have x23 : ∀ (p p' : Fin n) (l l' : Fin m), (D.A t = {p} ∧ D.B t = {l} ∧ D.inc p l = true) →
      HVr D t p' l' → False := by
    intro p p' l l' a c
    have e : l = l' := Finset.singleton_injective (a.2.1.symm.trans c.1)
    subst e
    exact c.2.2.2.1 (sing_all _ _ (fun g => D.inc g l = true) a.1 a.2.2)
  have x24 : ∀ (p p' : Fin n) (l l' : Fin m), (D.A t = {p} ∧ D.B t = {l} ∧ D.inc p l = true) →
      HVr D.dual t l' p' → False := by
    intro p p' l l' a c
    have e : p = p' := Finset.singleton_injective (a.1.symm.trans c.1)
    subst e
    exact c.2.2.2.1 (sing_all _ _ (fun g => D.inc p g = true) a.2.1 a.2.2)
  have x34 : ∀ (p p' : Fin n) (l l' : Fin m), HVr D t p l → HVr D.dual t l' p' → False := by
    intro p p' l l' a c
    have e : p = p' := sing_mem _ _ _ c.1 a.2.1
    subst e
    exact a.2.2.2.1 (sing_all _ _ (fun g => D.inc g l = true) c.1 a.2.2.1)
  rcases H1 with a | a | a | a | a <;> rcases H2 with c | c | c | c | c
  · exact (HS_inj h' t l l' p p' a c).symm
  · exact (x01 _ _ _ _ a c).elim
  · exact (x02 _ _ _ _ a c).elim
  · exact (x03 _ _ _ _ a c).elim
  · exact (x04 _ _ _ _ a c).elim
  · exact (x01 _ _ _ _ c a).elim
  · exact HS_inj h t p p' l l' a.1 c.1
  · exact (x12 _ _ _ _ a c).elim
  · exact (x13 _ _ _ _ a c).elim
  · exact (x14 _ _ _ _ a c).elim
  · exact (x02 _ _ _ _ c a).elim
  · exact (x12 _ _ _ _ c a).elim
  · exact ⟨Finset.singleton_injective (a.1.symm.trans c.1),
      Finset.singleton_injective (a.2.1.symm.trans c.2.1)⟩
  · exact (x23 _ _ _ _ a c).elim
  · exact (x24 _ _ _ _ a c).elim
  · exact (x03 _ _ _ _ c a).elim
  · exact (x13 _ _ _ _ c a).elim
  · exact (x23 _ _ _ _ c a).elim
  · exact HVr_inj t p p' l l' a c
  · exact (x34 _ _ _ _ a c).elim
  · exact (x04 _ _ _ _ c a).elim
  · exact (x14 _ _ _ _ c a).elim
  · exact (x24 _ _ _ _ c a).elim
  · exact (x34 _ _ _ _ c a).elim
  · exact (HVr_inj t l l' p p' a c).symm

lemma mult (h : OK D) (h' : OK D.dual) (y : ℕ ⊕ (Fin k ⊕ Fin k)) (p1 p2 p3 : Fin n)
    (l1 l2 l3 : Fin m) (b1 b2 b3 : Bool)
    (H1 : Hit D p1 l1 b1 y) (H2 : Hit D p2 l2 b2 y) (H3 : Hit D p3 l3 b3 y) :
    (p1 = p2 ∧ l1 = l2 ∧ b1 = b2) ∨ (p1 = p3 ∧ l1 = l3 ∧ b1 = b3) ∨
      (p2 = p3 ∧ l2 = l3 ∧ b2 = b3) := by
  rcases y with j | t | t
  · obtain ⟨hj, H1⟩ := H1
    obtain ⟨_, H2⟩ := H2
    obtain ⟨_, H3⟩ := H3
    rcases H1 with a | a <;> rcases H2 with c | c <;> rcases H3 with d | d
    · exact PS_three h j hj false p1 p2 p3 l1 l2 l3 b1 b2 b3 a c d
    · exact (PS_cross j _ _ _ _ _ _ _ _ a d).elim
    · exact (PS_cross j _ _ _ _ _ _ _ _ a c).elim
    · exact (PS_cross j _ _ _ _ _ _ _ _ a c).elim
    · exact (PS_cross j _ _ _ _ _ _ _ _ c a).elim
    · exact (PS_cross j _ _ _ _ _ _ _ _ c a).elim
    · exact (PS_cross j _ _ _ _ _ _ _ _ d a).elim
    · rcases PS_three h' j hj true l1 l2 l3 p1 p2 p3 b1 b2 b3 a c d with e | e | e
      · exact Or.inl ⟨e.2.1, e.1, e.2.2⟩
      · exact Or.inr (Or.inl ⟨e.2.1, e.1, e.2.2⟩)
      · exact Or.inr (Or.inr ⟨e.2.1, e.1, e.2.2⟩)
  · exact same3 b1 b2 b3 (rect_pair h h' t p1 p2 l1 l2 b1 b2 H1 H2)
      (rect_pair h h' t p1 p3 l1 l3 b1 b3 H1 H3)
  · exact same3 b1 b2 b3 (HS_inj h t p1 p2 l1 l2 H1.1 H2.1) (HS_inj h t p1 p3 l1 l3 H1.1 H3.1)

lemma cover (h : OK D) (h' : OK D.dual) (Dset : Finset (Fin k))
    (hD : ∀ t, Dst D t → (∃ f ∈ D.B t, 2 ≤ (D.A t).card ∧ ∀ g ∈ D.A t, D.inc g f = true) → t ∈ Dset)
    (p : Fin n) (l : Fin m) (b : Bool) (hpl : D.inc p l = true) (i j : Fin k) (hij : i ≠ j)
    (pi : p ∈ D.A i) (pj : p ∈ D.A j) (li : l ∈ D.B i) (lj : l ∈ D.B j) :
    ∃ y, y ∈ (Finset.range D.s).disjSum ((Finset.univ : Finset (Fin k)).disjSum Dset) ∧
      Hit D p l b y := by
  have memG : ∀ j0, j0 < D.s → (Sum.inl j0 : ℕ ⊕ (Fin k ⊕ Fin k)) ∈
      (Finset.range D.s).disjSum ((Finset.univ : Finset (Fin k)).disjSum Dset) :=
    fun j0 hj0 => Finset.inl_mem_disjSum.mpr (Finset.mem_range.mpr hj0)
  have memR : ∀ t : Fin k, (Sum.inr (Sum.inl t) : ℕ ⊕ (Fin k ⊕ Fin k)) ∈
      (Finset.range D.s).disjSum ((Finset.univ : Finset (Fin k)).disjSum Dset) :=
    fun t => Finset.inr_mem_disjSum.mpr (Finset.inl_mem_disjSum.mpr (Finset.mem_univ t))
  by_cases c1 : NoC D p l
  swap
  · obtain ⟨j0, hj0, hh⟩ := cov1 p l c1
    exact ⟨Sum.inl j0, memG j0 hj0, hj0, Or.inl (Or.inl hh)⟩
  by_cases c2 : NoC D.dual l p
  swap
  · obtain ⟨j0, hj0, hh⟩ := cov1 l p c2
    exact ⟨Sum.inl j0, memG j0 hj0, hj0, Or.inr (Or.inl hh)⟩
  by_cases c3 : ∃ t, p ∈ D.A t ∧ l ∈ D.B t ∧ 2 ≤ (D.B t).card ∧ ∀ e ∈ D.B t, D.inc p e = true
  · obtain ⟨t, a1, a2, a3, a4⟩ := c3
    exact ⟨Sum.inr (Sum.inl t), memR t, Or.inl (covS h' t l p a2 a1 a3 a4 c2)⟩
  by_cases c4 : ∃ t, p ∈ D.A t ∧ l ∈ D.B t ∧ 2 ≤ (D.A t).card ∧ ∀ g ∈ D.A t, D.inc g l = true
  · obtain ⟨t, a1, a2, a3, a4⟩ := c4
    have hs := covS h t p l a1 a2 a3 a4 c1
    by_cases hd : Dst D t
    · exact ⟨Sum.inr (Sum.inr t), Finset.inr_mem_disjSum.mpr (Finset.inr_mem_disjSum.mpr
        (hD t hd ⟨l, a2, a3, a4⟩)), hs, hd⟩
    · exact ⟨Sum.inr (Sum.inl t), memR t, Or.inr (Or.inl ⟨hs, hd⟩)⟩
  by_cases c5 : ∃ t, D.A t = {p} ∧ D.B t = {l}
  · obtain ⟨t, a1, a2⟩ := c5
    exact ⟨Sum.inr (Sum.inl t), memR t, Or.inr (Or.inr (Or.inl ⟨a1, a2, hpl⟩))⟩
  have sing : ∀ {α : Type} (S : Finset α) (x : α), x ∈ S → ¬ 2 ≤ S.card → S = {x} := by
    intro α S x hx hc
    exact Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hx, fun y hy => (Finset.card_le_one.mp (by omega)) y hy x hx⟩
  cases b
  · have ht1 : ∃ t, p ∈ D.A t ∧ D.B t = {l} := by
      rcases h.meet i j hij p pi pj with hh | hh
      · exact ⟨i, pi, sing _ _ li (fun h2 => c3 ⟨i, pi, li, h2, hh⟩)⟩
      · exact ⟨j, pj, sing _ _ lj (fun h2 => c3 ⟨j, pj, lj, h2, hh⟩)⟩
    obtain ⟨t, a1, a2⟩ := ht1
    have hlt : l ∈ D.B t := by rw [a2]; exact Finset.mem_singleton_self l
    have hnr : ¬ ∀ g ∈ D.A t, D.inc g l = true := by
      intro hall
      by_cases h2 : 2 ≤ (D.A t).card
      · exact c4 ⟨t, a1, hlt, h2, hall⟩
      · exact c5 ⟨t, sing _ _ a1 h2, a2⟩
    rcases covV h t p l a2 a1 hpl hnr c1 with hh | ⟨j0, hj0, hh⟩
    · exact ⟨Sum.inr (Sum.inl t), memR t, Or.inr (Or.inr (Or.inr (Or.inl hh)))⟩
    · exact ⟨Sum.inl j0, memG j0 hj0, hj0, Or.inl (Or.inr ⟨rfl, t, hh⟩)⟩
  · have ht2 : ∃ t, l ∈ D.B t ∧ D.A t = {p} := by
      rcases h'.meet i j hij l li lj with hh | hh
      · exact ⟨i, li, sing _ _ pi (fun h2 => c4 ⟨i, pi, li, h2, hh⟩)⟩
      · exact ⟨j, lj, sing _ _ pj (fun h2 => c4 ⟨j, pj, lj, h2, hh⟩)⟩
    obtain ⟨t, a1, a2⟩ := ht2
    have hpt : p ∈ D.A t := by rw [a2]; exact Finset.mem_singleton_self p
    have hnr : ¬ ∀ g ∈ D.B t, D.inc p g = true := by
      intro hall
      by_cases h2 : 2 ≤ (D.B t).card
      · exact c3 ⟨t, hpt, a1, h2, hall⟩
      · exact c5 ⟨t, a2, sing _ _ a1 h2⟩
    rcases covV h' t l p a2 a1 hpl hnr c2 with hh | ⟨j0, hj0, hh⟩
    · exact ⟨Sum.inr (Sum.inl t), memR t, Or.inr (Or.inr (Or.inr (Or.inr hh)))⟩
    · exact ⟨Sum.inl j0, memG j0 hj0, hj0, Or.inr (Or.inr ⟨rfl, t, hh⟩)⟩

lemma count2 {α β : Type} [DecidableEq α] [DecidableEq β] (S : Finset α) (T : Finset β)
    (R : α → β → Prop) (hex : ∀ x ∈ S, ∃ y ∈ T, R x y)
    (h3 : ∀ y x1 x2 x3, R x1 y → R x2 y → R x3 y → x1 = x2 ∨ x1 = x3 ∨ x2 = x3) :
    S.card ≤ 2 * T.card := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp
  obtain ⟨y0, _, _⟩ := hex x0 hx0
  have hex' : ∀ x, ∃ y, x ∈ S → y ∈ T ∧ R x y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨y, hy, hr⟩ := hex x hx
      exact ⟨y, fun _ => ⟨hy, hr⟩⟩
    · exact ⟨y0, fun hh => absurd hh hx⟩
  choose f hf using hex'
  apply Finset.card_le_mul_card_image_of_maps_to (f := f) (fun a ha => (hf a ha).1)
  intro y hy
  by_contra hcon
  rw [not_le, Finset.two_lt_card] at hcon
  obtain ⟨x1, hx1, x2, hx2, x3, hx3, h12, h13, h23⟩ := hcon
  rw [Finset.mem_filter] at hx1 hx2 hx3
  have r1 : R x1 y := hx1.2 ▸ (hf x1 hx1.1).2
  have r2 : R x2 y := hx2.2 ▸ (hf x2 hx2.1).2
  have r3 : R x3 y := hx3.2 ▸ (hf x3 hx3.1).2
  rcases h3 y x1 x2 x3 r1 r2 r3 with e | e | e
  · exact h12 e
  · exact h13 e
  · exact h23 e

lemma final (D : Side n m k) (h : OK D) (h' : OK D.dual) (E : Finset (Fin n × Fin m))
    (Dset : Finset (Fin k))
    (hE : ∀ q ∈ E, D.inc q.1 q.2 = true ∧ ∃ i j : Fin k, i ≠ j ∧ q.1 ∈ D.A i ∧ q.1 ∈ D.A j ∧
      q.2 ∈ D.B i ∧ q.2 ∈ D.B j)
    (hD : ∀ t, Dst D t → (∃ f ∈ D.B t, 2 ≤ (D.A t).card ∧ ∀ g ∈ D.A t, D.inc g f = true) → t ∈ Dset) :
    E.card ≤ D.s + (k + Dset.card) := by
  have hex : ∀ x ∈ E ×ˢ (Finset.univ : Finset Bool),
      ∃ y ∈ (Finset.range D.s).disjSum ((Finset.univ : Finset (Fin k)).disjSum Dset),
        Hit D x.1.1 x.1.2 x.2 y := by
    intro x hx
    obtain ⟨hpl, i, j, hij, a1, a2, a3, a4⟩ := hE x.1 (Finset.mem_product.mp hx).1
    exact cover h h' Dset hD x.1.1 x.1.2 x.2 hpl i j hij a1 a2 a3 a4
  have h3 : ∀ (y : ℕ ⊕ (Fin k ⊕ Fin k)) (x1 x2 x3 : (Fin n × Fin m) × Bool),
      Hit D x1.1.1 x1.1.2 x1.2 y → Hit D x2.1.1 x2.1.2 x2.2 y → Hit D x3.1.1 x3.1.2 x3.2 y →
      x1 = x2 ∨ x1 = x3 ∨ x2 = x3 := by
    intro y x1 x2 x3 r1 r2 r3
    rcases mult h h' y _ _ _ _ _ _ _ _ _ r1 r2 r3 with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact Or.inl (Prod.ext (Prod.ext a b) c)
    · exact Or.inr (Or.inl (Prod.ext (Prod.ext a b) c))
    · exact Or.inr (Or.inr (Prod.ext (Prod.ext a b) c))
  have hc := count2 (E ×ˢ (Finset.univ : Finset Bool))
    ((Finset.range D.s).disjSum ((Finset.univ : Finset (Fin k)).disjSum Dset))
    (fun x y => Hit D x.1.1 x.1.2 x.2 y) hex h3
  rw [Finset.card_product, Finset.card_disjSum, Finset.card_disjSum, Finset.card_range,
    Finset.card_univ, Finset.card_univ, Fintype.card_bool, Fintype.card_fin] at hc
  omega


-- the circuit side
def zin {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) : Fin (n + m) → Bool :=
  Fin.append (fun u => decide (u ∈ P)) (fun v => decide (v ∈ L))

lemma ofFn_zin {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) :
    List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L)) =
      List.ofFn (zin P L) := by
  unfold zin
  exact (List.ofFn_fin_append _ _).symm

lemma getD_ofFn {N : ℕ} (z : Fin N → Bool) (i : ℕ) (hi : i < N) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  have h := val_lt ([] : List Gate) z i hi
  exact h

lemma zin_left {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) (p : Fin n) :
    (List.ofFn (zin P L)).getD p.val false = decide (p ∈ P) := by
  rw [getD_ofFn _ _ (by have := p.isLt; omega)]
  show zin P L (Fin.castAdd m p) = decide (p ∈ P)
  unfold zin
  rw [Fin.append_left]

lemma zin_right {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) (l : Fin m) :
    (List.ofFn (zin P L)).getD (n + l.val) false = decide (l ∈ L) := by
  rw [getD_ofFn _ _ (by have := l.isLt; omega)]
  show zin P L (Fin.natAdd n l) = decide (l ∈ L)
  unfold zin
  rw [Fin.append_right]

lemma zin_in_left {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) (w : ℕ) (hw : w < n)
    (hw' : w < n + m) : zin P L ⟨w, hw'⟩ = decide ((⟨w, hw⟩ : Fin n) ∈ P) := by
  show zin P L (Fin.castAdd m ⟨w, hw⟩) = _
  unfold zin
  rw [Fin.append_left]

lemma zin_in_right {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) (w : ℕ) (hw : n ≤ w)
    (hw' : w < n + m) : zin P L ⟨w, hw'⟩ = decide ((⟨w - n, by omega⟩ : Fin m) ∈ L) := by
  have e : (⟨w, hw'⟩ : Fin (n + m)) = Fin.natAdd n ⟨w - n, by omega⟩ :=
    Fin.ext (by show w = n + (w - n); omega)
  rw [e]
  unfold zin
  rw [Fin.append_right]

def SPf (n m : ℕ) (G : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val G (zin ({p} : Finset (Fin n)) (∅ : Finset (Fin m))) w = true)

def SLf (n m : ℕ) (G : List Gate) (w : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun l => val G (zin (∅ : Finset (Fin n)) ({l} : Finset (Fin m))) w = true)

lemma SPf_in (n m : ℕ) (G : List Gate) (w : ℕ) (hw : w < n + m) : (SPf n m G w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp p' hp'
  simp only [SPf, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  rw [val_lt G _ w hw] at hp hp'
  by_cases hwn : w < n
  · rw [zin_in_left _ _ w hwn hw] at hp hp'
    simp only [decide_eq_true_eq, Finset.mem_singleton] at hp hp'
    rw [← hp, ← hp']
  · rw [zin_in_right _ _ w (by omega) hw] at hp
    simp at hp

lemma SLf_in (n m : ℕ) (G : List Gate) (w : ℕ) (hw : w < n + m) : (SLf n m G w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp p' hp'
  simp only [SLf, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  rw [val_lt G _ w hw] at hp hp'
  by_cases hwn : w < n
  · rw [zin_in_left _ _ w hwn hw] at hp
    simp at hp
  · rw [zin_in_right _ _ w (by omega) hw] at hp hp'
    simp only [decide_eq_true_eq, Finset.mem_singleton] at hp hp'
    rw [← hp, ← hp']

theorem main : ∀ (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
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
  intro n m inc C s k T a b A B h4 hM hRB hsz hk hOR hrect hout hsound
  have hlen : C.gates.length = s + k + T := hsz
  have rectv : ∀ (P : Finset (Fin n)) (L : Finset (Fin m)) (t : Fin k),
      (val C.gates (zin P L) (a t) = true ↔ ∃ pa ∈ A t, pa ∈ P) ∧
      (val C.gates (zin P L) (b t) = true ↔ ∃ lb ∈ B t, lb ∈ L) := by
    intro P L t
    have hx := (hrect t).2.2.2.2.2.2 (List.ofFn (zin P L)) (by simp)
    constructor
    · have h1 : val C.gates (zin P L) (a t) =
          decide (∃ pa ∈ A t, (List.ofFn (zin P L)).getD pa.val false = true) := hx.1
      rw [h1]
      simp only [zin_left, decide_eq_true_eq]
    · have h2 : val C.gates (zin P L) (b t) =
          decide (∃ lb ∈ B t, (List.ofFn (zin P L)).getD (n + lb.val) false = true) := hx.2
      rw [h2]
      simp only [zin_right, decide_eq_true_eq]
  have rectg : ∀ (z : Fin (n + m) → Bool) (t : Fin k),
      val C.gates z (n + m + s + t.val) = (val C.gates z (a t) && val C.gates z (b t)) := by
    intro z t
    obtain ⟨_, _, ha, hb, hop, hin, _⟩ := hrect t
    have e1 : (ga C.gates (s + t.val)).op = GateOp.and := hop
    have e2 : (ga C.gates (s + t.val)).inputs = [a t, b t] := hin
    rw [Nat.add_assoc (n + m) s t.val, val_ga, e1, e2]
    simp only [ev_and2]
    rw [if_pos (by omega), if_pos (by omega)]
  have org : ∀ j, j < s → ∃ u v, u < n + m + j ∧ v < n + m + j ∧
      ∀ z : Fin (n + m) → Bool, val C.gates z (n + m + j) = (val C.gates z u || val C.gates z v) := by
    intro j hj
    obtain ⟨hop, hl⟩ := hOR j hj
    have e1 : (ga C.gates j).op = GateOp.or := hop
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hl
    have e2 : (ga C.gates j).inputs = [u, v] := huv
    have hu : u < n + m + j := hRB j (by omega) u (by rw [huv]; simp)
    have hv : v < n + m + j := hRB j (by omega) v (by rw [huv]; simp)
    refine ⟨u, v, hu, hv, fun z => ?_⟩
    rw [val_ga, e1, e2]
    simp only [ev_or2]
    rw [if_pos hu, if_pos hv]
  have evi : ∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
      C.eval (List.ofFn (zin P L)) = true ↔ ∃ i1 j1 : Fin k, i1 < j1 ∧
        ((∃ pa ∈ A i1, pa ∈ P) ∧ ∃ lb ∈ B i1, lb ∈ L) ∧
        ((∃ pa ∈ A j1, pa ∈ P) ∧ ∃ lb ∈ B j1, lb ∈ L) := by
    intro P L
    have rt : ∀ t : Fin k,
        (C.wires (List.ofFn (zin P L))).getD (n + m + s + t.val) false = true ↔
        ((∃ pa ∈ A t, pa ∈ P) ∧ ∃ lb ∈ B t, lb ∈ L) := by
      intro t
      have e : (C.wires (List.ofFn (zin P L))).getD (n + m + s + t.val) false =
          val C.gates (zin P L) (n + m + s + t.val) := rfl
      rw [e, rectg, Bool.and_eq_true, (rectv P L t).1, (rectv P L t).2]
    rw [hout _ (by simp), decide_eq_true_eq]
    simp only [rt]
  have gateS : ∀ j, j < s → ∃ u v, u < n + m + j ∧ v < n + m + j ∧
      SPf n m C.gates (n + m + j) = SPf n m C.gates u ∪ SPf n m C.gates v ∧
      SLf n m C.gates (n + m + j) = SLf n m C.gates u ∪ SLf n m C.gates v := by
    intro j hj
    obtain ⟨u, v, hu, hv, hz⟩ := org j hj
    refine ⟨u, v, hu, hv, ?_, ?_⟩
    · ext p
      simp only [SPf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      rw [hz, Bool.or_eq_true]
    · ext p
      simp only [SLf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      rw [hz, Bool.or_eq_true]
  have awS : ∀ t, ∃ w, w < n + m + s ∧ SPf n m C.gates w = A t ∧ SLf n m C.gates w = ∅ := by
    intro t
    refine ⟨a t, (hrect t).2.2.1, ?_, ?_⟩
    · ext p
      simp only [SPf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(rectv {p} ∅ t).1]
      simp
    · ext l
      simp only [SLf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(rectv ∅ {l} t).1]
      simp
  have bwS : ∀ t, ∃ w, w < n + m + s ∧ SLf n m C.gates w = B t ∧ SPf n m C.gates w = ∅ := by
    intro t
    refine ⟨b t, (hrect t).2.2.2.1, ?_, ?_⟩
    · ext l
      simp only [SLf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(rectv ∅ {l} t).2]
      simp
    · ext p
      simp only [SPf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(rectv {p} ∅ t).2]
      simp
  have meetP : ∀ i j : Fin k, i ≠ j → ∀ p, p ∈ A i → p ∈ A j →
      (∀ l ∈ B i, inc p l = true) ∨ (∀ l ∈ B j, inc p l = true) := by
    intro i j hij p hpi hpj
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨l, hl, hnl⟩, ⟨l', hl', hnl'⟩⟩ := hcon
    have hs := hsound {p} {l, l'} (Or.inl ⟨Finset.card_singleton p, Finset.card_le_two⟩) (by
      intro x hx y hy
      rw [Finset.mem_singleton] at hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      subst hx
      rcases hy with rfl | rfl
      · simpa using hnl
      · simpa using hnl')
    rw [ofFn_zin] at hs
    have ht : C.eval (List.ofFn (zin ({p} : Finset (Fin n)) ({l, l'} : Finset (Fin m)))) = true := by
      rw [evi]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact ⟨i, j, hlt, ⟨⟨p, hpi, by simp⟩, ⟨l, hl, by simp⟩⟩, ⟨⟨p, hpj, by simp⟩, ⟨l', hl', by simp⟩⟩⟩
      · exact ⟨j, i, hlt, ⟨⟨p, hpj, by simp⟩, ⟨l', hl', by simp⟩⟩, ⟨⟨p, hpi, by simp⟩, ⟨l, hl, by simp⟩⟩⟩
    rw [ht] at hs
    exact absurd hs (by simp)
  have meetL : ∀ i j : Fin k, i ≠ j → ∀ l, l ∈ B i → l ∈ B j →
      (∀ p ∈ A i, inc p l = true) ∨ (∀ p ∈ A j, inc p l = true) := by
    intro i j hij l hli hlj
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨p, hp, hnp⟩, ⟨p', hp', hnp'⟩⟩ := hcon
    have hs := hsound {p, p'} {l} (Or.inr ⟨Finset.card_le_two, Finset.card_singleton l⟩) (by
      intro x hx y hy
      rw [Finset.mem_singleton] at hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      subst hy
      rcases hx with rfl | rfl
      · simpa using hnp
      · simpa using hnp')
    rw [ofFn_zin] at hs
    have ht : C.eval (List.ofFn (zin ({p, p'} : Finset (Fin n)) ({l} : Finset (Fin m)))) = true := by
      rw [evi]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact ⟨i, j, hlt, ⟨⟨p, hp, by simp⟩, ⟨l, hli, by simp⟩⟩, ⟨⟨p', hp', by simp⟩, ⟨l, hlj, by simp⟩⟩⟩
      · exact ⟨j, i, hlt, ⟨⟨p', hp', by simp⟩, ⟨l, hlj, by simp⟩⟩, ⟨⟨p, hp, by simp⟩, ⟨l, hli, by simp⟩⟩⟩
    rw [ht] at hs
    exact absurd hs (by simp)
  have hOK : OK (⟨inc, n + m, s, SPf n m C.gates, SLf n m C.gates, A, B⟩ : Side n m k) :=
    ⟨h4, gateS, SPf_in n m C.gates, awS, meetP⟩
  have hOK' : OK (Side.dual (⟨inc, n + m, s, SPf n m C.gates, SLf n m C.gates, A, B⟩ : Side n m k)) :=
    ⟨fun l l' p p' hl hp e1 e2 e3 e4 => h4 p p' l l' hp hl e1 e3 e2 e4,
      fun j hj => by
        obtain ⟨u, v, hu, hv, e1, e2⟩ := gateS j hj
        exact ⟨u, v, hu, hv, e2, e1⟩,
      SLf_in n m C.gates, bwS, meetL⟩
  have gen : ∀ (E : Finset (Fin n × Fin m)) (Dset : Finset (Fin k)),
      (∀ q ∈ E, inc q.1 q.2 = true ∧
        C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++
          List.ofFn (fun v : Fin m => decide (v = q.2))) = true) →
      (∀ t, (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) →
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true) → t ∈ Dset) →
      Dset.card ≤ k →
      E.card ≤ s + k + Dset.card ∧ (k ≤ T + 1 → E.card ≤ C.size + 1) := by
    intro E Dset hE hD hDk
    have key : E.card ≤ s + (k + Dset.card) :=
      final (⟨inc, n + m, s, SPf n m C.gates, SLf n m C.gates, A, B⟩ : Side n m k) hOK hOK' E Dset
        (by
          intro q hq
          obtain ⟨hinc, hev⟩ := hE q hq
          refine ⟨hinc, ?_⟩
          have e1 : (fun u : Fin n => decide (u = q.1)) =
              (fun u => decide (u ∈ ({q.1} : Finset (Fin n)))) := by
            funext u
            simp
          have e2 : (fun v : Fin m => decide (v = q.2)) =
              (fun v => decide (v ∈ ({q.2} : Finset (Fin m)))) := by
            funext v
            simp
          rw [e1, e2, ofFn_zin, evi] at hev
          obtain ⟨i1, j1, hlt, ⟨⟨pa, hpa, hm1⟩, ⟨lb, hlb, hm2⟩⟩, ⟨⟨pa', hpa', hm3⟩, ⟨lb', hlb', hm4⟩⟩⟩ := hev
          rw [Finset.mem_singleton] at hm1 hm2 hm3 hm4
          subst hm1 hm2
          rw [hm3] at hpa'
          rw [hm4] at hlb'
          exact ⟨i1, j1, ne_of_lt hlt, hpa, hpa', hlb, hlb'⟩)
        (fun t h1 h2 => hD t h1 h2)
    refine ⟨by omega, fun hkT => ?_⟩
    rw [hsz]
    omega
  refine gen _ _ ?_ ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro t h1 h2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, h1, h2⟩
  · exact (Finset.card_filter_le _ _).trans (by simp)


end PEqualNP.Outside.L_meta_3063_aux

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
  exact PEqualNP.Outside.L_meta_3063_aux.main
