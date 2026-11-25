import Mathlib
import PEqualNP.Defs

-- Helpers adapted from the merged files Outside/L_meta_2970.lean (scan and linear-part lemmas)
-- and Outside/L_meta_1942.lean (supports, essential_bound, plane_support).

namespace PEqualNP.Outside.L_meta_7021

namespace BoolSums

open Finset Classical

noncomputable section NC

inductive Opd (V ι : Type) where
  | var : V → Opd V ι
  | wire : ι → Opd V ι
  | zero : Opd V ι
  | one : Opd V ι

variable {V ι : Type}

def Opd.ev (f : ι → (V → Bool) → Bool) (x : V → Bool) : Opd V ι → Bool
  | .var v => x v
  | .wire i => f i x
  | .zero => false
  | .one => true

structure Net (V ι : Type) where
  isAnd : ι → Bool
  left : ι → Opd V ι
  right : ι → Opd V ι
  rank : ι → ℕ
  f : ι → (V → Bool) → Bool
  hl : ∀ i j, left i = .wire j → rank j < rank i
  hr : ∀ i j, right i = .wire j → rank j < rank i
  hf : ∀ i x, f i x = if isAnd i then ((left i).ev f x && (right i).ev f x)
    else ((left i).ev f x || (right i).ev f x)

def Le (x y : V → Bool) : Prop := ∀ v, x v = true → y v = true

def Mono (g : (V → Bool) → Bool) : Prop := ∀ x y, Le x y → g x = true → g y = true

def single (a : V) : V → Bool := fun v => decide (v = a)

variable [Fintype V]

def Tset (g : (V → Bool) → Bool) : Finset V := univ.filter fun a => g (single a) = true

lemma mem_Tset {g : (V → Bool) → Bool} {a : V} : a ∈ Tset g ↔ g (single a) = true := by
  simp [Tset]

namespace Net

variable (N : Net V ι)

def opf (o : Opd V ι) : (V → Bool) → Bool := fun x => o.ev N.f x

lemma mono_wire : ∀ i, Mono (N.f i) := by
  intro i
  induction' h : N.rank i using Nat.strong_induction_on with r ih generalizing i
  have hop : ∀ o : Opd V ι, (∀ j, o = .wire j → N.rank j < r) → Mono (N.opf o) := by
    intro o ho x y hxy hx
    cases o with
    | var v => exact hxy v hx
    | wire j => exact ih _ (ho j rfl) j rfl x y hxy hx
    | zero => simp [opf, Opd.ev] at hx
    | one => rfl
  have hL := hop (N.left i) (fun j hj => h ▸ N.hl i j hj)
  have hR := hop (N.right i) (fun j hj => h ▸ N.hr i j hj)
  intro x y hxy hx
  rw [N.hf] at hx ⊢
  by_cases ha : N.isAnd i = true
  · simp only [ha, if_true, Bool.and_eq_true] at hx ⊢
    exact ⟨hL x y hxy hx.1, hR x y hxy hx.2⟩
  · simp only [ha, Bool.false_eq_true, if_false, Bool.or_eq_true] at hx ⊢
    exact hx.imp (hL x y hxy) (hR x y hxy)

lemma mono_opf (o : Opd V ι) : Mono (N.opf o) := by
  intro x y hxy hx
  cases o with
  | var v => exact hxy v hx
  | wire j => exact N.mono_wire j x y hxy hx
  | zero => simp [opf, Opd.ev] at hx
  | one => rfl

lemma f_and {i : ι} (h : N.isAnd i = true) (x : V → Bool) :
    N.f i x = true ↔ N.opf (N.left i) x = true ∧ N.opf (N.right i) x = true := by
  rw [N.hf]; simp [h, opf]

lemma f_or {i : ι} (h : N.isAnd i = false) (x : V → Bool) :
    N.f i x = true ↔ N.opf (N.left i) x = true ∨ N.opf (N.right i) x = true := by
  rw [N.hf]; simp [h, opf]

lemma T_or {i : ι} (h : N.isAnd i = false) :
    Tset (N.f i) ⊆ Tset (N.opf (N.left i)) ∪ Tset (N.opf (N.right i)) := by
  intro a ha
  rw [mem_union, mem_Tset, mem_Tset]
  exact (N.f_or h _).mp (mem_Tset.mp ha)

lemma T_and_left {i : ι} (h : N.isAnd i = true) : Tset (N.f i) ⊆ Tset (N.opf (N.left i)) :=
  fun _ ha => mem_Tset.mpr ((N.f_and h _).mp (mem_Tset.mp ha)).1

lemma T_and_right {i : ι} (h : N.isAnd i = true) : Tset (N.f i) ⊆ Tset (N.opf (N.right i)) :=
  fun _ ha => mem_Tset.mpr ((N.f_and h _).mp (mem_Tset.mp ha)).2

variable [Fintype ι]

def ind (Z : Finset V) : V → Bool := fun v => decide (v ∈ Z)

lemma ind_single (a : V) : ind ({a} : Finset V) = single a := by
  funext v; simp [ind, single]

lemma ind_le {Z Z' : Finset V} (h : Z ⊆ Z') : Le (ind Z) (ind Z') := by
  intro v hv
  simp only [ind, decide_eq_true_eq] at hv ⊢
  exact h hv

def Dirt (S : Finset V) (g : (V → Bool) → Bool) (m : ℕ) : Prop :=
  ∃ Z : Finset V, Disjoint Z S ∧ Z.card ≤ m ∧ g (ind Z) = true

lemma Dirt.mono {S : Finset V} {g : (V → Bool) → Bool} {m m' : ℕ} (h : Dirt S g m)
    (hm : m ≤ m') : Dirt S g m' := by
  obtain ⟨Z, h1, h2, h3⟩ := h
  exact ⟨Z, h1, h2.trans hm, h3⟩

lemma T_sub_of_not_dirt {S : Finset V} {g : (V → Bool) → Bool} (h : ¬ Dirt S g 1) :
    Tset g ⊆ S := by
  intro a ha
  by_contra hn
  exact h ⟨{a}, by simpa using hn, by simp, by rw [ind_single]; exact mem_Tset.mp ha⟩

def mid (S : Finset V) : Finset ι :=
  univ.filter fun i => 2 ≤ (Tset (N.f i) ∩ S).card ∧ ¬ Dirt S (N.f i) 1

lemma mem_mid {S : Finset V} {i : ι} :
    i ∈ N.mid S ↔ 2 ≤ (Tset (N.f i) ∩ S).card ∧ ¬ Dirt S (N.f i) 1 := by simp [mid]

def smA (S : Finset V) (o : Opd V ι) : Finset V :=
  if (Tset (N.opf o) ∩ S).card ≤ 1 then Tset (N.opf o) ∩ S else ∅

def smB (S : Finset V) (o : Opd V ι) : Finset V :=
  if h : Dirt S (N.opf o) 1 then h.choose else ∅

lemma smA_card (S : Finset V) (o : Opd V ι) : (N.smA S o).card ≤ 1 := by
  unfold smA
  split_ifs with h
  · exact h
  · simp

lemma smB_card (S : Finset V) (o : Opd V ι) : (N.smB S o).card ≤ 1 := by
  unfold smB
  split_ifs with h
  · exact h.choose_spec.2.1
  · simp

lemma smB_disj (S : Finset V) (o : Opd V ι) : Disjoint (N.smB S o) S := by
  unfold smB
  split_ifs with h
  · exact h.choose_spec.1
  · simp

def LA (S : Finset V) : Finset V :=
  (N.mid S).biUnion fun i => N.smA S (N.left i) ∪ N.smA S (N.right i)

def LB (S : Finset V) : Finset V :=
  (N.mid S).biUnion fun i => N.smB S (N.left i) ∪ N.smB S (N.right i)

lemma LA_card (S : Finset V) : (N.LA S).card ≤ 2 * (N.mid S).card := by
  unfold LA
  calc _ ≤ ∑ i ∈ N.mid S, (N.smA S (N.left i) ∪ N.smA S (N.right i)).card := card_biUnion_le
    _ ≤ ∑ _i ∈ N.mid S, 2 := sum_le_sum fun i _ => by
        have h0 := card_union_le (N.smA S (N.left i)) (N.smA S (N.right i))
        have h1 := N.smA_card S (N.left i)
        have h2 := N.smA_card S (N.right i)
        omega
    _ = 2 * (N.mid S).card := by simp [mul_comm]

lemma LB_card (S : Finset V) : (N.LB S).card ≤ 2 * (N.mid S).card := by
  unfold LB
  calc _ ≤ ∑ i ∈ N.mid S, (N.smB S (N.left i) ∪ N.smB S (N.right i)).card := card_biUnion_le
    _ ≤ ∑ _i ∈ N.mid S, 2 := sum_le_sum fun i _ => by
        have h0 := card_union_le (N.smB S (N.left i)) (N.smB S (N.right i))
        have h1 := N.smB_card S (N.left i)
        have h2 := N.smB_card S (N.right i)
        omega
    _ = 2 * (N.mid S).card := by simp [mul_comm]

lemma LB_disj (S : Finset V) : Disjoint (N.LB S) S := by
  unfold LB
  rw [disjoint_biUnion_left]
  intro i _
  rw [disjoint_union_left]
  exact ⟨N.smB_disj S _, N.smB_disj S _⟩

lemma opd_cases (S : Finset V) (o : Opd V ι) :
    (Tset (N.opf o) ∩ S).card ≤ 1 ∨ Dirt S (N.opf o) 1 ∨ ∃ j, o = .wire j ∧ j ∈ N.mid S := by
  by_cases h1 : (Tset (N.opf o) ∩ S).card ≤ 1
  · exact Or.inl h1
  by_cases h2 : Dirt S (N.opf o) 1
  · exact Or.inr (Or.inl h2)
  right; right
  cases o with
  | var v =>
    exfalso; apply h1
    have hsub : Tset (N.opf (.var v : Opd V ι)) ⊆ {v} := by
      intro a ha
      have := mem_Tset.mp ha
      simp only [opf, Opd.ev, single, decide_eq_true_eq] at this
      simp [this]
    have hsub' : Tset (N.opf (.var v : Opd V ι)) ∩ S ⊆ {v} := fun a ha => hsub (mem_inter.mp ha).1
    have h3 := card_le_card hsub'
    simpa using h3
  | wire j =>
    have h1' : ¬ (Tset (N.f j) ∩ S).card ≤ 1 := h1
    have h2' : ¬ Dirt S (N.f j) 1 := h2
    exact ⟨j, rfl, N.mem_mid.mpr ⟨by omega, h2'⟩⟩
  | zero =>
    exfalso; apply h1
    have : Tset (N.opf (.zero : Opd V ι)) = ∅ := by
      ext a; simp [mem_Tset, opf, Opd.ev]
    simp [this]
  | one => exact (h2 ⟨∅, by simp, by simp, rfl⟩).elim

lemma mid_claim (S : Finset V) : ∀ i, i ∈ N.mid S →
    Tset (N.f i) ∩ S ⊆ N.LA S ∨ N.f i (ind (N.LB S)) = true := by
  intro i
  induction' h : N.rank i using Nat.strong_induction_on with r ih generalizing i
  intro hi
  have child : ∀ o : Opd V ι, (o = N.left i ∨ o = N.right i) →
      Tset (N.opf o) ∩ S ⊆ N.LA S ∨ N.opf o (ind (N.LB S)) = true := by
    intro o ho
    rcases N.opd_cases S o with h1 | h2 | ⟨j, hoj, hj⟩
    · left
      have hsm : N.smA S o = Tset (N.opf o) ∩ S := by simp [smA, h1]
      rw [← hsm]
      intro a ha
      refine mem_biUnion.mpr ⟨i, hi, ?_⟩
      rcases ho with ho | ho
      · exact mem_union_left _ (ho ▸ ha)
      · exact mem_union_right _ (ho ▸ ha)
    · right
      have hsub : N.smB S o ⊆ N.LB S := by
        intro a ha
        refine mem_biUnion.mpr ⟨i, hi, ?_⟩
        rcases ho with ho | ho
        · exact mem_union_left _ (ho ▸ ha)
        · exact mem_union_right _ (ho ▸ ha)
      have hsm : N.smB S o = h2.choose := by unfold smB; exact dif_pos h2
      have htrue : N.opf o (ind (N.smB S o)) = true := by
        rw [hsm]; exact h2.choose_spec.2.2
      exact N.mono_opf o _ _ (ind_le hsub) htrue
    · have hlt : N.rank j < r := by
        rcases ho with ho | ho
        · exact h ▸ N.hl i j (ho ▸ hoj)
        · exact h ▸ N.hr i j (ho ▸ hoj)
      subst hoj
      exact ih _ hlt j rfl hj
  have hL := child (N.left i) (Or.inl rfl)
  have hR := child (N.right i) (Or.inr rfl)
  by_cases ha : N.isAnd i = true
  · rcases hL with hL | hL
    · exact Or.inl ((inter_subset_inter (N.T_and_left ha) (subset_refl S)).trans hL)
    rcases hR with hR | hR
    · exact Or.inl ((inter_subset_inter (N.T_and_right ha) (subset_refl S)).trans hR)
    · exact Or.inr ((N.f_and ha _).mpr ⟨hL, hR⟩)
  · have ha' : N.isAnd i = false := by simpa using ha
    rcases hL with hL | hL
    · rcases hR with hR | hR
      · left
        intro a hm
        obtain ⟨h1, h2⟩ := mem_inter.mp hm
        rcases mem_union.mp (N.T_or ha' h1) with h3 | h3
        · exact hL (mem_inter.mpr ⟨h3, h2⟩)
        · exact hR (mem_inter.mpr ⟨h3, h2⟩)
      · exact Or.inr ((N.f_or ha' _).mpr (Or.inr hR))
    · exact Or.inr ((N.f_or ha' _).mpr (Or.inl hL))

lemma approx_one (S : Finset V) (o : Opd V ι) :
    (Tset (N.opf o) ∩ S).card ≤ 2 * (N.mid S).card + 1 ∨
      Dirt S (N.opf o) (2 * (N.mid S).card + 1) := by
  rcases N.opd_cases S o with h1 | h2 | ⟨j, hoj, hj⟩
  · left; omega
  · right; exact h2.mono (by omega)
  · subst hoj
    rcases N.mid_claim S j hj with h | h
    · left
      exact le_trans (card_le_card h) ((N.LA_card S).trans (by omega))
    · right
      exact ⟨N.LB S, N.LB_disj S, (N.LB_card S).trans (by omega), h⟩

lemma tame_or_dirty (S : Finset V) (o : Opd V ι) :
    (Tset (N.opf o) ∩ S).card ≤ 1 ∨ Dirt S (N.opf o) 1 ∨
      Tset (N.opf o) ∩ S ⊆ N.LA S ∨ N.opf o (ind (N.LB S)) = true := by
  rcases N.opd_cases S o with h1 | h2 | ⟨j, hoj, hj⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · subst hoj
    rcases N.mid_claim S j hj with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem sum_LA_le {κ : Type} [Fintype κ] (Nb : κ → Finset V)
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1) :
    ∑ c, (N.LA (Nb c)).card ≤ 2 * Fintype.card ι := by
  have hpair : ∀ c ∈ (univ : Finset κ), ∀ c' ∈ (univ : Finset κ), c ≠ c' →
      Disjoint (N.mid (Nb c)) (N.mid (Nb c')) := by
    intro c _ c' _ hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨h2, _⟩ := N.mem_mid.mp hi
    obtain ⟨_, hn'⟩ := N.mem_mid.mp hi'
    have hsub : Tset (N.f i) ∩ Nb c ⊆ Nb c ∩ Nb c' := fun a ha =>
      mem_inter.mpr ⟨(mem_inter.mp ha).2, T_sub_of_not_dirt hn' (mem_inter.mp ha).1⟩
    have := card_le_card hsub
    have := hdisj c c' hne
    omega
  have hsum : ∑ c, (N.mid (Nb c)).card ≤ Fintype.card ι := by
    rw [← card_biUnion hpair]
    exact card_le_univ _
  calc ∑ c, (N.LA (Nb c)).card ≤ ∑ c, 2 * (N.mid (Nb c)).card :=
        sum_le_sum fun c _ => N.LA_card (Nb c)
    _ = 2 * ∑ c, (N.mid (Nb c)).card := by rw [mul_sum]
    _ ≤ 2 * Fintype.card ι := by omega

theorem sum_min_le {κ : Type} [Fintype κ] (Nb : κ → Finset V)
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1) (σ : ℕ)
    (h : κ → Opd V ι)
    (hsound : ∀ c, ∀ Z : Finset V, Disjoint Z (Nb c) → Z.card < σ →
      N.opf (h c) (ind Z) = false) :
    ∑ c, min (Tset (N.opf (h c)) ∩ Nb c).card σ ≤ 2 * Fintype.card ι + Fintype.card κ := by
  have hterm : ∀ c, min (Tset (N.opf (h c)) ∩ Nb c).card σ ≤ 2 * (N.mid (Nb c)).card + 1 := by
    intro c
    rcases N.approx_one (Nb c) (h c) with h1 | ⟨Z, hd, hc, ht⟩
    · exact (Nat.min_le_left _ _).trans h1
    · have hσ : σ ≤ Z.card := by
        by_contra hlt
        have hf := hsound c Z hd (by omega)
        rw [hf] at ht
        exact Bool.false_ne_true ht
      exact (Nat.min_le_right _ _).trans (by omega)
  have hpair : ∀ c ∈ (univ : Finset κ), ∀ c' ∈ (univ : Finset κ), c ≠ c' →
      Disjoint (N.mid (Nb c)) (N.mid (Nb c')) := by
    intro c _ c' _ hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨h2, _⟩ := N.mem_mid.mp hi
    obtain ⟨_, hn'⟩ := N.mem_mid.mp hi'
    have hsub : Tset (N.f i) ∩ Nb c ⊆ Nb c ∩ Nb c' := fun a ha =>
      mem_inter.mpr ⟨(mem_inter.mp ha).2, T_sub_of_not_dirt hn' (mem_inter.mp ha).1⟩
    have := card_le_card hsub
    have := hdisj c c' hne
    omega
  have hsum : ∑ c, (N.mid (Nb c)).card ≤ Fintype.card ι := by
    rw [← card_biUnion hpair]
    exact card_le_univ _
  calc ∑ c, min (Tset (N.opf (h c)) ∩ Nb c).card σ ≤ ∑ c, (2 * (N.mid (Nb c)).card + 1) :=
        sum_le_sum fun c _ => hterm c
    _ = 2 * ∑ c, (N.mid (Nb c)).card + Fintype.card κ := by
        rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ 2 * Fintype.card ι + Fintype.card κ := by omega

end Net

section Adjoint

variable {X Y : Type} {s : ℕ}

def lift0 (x : X → Bool) : X ⊕ Y → Bool := Sum.elim x (fun _ => false)

def lift1 (x : X → Bool) (c : Y) : X ⊕ Y → Bool := Sum.elim x (fun c' => decide (c' = c))

abbrev Rd (s : ℕ) := Fin s × Bool

abbrev J (s : ℕ) := Fin s ⊕ (Rd s ⊕ Rd s)

variable (N : Net (X ⊕ Y) (Fin s))

def opd (t : Rd s) : Opd (X ⊕ Y) (Fin s) := if t.2 then N.right t.1 else N.left t.1

def oth (t : Rd s) : Opd (X ⊕ Y) (Fin s) := if t.2 then N.left t.1 else N.right t.1

def Side (x : X → Bool) (t : Rd s) : Prop :=
  N.isAnd t.1 = false ∨ N.opf (oth N t) (lift0 x) = true

inductive AdjP (out : Fin s) (x : X → Bool) : Fin s → Prop
  | root : AdjP out x out
  | step (t : Rd s) (w : Fin s) : AdjP out x t.1 → opd N t = .wire w → Side N x t → AdjP out x w

def Cp (out : Fin s) (x : X → Bool) (t : Rd s) : Prop := AdjP N out x t.1 ∧ Side N x t

def key (t : Rd s) : ℕ := 2 * t.1.val + (if t.2 then 1 else 0)

lemma key_inj : Function.Injective (key (s := s)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  simp only [key] at h
  have : i.val = j.val ∧ b = c := by
    cases b <;> cases c <;> simp at h ⊢ <;> omega
  exact Prod.ext (Fin.ext this.1) this.2

lemma key_lt (t : Rd s) : key t < 2 * s := by
  have := t.1.isLt
  simp only [key]; split_ifs <;> omega

lemma key_ge (t : Rd s) : 2 * t.1.val ≤ key t := by simp [key]

lemma key_le (t : Rd s) : key t ≤ 2 * t.1.val + 1 := by
  simp only [key]; split_ifs <;> omega

def readers (o : Opd (X ⊕ Y) (Fin s)) : Finset (Rd s) := univ.filter fun t => opd N t = o

lemma mem_readers {o : Opd (X ⊕ Y) (Fin s)} {t : Rd s} : t ∈ readers N o ↔ opd N t = o := by
  simp [readers]

def Ep (out : Fin s) (x : X → Bool) (t : Rd s) : Prop :=
  ∃ t' ∈ readers N (opd N t), key t ≤ key t' ∧ Cp N out x t'

def TargetAdj (out : Fin s) (x : X → Bool) (o : Opd (X ⊕ Y) (Fin s)) : Prop :=
  o = .wire out ∨ ∃ t ∈ readers N o, Cp N out x t

lemma adjP_iff (out : Fin s) (x : X → Bool) (w : Fin s) :
    AdjP N out x w ↔ TargetAdj N out x (.wire w) := by
  constructor
  · intro h
    cases h with
    | root => exact Or.inl rfl
    | step t _ hp ho hs => exact Or.inr ⟨t, (mem_readers N).mpr ho, hp, hs⟩
  · rintro (h | ⟨t, ht, hp, hs⟩)
    · have : w = out := by injection h
      exact this ▸ AdjP.root
    · exact AdjP.step t w hp ((mem_readers N).mp ht) hs

def firstR (o : Opd (X ⊕ Y) (Fin s)) (h : (readers N o).Nonempty) : Rd s :=
  Classical.choose (exists_min_image _ key h)

lemma firstR_spec (o : Opd (X ⊕ Y) (Fin s)) (h : (readers N o).Nonempty) :
    firstR N o h ∈ readers N o ∧ ∀ t ∈ readers N o, key (firstR N o h) ≤ key t :=
  Classical.choose_spec (exists_min_image _ key h)

def after (t : Rd s) : Finset (Rd s) := (readers N (opd N t)).filter fun t' => key t < key t'

def nextR (t : Rd s) (h : (after N t).Nonempty) : Rd s :=
  Classical.choose (exists_min_image _ key h)

lemma nextR_spec (t : Rd s) (h : (after N t).Nonempty) :
    nextR N t h ∈ after N t ∧ ∀ t' ∈ after N t, key (nextR N t h) ≤ key t' :=
  Classical.choose_spec (exists_min_image _ key h)

def tr0 : Opd (X ⊕ Y) (Fin s) → Opd X (J s)
  | .var (.inl a) => .var a
  | .var (.inr _) => .zero
  | .wire j => .wire (.inl j)
  | .zero => .zero
  | .one => .one

def adjOp (out : Fin s) (o : Opd (X ⊕ Y) (Fin s)) : Opd X (J s) :=
  if o = .wire out then .one
  else if h : (readers N o).Nonempty then .wire (.inr (.inr (firstR N o h))) else .zero

def Mf (out : Fin s) : J s → (X → Bool) → Bool
  | .inl i => fun x => N.f i (lift0 x)
  | .inr (.inl t) => fun x => decide (Cp N out x t)
  | .inr (.inr t) => fun x => decide (Ep N out x t)

lemma tr0_ev (out : Fin s) (o : Opd (X ⊕ Y) (Fin s)) (x : X → Bool) :
    (tr0 o).ev (Mf N out) x = o.ev N.f (lift0 x) := by
  cases o with
  | var v => cases v <;> rfl
  | wire j => rfl
  | zero => rfl
  | one => rfl

lemma tr0_wire {o : Opd (X ⊕ Y) (Fin s)} {j : J s} (h : tr0 o = .wire j) :
    ∃ j0, o = .wire j0 ∧ j = .inl j0 := by
  cases o with
  | var v => cases v <;> simp [tr0] at h
  | wire j0 => simp only [tr0, Opd.wire.injEq] at h; exact ⟨j0, rfl, h.symm⟩
  | zero => simp [tr0] at h
  | one => simp [tr0] at h

lemma adj_ev (out : Fin s) (o : Opd (X ⊕ Y) (Fin s)) (x : X → Bool) :
    (adjOp N out o).ev (Mf N out) x = true ↔ TargetAdj N out x o := by
  unfold adjOp
  split_ifs with h1 h2
  · simp [Opd.ev, TargetAdj, h1]
  · have hs := firstR_spec N o h2
    have ho : opd N (firstR N o h2) = o := (mem_readers N).mp hs.1
    simp only [Opd.ev, Mf, decide_eq_true_eq, Ep, ho]
    constructor
    · rintro ⟨t', ht', _, hc⟩
      exact Or.inr ⟨t', ht', hc⟩
    · rintro (h | ⟨t, ht, hc⟩)
      · exact absurd h h1
      · exact ⟨t, ht, hs.2 t ht, hc⟩
  · simp only [Opd.ev, Bool.false_eq_true, false_iff]
    rintro (h | ⟨t, ht, _⟩)
    · exact h1 h
    · exact h2 ⟨t, ht⟩

variable (hrank : ∀ i, N.rank i = i.val)
include hrank

lemma reader_lt {t : Rd s} {w : Fin s} (h : opd N t = .wire w) : w.val < t.1.val := by
  unfold opd at h
  split_ifs at h
  · have := N.hr _ _ h; rwa [hrank, hrank] at this
  · have := N.hl _ _ h; rwa [hrank, hrank] at this

omit hrank

variable [Fintype X] [Fintype Y]

lemma gate_true {t : Rd s} {z : X ⊕ Y → Bool} (h1 : N.opf (opd N t) z = true)
    (h2 : N.isAnd t.1 = false ∨ N.opf (oth N t) z = true) : N.f t.1 z = true := by
  obtain ⟨i, b⟩ := t
  by_cases ha : N.isAnd i = true
  · have h2' : N.opf (oth N (i, b)) z = true := by
      rcases h2 with h | h
      · simp_all
      · exact h
    rw [N.f_and ha]
    cases b <;> simp_all [opd, oth]
  · have ha' : N.isAnd i = false := by simpa using ha
    rw [N.f_or ha']
    cases b <;> simp_all [opd, oth]

lemma adjP_sound (out : Fin s) (x : X → Bool) (w : Fin s) (h : AdjP N out x w) :
    ∀ z, Le (lift0 x) z → N.f w z = true → N.f out z = true := by
  induction h with
  | root => exact fun _ _ h => h
  | step t w _ ho hs ih =>
    intro z hz hw
    apply ih z hz
    apply gate_true N
    · rw [ho]; exact hw
    · exact hs.imp id (fun h => N.mono_opf _ _ _ hz h)

def adjNet (out : Fin s) : Net X (J s) where
  isAnd := fun
    | .inl i => N.isAnd i
    | .inr (.inl _) => true
    | .inr (.inr _) => false
  left := fun
    | .inl i => tr0 (N.left i)
    | .inr (.inl t) => adjOp N out (.wire t.1)
    | .inr (.inr t) => .wire (.inr (.inl t))
  right := fun
    | .inl i => tr0 (N.right i)
    | .inr (.inl t) => if N.isAnd t.1 then tr0 (oth N t) else .one
    | .inr (.inr t) =>
      if h : (after N t).Nonempty then .wire (.inr (.inr (nextR N t h))) else .zero
  rank := fun
    | .inl i => i.val
    | .inr (.inl t) => s + 2 * (2 * s - key t)
    | .inr (.inr t) => s + 2 * (2 * s - key t) + 1
  f := Mf N out
  hl := by
    intro i j h
    rcases i with i | t | t
    · obtain ⟨j0, hj0, rfl⟩ := tr0_wire h
      have := N.hl _ _ hj0
      rw [hrank, hrank] at this
      exact this
    · simp only [adjOp] at h
      split_ifs at h with h1 h2
      · have hj : j = .inr (.inr (firstR N (.wire t.1) h2)) := by injection h with h; exact h.symm
        subst hj
        have hs := firstR_spec N (.wire t.1) h2
        have hlt := reader_lt N hrank ((mem_readers N).mp hs.1)
        have k1 := key_ge (firstR N (.wire t.1) h2)
        have k2 := key_lt (firstR N (.wire t.1) h2)
        have k3 := key_le t
        show s + 2 * (2 * s - key (firstR N (.wire t.1) h2)) + 1 < s + 2 * (2 * s - key t)
        omega
    · have hj : j = .inr (.inl t) := by injection h with h; exact h.symm
      subst hj
      show s + 2 * (2 * s - key t) < s + 2 * (2 * s - key t) + 1
      omega
  hr := by
    intro i j h
    rcases i with i | t | t
    · obtain ⟨j0, hj0, rfl⟩ := tr0_wire h
      have := N.hr _ _ hj0
      rw [hrank, hrank] at this
      exact this
    · simp only at h
      split_ifs at h with h1
      · obtain ⟨j0, _, rfl⟩ := tr0_wire h
        show j0.val < s + 2 * (2 * s - key t)
        have := j0.isLt
        omega
    · simp only at h
      split_ifs at h with h1
      have hj : j = .inr (.inr (nextR N t h1)) := by injection h with h; exact h.symm
      subst hj
      have hs := (nextR_spec N t h1).1
      simp only [after, mem_filter] at hs
      have k2 := key_lt (nextR N t h1)
      show s + 2 * (2 * s - key (nextR N t h1)) + 1 < s + 2 * (2 * s - key t) + 1
      omega
  hf := by
    intro i x
    rcases i with i | t | t
    · show N.f i (lift0 x) = _
      rw [N.hf]
      simp only [tr0_ev]
    · show decide (Cp N out x t) = _
      simp only [if_true]
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.and_eq_true, adj_ev, ← adjP_iff, Cp, Side]
      by_cases ha : N.isAnd t.1 = true
      · simp [ha, tr0_ev, Net.opf]
      · simp [ha, Opd.ev]
    · show decide (Ep N out x t) = _
      simp only [Bool.false_eq_true, if_false]
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, Opd.ev, Mf]
      constructor
      · rintro ⟨t', ht', hk, hc⟩
        by_cases hkk : key t = key t'
        · have := key_inj hkk
          subst this
          exact Or.inl hc
        · right
          have hmem : t' ∈ after N t := by
            simp only [after, mem_filter]; exact ⟨ht', by omega⟩
          have hne : (after N t).Nonempty := ⟨t', hmem⟩
          rw [dif_pos hne]
          have hs := nextR_spec N t hne
          have hin := hs.1
          simp only [after, mem_filter] at hin
          have ho : opd N (nextR N t hne) = opd N t := (mem_readers N).mp hin.1
          simp only [Opd.ev, Mf, decide_eq_true_eq, Ep, ho]
          exact ⟨t', ht', hs.2 t' hmem, hc⟩
      · rintro (hc | h)
        · exact ⟨t, (mem_readers N).mpr rfl, le_refl _, hc⟩
        · split_ifs at h with hne
          · have hs := nextR_spec N t hne
            have hin := hs.1
            simp only [after, mem_filter] at hin
            have ho : opd N (nextR N t hne) = opd N t := (mem_readers N).mp hin.1
            simp only [Opd.ev, Mf, decide_eq_true_eq, Ep, ho] at h
            obtain ⟨t', ht', hk, hc⟩ := h
            exact ⟨t', ht', by omega, hc⟩

def Captured (out : Fin s) (a : X) (c : Y) : Prop :=
  ∃ t : Rd s, opd N t = .var (.inr c) ∧ Cp N out (single a) t

include hrank in
theorem captured_min_le (out : Fin s) (E : X → Y → Prop) (σ : ℕ)
    (hC4 : ∀ c c' : Y, c ≠ c' → ∀ a b : X, E a c → E a c' → E b c → E b c' → a = b)
    (hsound : ∀ (Z : Finset X) (c : Y), Z.card < σ →
      N.f out (lift1 (Net.ind Z) c) = true → ∃ a ∈ Z, E a c) :
    ∑ c : Y, min ((univ : Finset X).filter fun a => Captured N out a c ∧ E a c).card σ
      ≤ 10 * s + Fintype.card Y := by
  let M := adjNet N hrank out
  let Nb : Y → Finset X := fun c => univ.filter fun a => E a c
  let h : Y → Opd X (J s) := fun c => adjOp N out (.var (.inr c))
  have hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1 := by
    intro c c' hne
    rw [card_le_one]
    intro a ha b hb
    simp only [Nb, mem_inter, mem_filter, mem_univ, true_and] at ha hb
    exact hC4 c c' hne a b ha.1 ha.2 hb.1 hb.2
  have hs : ∀ c, ∀ Z : Finset X, Disjoint Z (Nb c) → Z.card < σ →
      M.opf (h c) (Net.ind Z) = false := by
    intro c Z hd hZ
    rw [Bool.eq_false_iff]
    intro hx
    have hx' : (adjOp N out (.var (.inr c))).ev (Mf N out) (Net.ind Z) = true := hx
    rw [adj_ev] at hx'
    rcases hx' with h0 | ⟨t, ht, hp, hs⟩
    · cases h0
    · have ho := (mem_readers N).mp ht
      have hz : Le (lift0 (Net.ind Z)) (lift1 (Net.ind Z) c) := by
        intro v hv
        cases v with
        | inl a => exact hv
        | inr c' => simp [lift0] at hv
      have hg : N.f t.1 (lift1 (Net.ind Z) c) = true := by
        apply gate_true N
        · rw [ho]; simp [Net.opf, Opd.ev, lift1]
        · exact hs.imp id (fun h => N.mono_opf _ _ _ hz h)
      obtain ⟨a, haZ, hE⟩ := hsound Z c hZ (adjP_sound N out _ t.1 hp _ hz hg)
      exact Finset.disjoint_left.mp hd haZ (by simp [Nb, hE])
  have key := M.sum_min_le Nb hdisj σ h hs
  have hcard : Fintype.card (J s) = 5 * s := by
    simp [J, Rd, Fintype.card_sum, Fintype.card_prod]; omega
  calc ∑ c : Y, min ((univ : Finset X).filter fun a => Captured N out a c ∧ E a c).card σ
      ≤ ∑ c, min (Tset (M.opf (h c)) ∩ Nb c).card σ := by
        apply sum_le_sum
        intro c _
        apply min_le_min _ le_rfl
        apply card_le_card
        intro a ha
        simp only [mem_filter, mem_univ, true_and] at ha
        obtain ⟨⟨t, ho, hc⟩, hE⟩ := ha
        rw [mem_inter, mem_Tset]
        refine ⟨?_, by simp [Nb, hE]⟩
        show (adjOp N out (.var (.inr c))).ev (Mf N out) (single a) = true
        rw [adj_ev]
        exact Or.inr ⟨t, (mem_readers N).mpr ho, hc⟩
    _ ≤ 2 * Fintype.card (J s) + Fintype.card Y := key
    _ = 10 * s + Fintype.card Y := by rw [hcard]; omega

end Adjoint

end NC

end BoolSums

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

def pairList (N : ℕ) (p l : Fin N) : List Bool :=
  (List.range (N + N)).map fun i => i == p.val || i == N + l.val

def lpInit (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  ((pairList N p l).zipIdx).map fun (b, i) => if decide (i < N) then (false, b) else (b, false)

def lpList (C : Circuit) (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  linearParts C (fun k => decide (k < N)) (pairList N p l)

def lpAt (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) : Bool × Bool :=
  (lpList C N p l).getD w (false, false)

lemma lineSingle_eq_lpAt (C : Circuit) (N : ℕ) (p l : Fin N) :
    lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = (lpAt C N p l C.output).2 := rfl

lemma lpInit_length (N : ℕ) (p l : Fin N) : (lpInit N p l).length = N + N := by
  simp [lpInit, pairList]

lemma lpInit_getD (N : ℕ) (p l : Fin N) (i : ℕ) (hi : i < N + N) :
    (lpInit N p l).getD i (false, false) =
      if i < N then (false, decide (i = p.val)) else (decide (i = N + l.val), false) := by
  have hl1 : (pairList N p l).length = N + N := by simp [pairList]
  have hl2 : ((pairList N p l).zipIdx).length = N + N := by simp [hl1]
  rw [lpInit, List.getD_eq_getElem _ _ (by simp [hl2, hi]), List.getElem_map]
  have hz : ((pairList N p l).zipIdx)[i]'(by omega) = ((pairList N p l)[i]'(by omega), i) := by
    simp [List.getElem_zipIdx]
  rw [hz]
  dsimp only
  unfold pairList
  rw [List.getElem_map, List.getElem_range]
  by_cases hlt : i < N
  · have hne : (i == N + l.val) = false := by
      simp
      omega
    simp only [hlt, hne, Bool.or_false, decide_true, ite_true]
    by_cases hep : i = p.val <;> simp [hep]
  · have hne : (i == p.val) = false := by
      simp
      omega
    simp only [hlt, hne, Bool.false_or, decide_false, Bool.false_eq_true, ite_false]
    by_cases hel : i = N + l.val <;> simp [hel]

def lineInput (N : ℕ) (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i.val = N + l.val)

def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma getD_map_fst (ws : List (Bool × Bool)) (i : ℕ) :
    (ws.map (·.1)).getD i false = (ws.getD i (false, false)).1 := by
  by_cases hi : i < ws.length
  · simp [hi]
  · have hle : ws.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hle)]

lemma boolStep_fst_linStep (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (linStep ws g).1 = boolStep (ws.map (·.1)) g := by
  rcases hg with hop | hop
  · simp only [linStep, boolStep, hop, GateOp.eval]
    have hfold : ∀ (l : List (Bool × Bool)) (b c : Bool),
        (l.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (b, c)).1 =
        (b && l.all (·.1)) := by
      intro l
      induction l with
      | nil => intro b c; simp
      | cons x xs ih =>
        intro b c
        simp only [List.foldl_cons, List.all_cons]
        rw [ih, Bool.and_assoc]
    rw [hfold, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi; rw [getD_map_fst]; exact h i hi
    · intro h i hi; rw [← getD_map_fst]; exact h i hi
  · simp only [linStep, boolStep, hop, GateOp.eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [getD_map_fst]; exact hit⟩
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [← getD_map_fst]; exact hit⟩

lemma scan_lin_fst (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (scan linStep gs ws).map (·.1) = scan boolStep gs (ws.map (·.1)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    rw [scan_cons, scan_cons, ih hgs]
    simp [boolStep_fst_linStep g hg ws]

lemma lpInit_map_fst (N : ℕ) (p l : Fin N) :
    (lpInit N p l).map (·.1) = List.ofFn (lineInput N l) := by
  apply List.ext_getElem
  · simp [lpInit_length]
  · intro i h1 h2
    have hi : i < N + N := by simpa [lpInit_length] using h1
    rw [List.getElem_map, List.getElem_ofFn]
    have hg := lpInit_getD N p l i hi
    rw [List.getD_eq_getElem _ _ (by simp [lpInit_length, hi])] at hg
    rw [hg]
    by_cases hlt : i < N
    · simp [hlt, lineInput]
      omega
    · simp [hlt, lineInput]

lemma lpAt_fst (C : Circuit) (hAO : AndOrOnly C) (N : ℕ) (p l : Fin N) (w : ℕ) :
    (lpAt C N p l w).1 = wireVal (N + N) C w (lineInput N l) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  change ((scan linStep C.gates (lpInit N p l)).getD w (false, false)).1 =
    (scan boolStep C.gates (List.ofFn (lineInput N l))).getD w false
  rw [← getD_map_fst, scan_lin_fst C.gates hAO, lpInit_map_fst]

lemma lpList_length (C : Circuit) (N : ℕ) (p l : Fin N) :
    (lpList C N p l).length = N + N + C.gates.length := by
  rw [lpList, linearParts_eq_scan, scan_length]
  change (lpInit N p l).length + C.gates.length = N + N + C.gates.length
  rw [lpInit_length]

lemma lpAt_ge (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    lpAt C N p l w = (false, false) := by
  rw [lpAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [lpList_length]; exact hw)]
  rfl

lemma lpAt_lt_len (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N + N) :
    lpAt C N p l w = (lpInit N p l).getD w (false, false) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  exact scan_prefix linStep C.gates (lpInit N p l) (false, false) w (by rw [lpInit_length]; exact hw)

lemma lpAt_snd_point (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N) :
    (lpAt C N p l w).2 = decide (w = p.val) := by
  rw [lpAt_lt_len C N p l w (by omega), lpInit_getD N p l w (by omega)]
  simp [hw]

lemma lpAt_snd_line (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    (lpAt C N p l w).2 = false := by
  rw [lpAt_lt_len C N p l w h2, lpInit_getD N p l w h2]
  have hnot : ¬ (w < N) := by omega
  simp [hnot]

lemma lpAt_gate {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) :
    lpAt C N p l (N + N + j) = linStep (lpList C N p l) C.gates[j] := by
  rw [lpAt, lpList, linearParts_eq_scan]
  have hlen : (lpInit N p l).length = N + N := lpInit_length N p l
  conv_lhs => rw [← hlen]
  apply scan_gate linStep C.gates (lpInit N p l) (false, false) j hj
  intro q1 q2 hq
  simp only [linStep]
  have hrb := hAO2.2.1 j hj
  have hcongr : C.gates[j].inputs.map (fun i => q1.getD i (false, false)) =
      C.gates[j].inputs.map (fun i => q2.getD i (false, false)) := by
    apply List.map_congr_left
    intro i hi
    apply hq
    rw [hlen]
    exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
  rw [hcongr]

lemma lpAt_snd_or {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    (lpAt C N p l (N + N + j)).2 =
      ((lpAt C N p l (opnd C j 0)).2 || (lpAt C N p l (opnd C j 1)).2) := by
  rw [lpAt_gate hAO2 p l hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [linStep, hop, hin, lpAt]

lemma lpAt_snd_and {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    (lpAt C N p l (N + N + j)).2 =
      ((wireVal (N + N) C (opnd C j 0) (lineInput N l) && (lpAt C N p l (opnd C j 1)).2) ||
       ((lpAt C N p l (opnd C j 0)).2 && wireVal (N + N) C (opnd C j 1) (lineInput N l))) := by
  rw [lpAt_gate hAO2 p l hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp only [linStep, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Bool.true_and, Bool.false_and, Bool.or_false]
  rw [← lpAt_fst C hAO2.1 N p l (opnd C j 0), ← lpAt_fst C hAO2.1 N p l (opnd C j 1)]
  rfl

lemma wireVal_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_scan, scan_length, List.length_ofFn]

lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  rw [wireVal, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wireVal_length]; exact hw)]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  rw [wireVal, wires_eq_scan, scan_prefix boolStep C.gates (List.ofFn x) false i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wireVal n C (n + j) x = boolStep (C.wires (List.ofFn x)) C.gates[j] := by
  rw [wireVal, wires_eq_scan]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := scan_gate boolStep C.gates (List.ofFn x) false j hj (by
    intro q1 q2 hq
    simp only [boolStep]
    have hrb := hAO2.2.1 j hj
    have hcongr : C.gates[j].inputs.map (fun i => q1.getD i false) =
        C.gates[j].inputs.map (fun i => q2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hq
      rw [hlen]
      exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
    rw [hcongr])
  simpa only [hlen] using h

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

open BoolSums

def toOpd (N : ℕ) (C : Circuit) (w : ℕ) : Opd (Fin N ⊕ Fin N) (Fin C.gates.length) :=
  if h : w < N then .var (.inr ⟨w, h⟩)
  else if h2 : w < N + N then .var (.inl ⟨w - N, by omega⟩)
  else if h3 : w - (N + N) < C.gates.length then .wire ⟨w - (N + N), h3⟩
  else .zero

def toIn {N : ℕ} (z : Fin N ⊕ Fin N → Bool) : Fin (N + N) → Bool :=
  fun i => if h : i.val < N then z (.inr ⟨i.val, h⟩) else z (.inl ⟨i.val - N, by omega⟩)

def bf (N : ℕ) (C : Circuit) (i : Fin C.gates.length) (z : Fin N ⊕ Fin N → Bool) : Bool :=
  wireVal (N + N) C (N + N + i.val) (toIn z)

lemma toOpd_ev (N : ℕ) (C : Circuit) (w : ℕ) (z : Fin N ⊕ Fin N → Bool) :
    (toOpd N C w).ev (bf N C) z = wireVal (N + N) C w (toIn z) := by
  unfold toOpd
  split_ifs with h h2 h3
  · rw [wireVal_input _ _ _ _ (by omega)]
    simp [Opd.ev, toIn, h]
  · rw [wireVal_input _ _ _ _ h2]
    simp [Opd.ev, toIn, h]
  · have hw : w = N + N + (w - (N + N)) := by omega
    conv_rhs => rw [hw]
    rfl
  · rw [wireVal_ge _ _ _ _ (by omega)]
    rfl

lemma toOpd_wire {N : ℕ} {C : Circuit} {w : ℕ} {j : Fin C.gates.length}
    (h : toOpd N C w = .wire j) : w = N + N + j.val := by
  unfold toOpd at h
  split_ifs at h with h1 h2 h3
  · injection h with h
    subst h
    show w = N + N + (w - (N + N))
    omega

def isAndOp : GateOp → Bool
  | .and => true
  | _ => false

def bnet (N : ℕ) (C : Circuit) (hAO2 : IsAO2 (N + N) C) :
    Net (Fin N ⊕ Fin N) (Fin C.gates.length) where
  isAnd i := isAndOp (gateAt C i.val).op
  left i := toOpd N C (opnd C i.val 0)
  right i := toOpd N C (opnd C i.val 1)
  rank i := i.val
  f := bf N C
  hl := by
    intro i j h
    have h1 := toOpd_wire h
    have h2 := (ao2_gate_props hAO2 i.isLt).2.2.1
    show j.val < i.val
    omega
  hr := by
    intro i j h
    have h1 := toOpd_wire h
    have h2 := (ao2_gate_props hAO2 i.isLt).2.2.2
    show j.val < i.val
    omega
  hf := by
    intro i z
    rw [toOpd_ev, toOpd_ev]
    rcases (ao2_gate_props hAO2 i.isLt).1 with hop | hop
    · simp only [hop, isAndOp, if_true]
      exact wireVal_and hAO2 (toIn z) i.isLt hop
    · simp only [hop, isAndOp, Bool.false_eq_true, if_false]
      exact wireVal_or hAO2 (toIn z) i.isLt hop

lemma toIn_line (N : ℕ) (l : Fin N) :
    toIn (lift0 (Y := Fin N) (single l)) = lineInput N l := by
  funext i
  unfold toIn lineInput
  split_ifs with h
  · simp only [lift0, Sum.elim_inr]
    symm
    apply decide_eq_false
    omega
  · simp only [lift0, Sum.elim_inl, single]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro e
      have h3 : i.val - N = l.val := congrArg Fin.val e
      omega
    · intro e
      exact Fin.ext (by simp; omega)

lemma adjP_trans {X Y : Type} {s : ℕ} (M : Net (X ⊕ Y) (Fin s)) {r w v : Fin s} {x : X → Bool}
    (h1 : AdjP M r x w) (h2 : AdjP M w x v) : AdjP M r x v := by
  induction h2 with
  | root => exact h1
  | step t u _ ho hs ih => exact AdjP.step t u ih ho hs

lemma lp_captured {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N) :
    ∀ w : ℕ, (lpAt C N p l w).2 = true →
      w = p.val ∨ ∃ (j : ℕ) (hj : j < C.gates.length), w = N + N + j ∧
        ∃ t : Rd C.gates.length, opd (bnet N C hAO2) t = .var (.inr p) ∧
          Cp (bnet N C hAO2) ⟨j, hj⟩ (single l) t := by
  intro w
  induction' w using Nat.strong_induction_on with w ih
  intro hw
  by_cases h1 : w < N
  · rw [lpAt_snd_point C N p l w h1] at hw
    exact Or.inl (of_decide_eq_true hw)
  by_cases h2 : w < N + N
  · rw [lpAt_snd_line C N p l w (by omega) h2] at hw
    exact absurd hw (by decide)
  by_cases h3 : w < N + N + C.gates.length
  swap
  · rw [lpAt_ge C N p l w (by omega)] at hw
    exact absurd hw (by decide)
  right
  obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
  have hj : j < C.gates.length := by omega
  refine ⟨j, hj, rfl, ?_⟩
  obtain ⟨hop, _, hb0, hb1⟩ := ao2_gate_props hAO2 hj
  have stepdown : ∀ b : Bool,
      (lpAt C N p l (opnd C j (if b then 1 else 0))).2 = true →
      Side (bnet N C hAO2) (single l) (⟨j, hj⟩, b) →
      ∃ t : Rd C.gates.length, opd (bnet N C hAO2) t = .var (.inr p) ∧
          Cp (bnet N C hAO2) ⟨j, hj⟩ (single l) t := by
    intro b hb hside
    have hlt : opnd C j (if b then 1 else 0) < N + N + j := by
      cases b
      · exact hb0
      · exact hb1
    have hopd : opd (bnet N C hAO2) (⟨j, hj⟩, b) = toOpd N C (opnd C j (if b then 1 else 0)) := by
      cases b <;> rfl
    rcases ih _ hlt hb with he | ⟨j', hj', he, t', ho', hp', hs'⟩
    · refine ⟨(⟨j, hj⟩, b), ?_, AdjP.root, hside⟩
      rw [hopd, he]
      unfold toOpd
      rw [dif_pos p.isLt]
    · refine ⟨t', ho', ?_, hs'⟩
      have hstep : AdjP (bnet N C hAO2) ⟨j, hj⟩ (single l) ⟨j', hj'⟩ := by
        refine AdjP.step (⟨j, hj⟩, b) ⟨j', hj'⟩ AdjP.root ?_ hside
        rw [hopd, he]
        unfold toOpd
        have hn1 : ¬ (N + N + j' < N) := by omega
        have hn2 : ¬ (N + N + j' < N + N) := by omega
        have hn3 : N + N + j' - (N + N) < C.gates.length := by omega
        rw [dif_neg hn1, dif_neg hn2, dif_pos hn3]
        congr 1
        exact Fin.ext (by simp)
      exact adjP_trans _ hstep hp'
  have sideval : ∀ b : Bool,
      wireVal (N + N) C (opnd C j (if b then 0 else 1)) (lineInput N l) = true →
      Side (bnet N C hAO2) (single l) (⟨j, hj⟩, b) := by
    intro b hv
    right
    have hoth : oth (bnet N C hAO2) (⟨j, hj⟩, b) = toOpd N C (opnd C j (if b then 0 else 1)) := by
      cases b <;> rfl
    show (oth (bnet N C hAO2) (⟨j, hj⟩, b)).ev (bf N C) (lift0 (single l)) = true
    rw [hoth, toOpd_ev, toIn_line]
    exact hv
  rcases hop with hop | hop
  · rw [lpAt_snd_and hAO2 p l hj hop] at hw
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hw
    rcases hw with ⟨hv, hb⟩ | ⟨hb, hv⟩
    · exact stepdown true hb (sideval true hv)
    · exact stepdown false hb (sideval false hv)
  · have hor : Side (bnet N C hAO2) (single l) (⟨j, hj⟩, true) ∧
        Side (bnet N C hAO2) (single l) (⟨j, hj⟩, false) := by
      have : (bnet N C hAO2).isAnd ⟨j, hj⟩ = false := by
        show isAndOp (gateAt C j).op = false
        rw [hop]; rfl
      exact ⟨Or.inl this, Or.inl this⟩
    rw [lpAt_snd_or hAO2 p l hj hop] at hw
    simp only [Bool.or_eq_true] at hw
    rcases hw with hb | hb
    · exact stepdown false hb hor.2
    · exact stepdown true hb hor.1

def onePt {N : ℕ} (Z : Finset (Fin N)) (p : Fin N) : Fin (N + N) → Bool :=
  fun i => if h : i.val < N then decide (i.val = p.val)
    else decide ((⟨i.val - N, by omega⟩ : Fin N) ∈ Z)

lemma toIn_onePt {N : ℕ} (Z : Finset (Fin N)) (p : Fin N) :
    toIn (lift1 (Net.ind Z) p) = onePt Z p := by
  funext i
  unfold toIn onePt
  split_ifs with h
  · simp only [lift1, Sum.elim_inr]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact ⟨fun e => congrArg Fin.val e, fun e => Fin.ext e⟩
  · simp [lift1, Net.ind]

lemma onePt_natAdd {N : ℕ} (Z : Finset (Fin N)) (p l : Fin N) :
    onePt Z p (Fin.natAdd N l) = decide (l ∈ Z) := by
  have h : ¬ ((Fin.natAdd N l).val < N) := by simp
  unfold onePt
  rw [dif_neg h]
  have e : (⟨(Fin.natAdd N l).val - N, by have := l.isLt; simp⟩ : Fin N) = l := Fin.ext (by simp)
  rw [e]

lemma onePt_castAdd {N : ℕ} (Z : Finset (Fin N)) (p p' : Fin N) :
    onePt Z p (Fin.castAdd N p') = decide (p' = p) := by
  have h : (Fin.castAdd N p').val < N := p'.isLt
  unfold onePt
  rw [dif_pos h]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩

theorem graded_pointSingle (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (σ : ℕ)
    (hC4 : ∀ p p' : Fin N, p ≠ p' → ∀ l l' : Fin N, I p l → I p' l → I p l' → I p' l' → l = l')
    (hAO2 : IsAO2 (N + N) C)
    (hSound : ∀ (Z : Finset (Fin N)) (p : Fin N), Z.card < σ →
      circuitFun (N + N) C (onePt Z p) = true → ∃ l ∈ Z, I p l) :
    ∑ p : Fin N, min ((Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card) σ
      ≤ 10 * C.size + N := by
  classical
  by_cases hσ : σ = 0
  · subst hσ
    simp
  by_cases hout : ∃ (j : ℕ) (hj : j < C.gates.length), C.output = N + N + j
  · obtain ⟨j, hj, hjo⟩ := hout
    let M := bnet N C hAO2
    have hs : ∀ (Z : Finset (Fin N)) (c : Fin N), Z.card < σ →
        M.f ⟨j, hj⟩ (lift1 (Net.ind Z) c) = true → ∃ a ∈ Z, I c a := by
      intro Z c hZ ht
      apply hSound Z c hZ
      have : wireVal (N + N) C (N + N + j) (toIn (lift1 (Net.ind Z) c)) = true := ht
      rw [toIn_onePt] at this
      show (C.wires (List.ofFn (onePt Z c))).getD C.output false = true
      rw [hjo]
      exact this
    have key := captured_min_le M (fun i => rfl) ⟨j, hj⟩ (fun (a c : Fin N) => I c a) σ
      (fun c c' hne a b h1 h2 h3 h4 => hC4 c c' hne a b h1 h2 h3 h4) hs
    have hcard : Fintype.card (Fin N) = N := Fintype.card_fin N
    rw [hcard] at key
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) key
    apply min_le_min _ le_rfl
    apply Finset.card_le_card
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    refine ⟨?_, hl.1⟩
    have hls := hl.2
    rw [lineSingle_eq_lpAt, hjo] at hls
    rcases lp_captured hAO2 p l _ hls with he | ⟨j', hj', he, t, ho, hc⟩
    · have := p.isLt
      omega
    · have hjj : j' = j := by omega
      subst hjj
      exact ⟨t, ho, hc⟩
  · have hzero : ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true) = ∅ := by
      intro p
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      have hls := hl.2
      rw [lineSingle_eq_lpAt] at hls
      rcases lp_captured hAO2 p l _ hls with he | ⟨j', hj', he, _⟩
      · have htrue : circuitFun (N + N) C (onePt (∅ : Finset (Fin N)) p) = true := by
          show (C.wires (List.ofFn (onePt (∅ : Finset (Fin N)) p))).getD C.output false = true
          rw [he]
          have hlt : p.val < N + N := by have := p.isLt; omega
          have := wireVal_input (N + N) C (onePt (∅ : Finset (Fin N)) p) p.val hlt
          unfold wireVal at this
          rw [this]
          simp [onePt]
        obtain ⟨a, ha, _⟩ := hSound ∅ p (by simpa using Nat.pos_of_ne_zero hσ) htrue
        simp at ha
      · exact hout ⟨j', hj', he⟩
    simp [hzero]

lemma scan_snoc {α : Type} (step : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    scan step (gs ++ [g]) w = scan step gs w ++ [step (scan step gs w) g] := by
  rw [scan_append]
  rfl

lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (scan boolStep gs x).getD i false = (scan boolStep gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (scan boolStep gs x).length = j := by simp [scan_length, hx, j]
    have ey : (scan boolStep gs y).length = j := by simp [scan_length, hy, j]
    rw [scan_snoc, scan_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      unfold boolStep
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  show (scan boolStep C.gates (List.ofFn x)).getD C.output false =
    (scan boolStep C.gates (List.ofFn y)).getD C.output false
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

def pair {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

def point {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p)

def line {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.natAdd N l)

lemma size_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : N = q ^ 2 + q + 1) (hq2 : 2 ≤ q)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : IsAO2 (N + N) C)
    (hpair : ∀ p l : Fin N, I p l → circuitFun (N + N) C (pair p l) = true)
    (hpoint : ∀ p : Fin N, circuitFun (N + N) C (point p) = false)
    (hline : ∀ l : Fin N, circuitFun (N + N) C (line l) = false) : N + N ≤ C.size + 1 := by
  have htwo : 2 ≤ N := by nlinarith
  apply essential_bound C (fun g hg => (hAO.2.2 g hg).le)
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    have hex : ∃ p' : Fin N, p ≠ p' := by
      by_cases hz : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have hh := congrArg Fin.val h; simp at hh; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => hz (congrArg Fin.val h)⟩
    obtain ⟨p', hn⟩ := hex
    obtain ⟨l, hi, _⟩ := hp p p' hn
    refine ⟨pair p l, line l, fun j hj => ?_, by rw [hpair p l hi.1, hline]; decide⟩
    simp [pair, line, hj]
  · intro l
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun p => I p l)).card by
      rw [hl]; omega)
    refine ⟨pair p l, point p, fun j hj => ?_,
      by rw [hpair p l (Finset.mem_filter.mp hp).2, hpoint]; decide⟩
    simp only [pair, point, hj, or_false]

lemma point_deg_le (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∀ l l' : Fin N, I p l → I p' l → I p l' → I p' l' → l = l')
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card ≤ q + 1 := by
  classical
  have hdisj : ∀ l ∈ Finset.univ.filter (fun l => I p l), ∀ l' ∈ Finset.univ.filter (fun l => I p l),
      l ≠ l' → Disjoint ((Finset.univ.filter (fun p' => I p' l)).erase p)
        ((Finset.univ.filter (fun p' => I p' l')).erase p) := by
    intro l hl1 l' hl2 hne
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hne (hu p a (Ne.symm ha.1) l l' (Finset.mem_filter.mp hl1).2 ha.2
      (Finset.mem_filter.mp hl2).2 ha'.2)
  have hcard : ((Finset.univ.filter (fun l => I p l)).biUnion
      fun l => (Finset.univ.filter (fun p' => I p' l)).erase p).card =
      (Finset.univ.filter (fun l => I p l)).card * q := by
    rw [Finset.card_biUnion hdisj]
    have hc : ∀ l ∈ Finset.univ.filter (fun l => I p l),
        ((Finset.univ.filter (fun p' => I p' l)).erase p).card = q := by
      intro l hl1
      have hpm : p ∈ Finset.univ.filter (fun p' => I p' l) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ p, (Finset.mem_filter.mp hl1).2⟩
      rw [Finset.card_erase_of_mem hpm, hl]
      simp
    rw [Finset.sum_congr rfl hc]
    simp
  have hsub : ((Finset.univ.filter (fun l => I p l)).biUnion
      fun l => (Finset.univ.filter (fun p' => I p' l)).erase p) ⊆ Finset.univ.erase p := by
    intro a ha
    obtain ⟨l, _, hal⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hal).1, Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  have hN' : N - 1 = q ^ 2 + q := by rw [hN]; rfl
  rw [hN'] at h1
  by_contra hcon
  push_neg at hcon
  have h2 := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hcon)
  nlinarith

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 100 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO2 : IsAO2 (N + N) C)
    (hT : ∀ p l : Fin N, I p l → circuitFun (N + N) C
      (fun i : Fin (N + N) => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true)
    (hF : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) :
    Fintype.card { pl : Fin N × Fin N // I pl.1 pl.2 ∧
      lineSingle C (N + N) (fun k => decide (k < N)) pl.1.val (N + pl.2.val) = true } ≤ 38 * C.size := by
  have hl' : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    intro l
    rw [← hl l, Fintype.card_subtype]
  have hu : ∀ p p' : Fin N, p ≠ p' → ∀ l l' : Fin N, I p l → I p' l → I p l' → I p' l' → l = l' := by
    intro p p' hne l l' h1 h2 h3 h4
    obtain ⟨m, _, hm⟩ := hp p p' hne
    rw [hm l ⟨h1, h2⟩, hm l' ⟨h3, h4⟩]
  have hSound : ∀ (Z : Finset (Fin N)) (p : Fin N), Z.card < q + 1 →
      circuitFun (N + N) C (onePt Z p) = true → ∃ l ∈ Z, I p l := by
    intro Z p hZ ht
    by_contra hno
    have hc : Fintype.card { l : Fin N // onePt Z p (Fin.natAdd N l) = true } ≤ Z.card := by
      rw [Fintype.card_subtype]
      apply Finset.card_le_card
      intro l hl
      have h := (Finset.mem_filter.mp hl).2
      rw [onePt_natAdd] at h
      exact of_decide_eq_true h
    have hf := hF (onePt Z p) (by omega) (by
      rintro ⟨p', l, hI, h1, h2⟩
      rw [onePt_castAdd] at h1
      rw [onePt_natAdd] at h2
      have e : p' = p := of_decide_eq_true h1
      subst e
      exact hno ⟨l, of_decide_eq_true h2, hI⟩)
    rw [hf] at ht
    exact Bool.false_ne_true ht
  have key := graded_pointSingle N I C (q + 1) hu hAO2 hSound
  have hpoint : ∀ p : Fin N, circuitFun (N + N) C (point p) = false := by
    intro p
    apply hF
    · have h0 : Fintype.card { l : Fin N // point p (Fin.natAdd N l) = true } = 0 := by
        rw [Fintype.card_eq_zero_iff]
        exact ⟨fun x => cast_ne_nat p x.1 (of_decide_eq_true x.2).symm⟩
      omega
    · rintro ⟨_, l, _, _, h⟩
      exact cast_ne_nat p l (of_decide_eq_true h).symm
  have hline : ∀ l : Fin N, circuitFun (N + N) C (line l) = false := by
    intro l
    apply hF
    · rw [Fintype.card_subtype]
      have hsub : (Finset.univ.filter fun l' : Fin N => line l (Fin.natAdd N l') = true) ⊆ {l} := by
        intro l' h'
        have h2 := of_decide_eq_true (Finset.mem_filter.mp h').2
        have h3 : N + l'.val = N + l.val := congrArg Fin.val h2
        exact Finset.mem_singleton.mpr (Fin.ext (by omega))
      have h4 := Finset.card_le_card hsub
      rw [Finset.card_singleton] at h4
      omega
    · rintro ⟨p, _, _, h, _⟩
      exact cast_ne_nat p l (of_decide_eq_true h)
  have hsize := size_bound q N I C hN (by omega) hl' hp hAO2 (fun p l h => hT p l h) hpoint hline
  have hcount : Fintype.card { pl : Fin N × Fin N // I pl.1 pl.2 ∧
      lineSingle C (N + N) (fun k => decide (k < N)) pl.1.val (N + pl.2.val) = true } =
      ∑ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.card_filter]
  have hmin : ∀ p : Fin N, min ((Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card) (q + 1) =
      (Finset.univ.filter fun l : Fin N => I p l ∧
        lineSingle C (N + N) (fun k => decide (k < N)) p.val (N + l.val) = true).card := by
    intro p
    apply min_eq_left
    refine le_trans (Finset.card_le_card ?_) (point_deg_le q N I (by omega) hN hl' hu p)
    intro l hl1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl1).2.1⟩
  rw [Finset.sum_congr rfl (fun p _ => hmin p)] at key
  rw [hcount]
  have htwo : 2 ≤ N := by nlinarith
  omega

end PEqualNP.Outside.L_meta_7021

theorem PEqualNP.Outside.L_meta_7021 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x14 < x2)) (↑x13.1) (x2 + ↑x13.2) = Bool.true } ≤ (38 : ℕ) * x5.size := by
  intro x1 x2 x3 _ x5 h1 h2 h3 h4 h5 h6 h7
  exact PEqualNP.Outside.L_meta_7021.main x1 x2 x3 x5 h1 h2 h3 h4 h5 h6 h7
