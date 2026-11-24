import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Image
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Intervals
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1674

def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]

inductive Sol (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol m T q (insert (a ^^^ m) S) → Sol m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S →
      Sol m T q (insert (op d a b) S) → Sol m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) (ih (by omega) (Set.insert_subset_insert hs))

inductive Live (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live m T k t (insert (a ^^^ m) U) →
      Live m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Live m T k t (insert (op d a b) U) →
      Live m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : Sol m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left

def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S') :
    Live m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S') :
    Live m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl⟩ := h; exact .bi hab hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') : Bi d b a S S' := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm]⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]

def Min (m T k t : ℕ) (S : Finset ℕ) : Prop := Live m T k t S ∧ ∀ q < k, ¬ Sol m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol m T q (C m S')) :
    Sol m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hs : Sol m T q (C m S')) :
    Sol m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : Min m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : Min m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'

lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hl ih =>
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega

def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h

lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi d a b S S1 ∧ Live m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi d (a ^^^ m) c S1 S2 ∧ Live m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol n (T &&& n) q (C n (Im n S'))) : Sol n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hl ih =>
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩

def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hl : Live m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min m T k t (insert (op d a b) U) := by
  have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live m T k 0 S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live m T k t S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live m T k t S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect

structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
def NN : Nat := 1118
def AA : Nat := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7fff0000000000000000
def HX : Nat := 0x2954955552924a49554a5494800092552500015494a9200029294a94925524a524a52800094a52a94800094a94929254a49252a8000a4955292500014a00024a0002900012800080000000000000000000
def HY : Nat := 0x2000082080001080001042000041041100002000082084108000104210900004100002084108210000210904000084000082082210904110444400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f (Nat.succ m)) n
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def tail (f : Nat → List W → Bool) (d : Bool) (l e n z : Nat) (r : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (f z r) (Bool.rec (motive := fun _ => Bool) (f z r) false (rect d l (Nat.xor l (twice d l r)) r [])) (Nat.beq n e)
def child (f : Nat → List W → Bool) (d : Bool) (l g e n : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (tail f d l e n z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x => (st (y) (fun y => (st (Nat.lor x y) (fun w => ins ⟨s, x, y, w⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : Nat → ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ n) (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c n (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f d l g e) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def notsCore (f : Nat → Nat → List W → Bool) (d : Bool) (l m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) d l g e (Nat.succ n) (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) d l g e n (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def nots (f : Nat → Nat → List W → Bool) (d : Bool) (l m g e n z q : Nat) (v r : List W) : Bool :=
  notsCore (fun s z w => Bool.rec (motive := fun _ => Bool) false (f s z w) (Nat.beq (cov d l w) l)) d l m g e n z q v r
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f d l m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => (fun n => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (ih (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub k 2) s) v.length z v (pairsQ q q')) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z (Nat.succ q) v v)) (true) (node (ih (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z v (pairsP q)))) (pos s) l m g (Nat.sub k s) n z 0 v v)) (true) (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub k t) n z v pairs))) (true) (Nat.ble n 1))) v.length) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
def segsX : List (ℕ × ℕ) := [(63,79), (79,95), (95,97), (97,100), (100,116), (116,119), (119,121), (121,137), (137,139), (139,142), (142,145), (145,161), (161,163), (163,166), (166,168), (168,184), (184,186), (186,189), (189,192), (192,195), (195,197), (197,200), (200,202), (202,204), (204,206), (206,208), (208,211), (211,214), (214,217), (217,219), (219,235), (235,237), (237,239), (239,241), (241,244), (244,246), (246,249), (249,252), (252,255), (255,258), (258,261), (261,263), (263,266), (266,268), (268,270), (270,273), (273,276), (276,279), (279,281), (281,284), (284,287), (287,290), (290,292), (292,295), (295,297), (297,299), (299,302), (302,304), (304,307), (307,323), (323,326), (326,328), (328,331), (331,333), (333,335), (335,337), (337,340), (340,342), (342,345), (345,347), (347,350), (350,352), (352,355), (355,371), (371,373), (373,376), (376,378), (378,381), (381,383), (383,386), (386,389), (389,392), (392,394), (394,397), (397,399), (399,402), (402,405), (405,408), (408,410), (410,412), (412,414), (414,417), (417,420), (420,423), (423,426), (426,428), (428,431), (431,433), (433,435), (435,438), (438,440), (440,443), (443,445), (445,448), (448,451), (451,453), (453,469), (469,472), (472,475), (475,477), (477,479), (479,482), (482,484), (484,487), (487,490), (490,492), (492,494), (494,496), (496,512), (512,514), (514,517), (517,520), (520,522), (522,524), (524,526), (526,529), (529,532), (532,535), (535,551), (551,554), (554,556), (556,559), (559,562), (562,564), (564,566), (566,569), (569,571), (571,574), (574,576), (576,578), (578,580), (580,582), (582,584), (584,587), (587,590), (590,593), (593,595), (595,598), (598,601), (601,604), (604,607), (607,609), (609,612), (612,614), (614,616), (616,618), (618,620), (620,622), (622,624), (624,626), (626,628), (628,631), (631,634), (634,636), (636,638), (638,640), (640,643), (643,645)]
def segsY : List (ℕ × ℕ) := [(645,658), (658,662), (662,666), (666,670), (670,676), (676,680), (680,686), (686,692), (692,695), (695,700), (700,705), (705,709), (709,715), (715,721), (721,727), (727,746), (746,751), (751,770), (770,776), (776,779), (779,784), (784,789), (789,808), (808,813), (813,819), (819,824), (824,830), (830,835), (835,841), (841,860), (860,866), (866,884), (884,887), (887,892), (892,897), (897,902), (902,908), (908,927), (927,932), (932,938), (938,943), (943,949), (949,955), (955,973), (973,992), (992,996), (996,1002), (1002,1008), (1008,1014), (1014,1033), (1033,1038), (1038,1044), (1044,1063), (1063,1068), (1068,1087), (1087,1093), (1093,1099), (1099,1117)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma tail_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    (hr : StOk P T l k z r S) (hm : Min m T k' t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = r.length)
    (he : e = k + 1 - t) (h : tail f d l e n z r = false) : f z r = false := by
  simp only [tail, bR] at h
  by_cases hne : n = e
  · have hb : Nat.beq n e = true := by simpa using hne
    rw [hb, cond_true] at h
    cases hrect : rect d l (Nat.xor l (twice d l r)) r [] with
    | false => rw [hrect] at h; simpa using h
    | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := Nat.xor l (twice d l r))] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp d l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : d = false := by rw [hd]; simp [pos']
          subst hd'
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : d = true := by rw [hd]; simp [pos', htp]
          subst hd'
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
  · have hb : Nat.beq n e = false := Bool.eq_false_iff.2 fun h => hne (Nat.eq_of_beq_eq_true h)
    rw [hb, cond_false] at h; exact h
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min m T k' t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = r.length)
    (he : e = k + 1 - t) (h : child f d l g e n mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact tail_sound X hr hm hk hd hn he h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b)⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b)⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi d' a.s c.s S S')
    (hl : Live m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi d' a.s c.s S S') (hl : Live m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f d l m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
lemma mid_false {f : ℕ → List W → Bool} {d : Bool} {l m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f d l m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f d l g e) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ℕ → ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch n (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (n + 1) (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (n + 1) (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch (n + 2) mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch n (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ n) (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (Nat.succ n) (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y) = false
    cases ch (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y) <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Bi d' a.s c.s S S') (hl : Live m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f d l m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hsz := hmin.size
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ S'.card ≤ e ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, by omega, this⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {n z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → n = r.length →
      child f (pos' t) l g e n mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' :=
    fun {n z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk rfl h3 he h4, h2⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 (by omega) ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma notsCore_false {f : ℕ → ℕ → List W → Bool} {d : Bool} {l m g e n z q : ℕ} {v r : List W} (h : notsCore f d l m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (notsCore f d l m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) d l g e (Nat.succ n) (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) d l g e n (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) then true
          else notsCore f d l m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases notsCore f d l m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma notsCore_sound {f : ℕ → ℕ → List W → Bool} {d : Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Un m a.s S S') (hl : Live m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : notsCore f d l m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hsz := hmin.size
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := notsCore_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) (pos' t) l g e (v.length + 1) (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) (pos' t) l g e (v.length + 1) (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk rfl (by omega) he h, hst⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) (pos' t) l g e v.length (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) (pos' t) l g e v.length (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk rfl (by omega) he h, hst⟩
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {d : Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Un m a.s S S') (hl : Live m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f d l m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' := by
  obtain ⟨z', r, h, hr⟩ := notsCore_sound X hs hm hk hd hn he hb hl ha hq har' hp
  have hcov : Nat.beq (cov d l r) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hsep⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hd, hsep]; rfl⟩
  refine ⟨z', r, ?_, hr⟩
  change Bool.rec (motive := fun _ => Bool) false _ (Nat.beq (cov d l r) l) = false at h
  rwa [hcov] at h
end sound
def FM (m T k t : ℕ) (S : Finset ℕ) (KP : ℕ → ℕ → Prop) (KN : ℕ → Prop) : Prop :=
  (∃ k0 d a b S1, k = k0 + 1 ∧ KP a b ∧ Bi d a b S S1 ∧ Live m T k0 t S1) ∨
  (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ KN a ∧ Un m a S S1 ∧ Bi d (a ^^^ m) c S1 S2 ∧ Live m T k0 t0 S2) ∨
  (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ KN a ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
    Bi d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live m T k0 t0 S3)
lemma FM_of {m T k t : ℕ} {S : Finset ℕ} (h : Min m T k t S) (hc : 2 ≤ S.card) : FM m T k t S (fun _ _ => True) (fun _ => True) := by
  rcases first_move k t S h hc with ⟨k0, d, a, b, S1, e, h⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', h⟩ | ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h⟩
  · exact Or.inl ⟨k0, d, a, b, S1, e, trivial, h⟩
  · exact Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', trivial, h⟩)
  · exact Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', trivial, h⟩)
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma look_succ (l m g fuel k t z : ℕ) (v : List W) (h : look l m g (fuel + 1) k t z v = false) :
    2 ≤ v.length ∧ node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v pairs = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos s) l m g (k - 2 - s)
        v.length z v (pairsQ q q')) (pos s) l m g (k - 1 - s) v.length z (q + 1) v v)) true
        (node (look l m g fuel (k - 2) s) (pos s) l m g (k - 1 - s) v.length z v (pairsP q)))) (pos s) l m g (k - s) v.length z 0 v v)) true
      (node (look l m g fuel (k - 1) t) (pos t) l m g (k - t) v.length z v pairs)) true (Nat.ble v.length 1) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h0 : Nat.ble v.length 1 with
  | true => rw [h0] at h; simp at h
  | false =>
    rw [h0, Bool.cond_false] at h
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    cases h1 : node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v pairs with
    | true => rw [h1] at h; simp at h
    | false =>
      rw [h1, Bool.cond_false] at h
      refine ⟨hlen, rfl, ?_⟩
      rintro s rfl
      exact h
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_1674.X → L_meta_1674.X → Bool) → List L_meta_1674.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Bi d' x y S S') (hl : Live m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · exact gate_sound X hs hm hk hd hn he hb hl ha hc h
  · exact gate_sound X hs hm hk hd hn he hb.symm hl hc ha h
lemma step_sound {fuel : ℕ} (ih : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S →
    ∀ k' ≤ k, ¬ Min m T k' t S) {k t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hlen : 2 ≤ v.length)
    {KP : ℕ → ℕ → Prop} {KN : ℕ → Prop}
    (hA : ∀ x y : ℕ, x ≠ y → KP x y → ∃ go : (L_meta_1674.X → L_meta_1674.X → Bool) → List L_meta_1674.X → Bool,
      node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false)
    (hN : ∀ s, t = s + 1 → ∀ a ∈ v, KN a.s → ∃ rr, a ∈ rr ∧ nots (fun q z v =>
      bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v rr = false) :
    ∀ k' ≤ k, Min m T k' t S → ¬ FM m T k' t S KP KN := by
  intro k' hk hm hfm
  rcases hfm with
    ⟨k0, d, a, b, S1, rfl, hkp, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hkn, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hkn, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨go, h1, hgo⟩ := hA a b hb.1 hkp
    obtain ⟨z', r, hf, hst⟩ := node_bi X hs hm (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact hgo h hp a c ha hc hax hcy) h1
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    obtain ⟨rr, hrr, h2⟩ := hN t0 rfl wa hwa hkn
    obtain ⟨z1, r1, hf1, hst1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl rfl (by omega) hu hl1 hwa (by omega) hrr h2
    have hm1 := hu.min hl1 hm.2
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    obtain ⟨rr, hrr, h2⟩ := hN (t0 + 1) rfl wa hwa hkn
    obtain ⟨z1, r1, hf1, hst1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl rfl (by omega) hu hl2 hwa (by omega) hrr h2
    have hm1 := hu.min hl2 hm.2
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl rfl (by omega) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    obtain ⟨z', r, hf, hst⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S →
    ∀ k' ≤ k, ¬ Min m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs
    obtain ⟨hlen, h1, h2⟩ := look_succ _ _ _ _ _ _ _ _ h
    intro k' hk hm
    refine step_sound X (KP := fun _ _ => True) (KN := fun _ => True) ih hs hlen (fun x y hxy _ => ⟨pairs, h1, fun h hp a c ha hc hax hcy => ?_⟩)
      (fun s hs a ha _ => ⟨v, ha, h2 s hs⟩) k' hk hm (FM_of hm (by rw [hs.rep.card]; exact hlen))
    have hpw := pairs_false hp
    have : Std.Symm (fun a c : L_meta_1674.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
    refine (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_
    intro e
    have : a.s = c.s := congrArg L_meta_1674.X.s e
    exact hxy (by rw [← hax, ← hcy, this])
end sound
def rawP : List ℕ := [0x1ffff8000000007fffe000f8000007fffc07c000000003e003c00000000000000001f03ffff03c00000000000000000000000f83e00e000020c00800086060800008c0ca44000080948800085032910410204200288610001004a8402001108ca8408000010822020b0844a880000000821511012a20042a221951014a880a888000000000000000010290417e052000852085ad14800be0008a51e2901f002100252f802f0005482002a4108217c089ea40f00800690800690410442120be0f80b80a40830020016181860000230300000002020000006b40c00010c0810801a218400040100000802c4630000601080c6188186c2110000000a8161afffe04000035fffc60000d00007fff79108a00c1600211, 0x7fffc07c00000000003e00000003e0000000000000000f81ffff80078000000000000000000000000000000ffffc0ffffc001f003c3e00000e000040202208843010100010002102183080620460842018408c0a000000100100230c0310431810841210431000808010000400101043860888410a08c0c41182141184208c21046904700000000000000001f04301f02086001086f80012182f8200110c02430410be046e86081e1000a1840050c210420420030c2121127c30127c30027c04f0f82008b8810d0080882210c04060004000800000c20180000230806000016c000000c02c058c300c000060421068000060460610c0043002d57fff1862210c2000030000184000100000d7fff7fff0000000c1b00f00f, 0x1ffff8007fffef80000000000000000000000000000003fffe0000007c0f80003ffff7803e0000000000007c0078000003ee00000000000001000024208c00d806141800b00c282098140185050401000800024080008061400020000461482140405808160120506281012010260c502018a04c18a008c510462906280000000000000000020860820410c16b90c101ad433e100002218048608210420050c1044228bc30002819f03e00848be19e00f8088600088609f081e201042fb90021800000002c0005b08230036000006002c0000083605000001610040060281b020002000000058150b7fff08503016020580d814000040682c0d80000800001b000016fffe17fff0000b6204500c2900122, 0x7fffdf000001ffffbef0000000003ffff000001f78000000000000000ffffdf00000003efb8000000002800000001240002000a000068800a0000d2000000901a60002c02400ab00000d6000c90a40055800c9004009b000240024b000d102400a58001a405034a000348501a6300d200d200000000000000000421410408428202428208060a042042140513e147c000844ee28fbc000110a0899e50400847de104504002041141165d47c4000844fbee110008500a00002800db0000800280000000028000000a80056dfffc000b00b002ac0000358000006b00156000000b0036c002b000dac000005b002d6000000b5fffc0000016fffec0000000004e9569449441700, 0x7fffdf00000001ffffbef00000000003ffff000000000fbc00000000003fffef80000000fbc00000000003effffde00000000007bd8000000000005800280ab500000280d600014911b600029242ad2800524800580009b400000b600015121096a00015120295a00000894d00001522149aa00002a4828549469549402a4801524152400000000000000001f0187c01003006b830fbc080c0000808f860081810403ef0083020804089cc3e01060003ef10800860020f925d8780118100001ef62084200100616000a02ad600000a035800000006d80000000ab6b0000000016000b6d800002d800000006b5ac00000000b56800002b5b6000000005b6a800000000b5fffdb5fffc00000000000000284504a1207d5054, 0x3fffefbffff7de00000000000003effffdeffffdf7df70000000000000000000000000000002aa000000019892a1200370000000006c00485080000000092429001b80000000001b02d5ada53400000000003316daab534806e0000d80000d80006c00036003600000000000000000852020820a4040c2404103090084104284805120208210813040410884add03eade81f780020025080040f9b5e079b5e07df7dc0000100400214800000aa800000000aa80000000006daadafffe00000000000016b56000000002db5ad7fff0000000000000b56b6d6d80000000000005b6aad6dafffe0000000000000000000000000008d6a96892882b00, 0x3ffff7fffdf7de00000000000003fffefbffff7defbdf7bffff7bd8000000000000000000000000000000000a84800000000002aa42a4840de00000001b800000000370005ad5ada6aa6d400000019c00000000019c02d52d35a6ad69b6a541bc00000000003700006e00006e000370001b801b800000000000000001084041041080830080820c020108208cf9019e407df7a0024080001000c9e03ec9f01f7bef7dec9f01ef60206000206000001000804000002021016ab600000000000aab5ab6b7fff000000000000000000000016b56b6daadb580000000000000000000000b56b6d6dab5b6dad57fff000000000000000000000000000000000000000c03030c01c03cc30, 0x7fffdf7dffffbc000000000000000003ffff7fffdf7defbdffffbef7bd8000000000000000000000000000000000000000000000000000000000005aadaaaaa5b6d498000000018e000000031c0000000063800012852d36ab4962494259e01ad4b55a99e018000000000000000019c0000000000338000670000670003380019c019c000000000000000001f1807df7e300f4030000100c02000008fe011f807df7bef47f00fbdef60e00100e000821000000e0008004038002038002082090000000820006016ab6aaaad6db5b6000000000000000000000000000000000016b56b6daadb5adb5ad7fff6b5ad56b7fff6000000000000000000000000000000000000000000000000000000000000148a085220bea0a8, 0x7fffdf7dffffbdffffbef7fffefbefb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000050292aaab5a496d800940929f001240a4be002adad527c005b0000000000000000001e00000000001e000000000000000000001e000000000003c0000780000780003c0001e001e0000000000000000001fe007df7fc00f7fc00fbdff003efbeef0001e000410400078000820000f00020f000104208410f000108483c00043c0004104100008208000038016ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00ff30f00030003]
def rawL : List ℕ := rawP ++ [rawP.getD 0 0 ||| rawP.getD 2 0]
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7ffffcffffccdbfff333
def kz (Z : ℕ) : ℕ := (List.range 9).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawL.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawL) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)))⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c⟩ :: r)) v
def anySub (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (ih h) true (ih fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def filt (H : ℕ) (v : List W) : List W := List.rec (motive := fun _ => List W) [] (fun w _ ih => Bool.rec (motive := fun _ => List W) ih (w :: ih) (hb H w.s)) v
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g fuel H HN k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (look l m g fuel (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub k 2) s)
        v.length z v (pairsQ q q')) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z (Nat.succ q) v v)) true
        (node (look l m g fuel (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z v (pairsP q)))) (pos s) l m g (Nat.sub k s) v.length z 0 v (filt HN v))) true
      (node (look l m g fuel (Nat.sub k 1) t) (pos t) l m g (Nat.sub k t) v.length z v (pairsC H))) true (Nat.ble v.length 1)

def sameWire (a b : W) : Bool := a.s == b.s && a.a == b.a && a.b == b.b && a.c == b.c
lemma sameWire_eq {a b : W} (h : sameWire a b = true) : a = b := by
  cases a; cases b; simp_all [sameWire]
def sameBank : List W → List W → Bool
  | [], [] => true
  | a :: as', b :: bs => sameWire a b && sameBank as' bs
  | _, _ => false
lemma sameBank_eq {a b : List W} (h : sameBank a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [sameBank]
  | cons a as' ih =>
    cases b with
    | nil => simp [sameBank] at h
    | cons b bs =>
      simp only [sameBank, Bool.and_eq_true] at h
      obtain ⟨hab, htail⟩ := h
      rw [sameWire_eq hab, ih htail]
abbrev Saved := ℕ × ℕ × ℕ × List W
def sameSaved (k t z : ℕ) (v : List W) (s : Saved) : Bool :=
  k == s.1 && t == s.2.1 && z == s.2.2.1 && sameBank v s.2.2.2
lemma sameSaved_eq {k t z : ℕ} {v : List W} {s : Saved} (h : sameSaved k t z v s = true) :
    (k, t, z, v) = s := by
  obtain ⟨j,u,b,w⟩ := s
  simp only [sameSaved, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,h⟩ := h
  rw [sameBank_eq h]
def gl : ℕ := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7fff0000000000000000
def gm : ℕ := 0x7fffdf7dffffbdffffbef7fffefbefbbffff7fffdf7defbdffffbef7bdbfffefbffff7defbdf7bffff7bdbeffffdeffffdf7df77bdbefbbeeeefff5aadaaaab5b6d6daaad6adadfffdb6ab6bfffaadad5b7fff5b5ad5adb6ab6d6b6d6b5fffdad6b55adfffdad5adb5b6ad6db6b55fffd6daab5b6bfffad7fff6d7fff5bfffb5fffdfffc0000000000000001ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7fffffffffffffffffff
def gg : ℕ := 0x108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
def oneStep (l m g : ℕ) (ih : ℕ → ℕ → ℕ → List W → Bool) (k t z : ℕ) (v : List W) : Bool :=
  (fun n => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (ih (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub k 2) s) v.length z v (pairsQ q q')) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z (Nat.succ q) v v)) (true) (node (ih (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z v (pairsP q)))) (pos s) l m g (Nat.sub k s) n z 0 v v)) (true) (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub k t) n z v pairs))) (true) (Nat.ble n 1))) v.length
def u11 : W := ⟨0x3fffefbffff7de00000000000003effffdeffffdf7df70000000000000000000000000000002aa000000019892a1200370000000006c00485080000000092429001b80000000001b02d5ada53400000000003316daab534806e0000d80000d80006c00036003600000000000000000852020820a4040c2404103090084104284805120208210813040410884add03eade81f780020025080040f9b5e079b5e07df7dc0000100400214800000aa800000000aa80000000006daadafffe00000000000016b56000000002db5ad7fff0000000000000b56b6d6d80000000000005b6aad6dafffe0000000000000000000000000008d6a96892882b00, 0x800000000000010840000020000000800008400000000040000000000210000000000004200042108421000010040000000084000002100021000210000000420000010000108400000000000008000, 0x0, 0x800000000000010840000020000000800008400000000040000000000210000000000004200042108421000010040000000084000002100021000210000000420000010000108400000000000008000⟩
def u18 : W := ⟨0x7fffdf000001ffffbef0000000003ffff000001f78000000000000000ffffdf00000003efb8000000002800000001240002000a000068800a0000d2000000901a60002c02400ab00000d6000c90a40055800c9004009b000240024b000d102400a58001a405034a000348501a6300d200d200000000000000000421410408428202428208060a042042140513e147c000844ee28fbc000110a0899e50400847de104504002041141165d47c4000844fbee110008500a00002800db0000800280000000028000000a80056dfffc000b00b002ac0000358000006b00156000000b0036c002b000dac000005b002d6000000b5fffc0000016fffec0000000004e9569449441700, 0x40000000000010002100000084000040000000080000000000020000000002100001084010000108400084200002000000080010802000000004200802000000080200000000020004010000000420, 0x0, 0x40000000000010002100000084000040000000080000000000020000000002100001084010000108400084200002000000080010802000000004200802000000080200000000020004010000000420⟩
def u21 : W := ⟨0x3ffff7fffdf7de00000000000003fffefbffff7defbdf7bffff7bd8000000000000000000000000000000000a84800000000002aa42a4840de00000001b800000000370005ad5ada6aa6d400000019c00000000019c02d52d35a6ad69b6a541bc00000000003700006e00006e000370001b801b800000000000000001084041041080830080820c020108208cf9019e407df7a0024080001000c9e03ec9f01f7bef7dec9f01ef60206000206000001000804000002021016ab600000000000aab5ab6b7fff000000000000000000000016b56b6daadb580000000000000000000000b56b6d6dab5b6dad57fff000000000000000000000000000000000000000c03030c01c03cc30, 0x20000000000000000000000842100000000010800008400000000000000000004210800000000000000042000021000000840000021084000000008021084010842000000000010842100000, 0x0, 0x20000000000000000000000842100000000010800008400000000000000000004210800000000000000042000021000000840000021084000000008021084010842000000000010842100000⟩
def u26 : W := ⟨0x1ffff8007fffef80000000000000000000000000000003fffe0000007c0f80003ffff7803e0000000000007c0078000003ee00000000000001000024208c00d806141800b00c282098140185050401000800024080008061400020000461482140405808160120506281012010260c502018a04c18a008c510462906280000000000000000020860820410c16b90c101ad433e100002218048608210420050c1044228bc30002819f03e00848be19e00f8088600088609f081e201042fb90021800000002c0005b08230036000006002c0000083605000001610040060281b020002000000058150b7fff08503016020580d814000040682c0d80000800001b000016fffe17fff0000b6204500c2900122, 0x2000000080000800008000000000002000020084000000100000000200800008400000200840100021080000002100420000010000000400080000042100000000000040008001004200002000400, 0x0, 0x2000000080000800008000000000002000020084000000100000000200800008400000200840100021080000002100420000010000000400080000042100000000000040008001004200002000400⟩
def u33 : W := ⟨0x1ffff8000000007fffe000f8000007fffc07c000000003e003c00000000000000001f03ffff03c00000000000000000000000f83e00e000020c00800086060800008c0ca44000080948800085032910410204200288610001004a8402001108ca8408000010822020b0844a880000000821511012a20042a221951014a880a888000000000000000010290417e052000852085ad14800be0008a51e2901f002100252f802f0005482002a4108217c089ea40f00800690800690410442120be0f80b80a40830020016181860000230300000002020000006b40c00010c0810801a218400040100000802c4630000601080c6188186c2110000000a8161afffe04000035fffc60000d00007fff79108a00c1600211, 0x8000000200000108000000010000100400000200000000001004000000100420080010800000401084000840000001004200040000400000010040100000000000000000400080000040108021, 0x0, 0x8000000200000108000000010000100400000200000000001004000000100420080010800000401084000840000001004200040000400000010040100000000000000000400080000040108021⟩
def u48 : W := ⟨0x1ffff81ffff8007fffef80f8000007fffc07c000000003e003c3fffe0000007c0f81f03ffff7bc3e0000000000007c0078000f83ee0e000020c00801086064a08c08d8ce541800b09ca820985433950514214208288650801084e9402021108ce948a14041582a160b2854ea81012010a61d51213aa04c3aa219d5114ea90ea88000000000000000030af0c37e15e16b95e185ad57be1be002abd1eaf09f10630075ef846f28bd78202abdf0be17c48bebdef0f808ef0808ef0df0c5e321be2fb9b82bc08300202d6185b68230236300006002c20000836b50c00016d0850861aa1b42004210000085ad56b7fff6850b0d61a8586da150000406aad6dafffe840001b5fffd6fffed7fff7fffff30cf00c3f00333, 0x8000000000000000000000000000000000000000000000400000000800000001080000000000000000000000000400000000040100000000000000000000000000000000000, 0x0, 0x8000000000000000000000000000000000000000000000400000000800000001080000000000000000000000000400000000040100000000000000000000000000000000000⟩
def u54 : W := ⟨0x7fffc07c00000000003e00000003e0000000000000000f81ffff80078000000000000000000000000000000ffffc0ffffc001f003c3e00000e000040202208843010100010002102183080620460842018408c0a000000100100230c0310431810841210431000808010000400101043860888410a08c0c41182141184208c21046904700000000000000001f04301f02086001086f80012182f8200110c02430410be046e86081e1000a1840050c210420420030c2121127c30127c30027c04f0f82008b8810d0080882210c04060004000800000c20180000230806000016c000000c02c058c300c000060421068000060460610c0043002d57fff1862210c2000030000184000100000d7fff7fff0000000c1b00f00f, 0x100000004000042000000000200000000001004200000000400080010042008021000000002008020004000800100000000000000108001004010802100000004000002000000000200802100001, 0x0, 0x100000004000042000000000200000000001004200000000400080010042008021000000002008020004000800100000000000000108001004010802100000004000002000000000200802100001⟩
def u66 : W := ⟨0x7fffdf00000001ffffbef00000000003ffff000000000fbc00000000003fffef80000000fbc00000000003effffde00000000007bd8000000000005800280ab500000280d600014911b600029242ad2800524800580009b400000b600015121096a00015120295a00000894d00001522149aa00002a4828549469549402a4801524152400000000000000001f0187c01003006b830fbc080c0000808f860081810403ef0083020804089cc3e01060003ef10800860020f925d8780118100001ef62084200100616000a02ad600000a035800000006d80000000ab6b0000000016000b6d800002d800000006b5ac00000000b56800002b5b6000000005b6a800000000b5fffdb5fffc00000000000000284504a1207d5054, 0x1000000000000001000000000008021000000002008021000000840000000000000042000000000010000108000000200000008020080200840000001000200800100021080010840008421, 0x0, 0x1000000000000001000000000008021000000002008021000000840000000000000042000000000010000108000000200000008020080200840000001000200800100021080010840008421⟩
def u77 : W := ⟨0x7fffdf7dffffbc000000000000000003ffff7fffdf7defbdffffbef7bd8000000000000000000000000000000000000000000000000000000000005aadaaaaa5b6d498000000018e000000031c0000000063800012852d36ab4962494259e01ad4b55a99e018000000000000000019c0000000000338000670000670003380019c019c000000000000000001f1807df7e300f4030000100c02000008fe011f807df7bef47f00fbdef60e00100e000821000000e0008004038002038002082090000000820006016ab6aaaad6db5b6000000000000000000000000000000000016b56b6daadb5adb5ad7fff6b5ad56b7fff6000000000000000000000000000000000000000000000000000000000000148a085220bea0a8, 0x400000000000000400004210000000000000000842100000084000000000001080000000000000000200800008400000000842108400000000000008400000010842108421084200000000000, 0x0, 0x400000000000000400004210000000000000000842100000084000000000001080000000000000000200800008400000000842108400000000000008400000010842108421084200000000000⟩
def u97 : W := ⟨0x7fffdf7dffffbdffffbef7fffefbefb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000050292aaab5a496d800940929f001240a4be002adad527c005b0000000000000000001e00000000001e000000000000000000001e000000000003c0000780000780003c0001e001e0000000000000000001fe007df7fc00f7fc00fbdff003efbeef0001e000410400078000820000f00020f000104208410f000108483c00043c0004104100008208000038016ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00ff30f00030003, 0x10000000000084200000000421080000000000000000010000000000084210842108420000000000000000000210000008421084210000000000000000000008421084200000000000000000000000000, 0x0, 0x10000000000084200000000421080000000000000000010000000000084210842108420000000000000000000210000008421084210000000000000000000008421084200000000000000000000000000⟩
def u0 : W := opW false u18 u97
def u3 : W := opW false u11 u97
def u7 : W := opW false u11 u48
def u13 : W := opW false u18 u48
def u20 : W := opW true u11 u18
def u24 : W := opW false u26 u33
def u28 : W := opW true u11 u26
def u29 : W := opW true u18 u26
def u38 : W := opW true u18 u33
def u40 : W := opW false u48 u97
def u50 : W := opW true u11 u48
def u51 : W := opW true u18 u48
def u56 : W := opW true u11 u54
def u57 : W := opW true u18 u54
def u59 : W := opW true u26 u54
def u60 : W := opW true u33 u54
def u63 : W := opW true u48 u54
def u67 : W := opW true u11 u66
def u68 : W := opW true u18 u66
def u70 : W := opW true u26 u66
def u71 : W := opW true u48 u66
def u73 : W := opW true u54 u66
def u79 : W := opW true u18 u77
def u80 : W := opW true u11 u77
def u82 : W := opW true u33 u77
def u85 : W := opW true u54 u77
def u89 : W := opW true u48 u77
def u92 : W := opW true u66 u77
def u98 : W := opW true u26 u97
def u99 : W := opW true u11 u97
def u101 : W := opW true u54 u97
def u105 : W := opW true u33 u97
def u106 : W := opW true u48 u97
def u110 : W := opW true u18 u97
def u115 : W := opW true u66 u97
def u120 : W := opW true u77 u97
def u1 : W := opW false u18 u98
def u2 : W := opW false u38 u66
def u4 : W := opW false u20 u97
def u5 : W := opW false u11 u101
def u6 : W := opW false u18 u99
def u8 : W := opW false u11 u98
def u9 : W := opW false u11 u106
def u10 : W := opW false u11 u51
def u12 : W := opW false u18 u101
def u14 : W := opW false u48 u57
def u15 : W := opW false u18 u106
def u16 : W := opW false u20 u48
def u17 : W := opW false u20 u50
def u19 : W := opW false u20 u110
def u22 : W := opW true u3 u21
def u23 : W := opW true u13 u21
def u25 : W := opW false u51 u66
def u27 : W := opW false u28 u98
def u30 : W := opW true u28 u29
def u31 : W := opW false u48 u85
def u32 : W := opW false u48 u79
def u34 : W := opW false u38 u48
def u35 : W := opW false u48 u60
def u36 : W := opW false u48 u82
def u37 : W := opW true u3 u33
def u39 : W := opW true u20 u38
def u41 : W := opW false u48 u101
def u42 : W := opW false u51 u97
def u43 : W := opW false u48 u99
def u44 : W := opW false u48 u98
def u45 : W := opW false u50 u99
def u46 : W := opW false u48 u120
def u47 : W := opW false u48 u105
def u49 : W := opW false u50 u106
def u52 : W := opW true u50 u51
def u53 : W := opW false u57 u97
def u55 : W := opW false u56 u101
def u58 : W := opW true u56 u57
def u61 : W := opW true u57 u60
def u62 : W := opW false u63 u97
def u64 : W := opW true u56 u63
def u65 : W := opW true u57 u63
def u69 : W := opW true u67 u68
def u72 : W := opW true u67 u71
def u74 : W := opW true u68 u73
def u75 : W := opW true u71 u73
def u76 : W := opW false u79 u97
def u78 : W := opW false u79 u89
def u81 : W := opW true u79 u80
def u83 : W := opW true u79 u82
def u84 : W := opW false u85 u97
def u86 : W := opW true u79 u85
def u87 : W := opW true u80 u85
def u88 : W := opW true u82 u85
def u90 : W := opW true u79 u89
def u91 : W := opW true u85 u89
def u93 : W := opW true u79 u92
def u94 : W := opW true u80 u92
def u95 : W := opW true u85 u92
def u96 : W := opW true u89 u92
def u100 : W := opW true u98 u99
def u102 : W := opW true u98 u101
def u103 : W := opW true u99 u101
def u104 : W := opW false u106 u110
def u107 : W := opW true u99 u106
def u108 : W := opW true u101 u105
def u109 : W := opW true u101 u106
def u111 : W := opW true u99 u110
def u112 : W := opW true u101 u110
def u113 : W := opW true u105 u110
def u114 : W := opW true u106 u110
def u116 : W := opW true u98 u115
def u117 : W := opW true u99 u115
def u118 : W := opW true u101 u115
def u119 : W := opW true u106 u115
def u121 : W := opW true u101 u120
def u122 : W := opW true u105 u120
def u123 : W := opW true u110 u120
def u124 : W := opW true u106 u120
def zv0 : ℕ := 0x10846308c61194651946539ca528ce538ca739467294a5094251942319d293a4e539ce74ace95ad27394e73a5274a4e949ca5294a51a52519ce71a4a5194e5294a528c232a4e528c6739ca5394e528ca52
def zv1 : ℕ := 0x10846308c6119465194653a4a528ce538ca739467294a5094251942319d293a4e539d274ace95b527394e74ad274a4e949ca5294a51a52519d271a4a519525394a528c232a4e528c6739ca5394e528ca52
def zv2 : ℕ := 0x10846318461194a3194a729ca528ce728ca729427394e509425194630a4e94a5272a4e75a4e94ad2939ca93a5274a4a959ca5194631a4e52a4e72a4e519ce7394a528c632a4e728c27394a739ca7284a32
def zv3 : ℕ := 0x10846318c61194a5194a739ca528ce738ca739467394e709425194631a5294a5273a4e95ace95ad2939ce93a5674ace959ca5294a51a5252a4e72a4e529ce7394a528c632a4e728c6739ca739ce738ca53
def zv4 : ℕ := 0x1084a108c6118c6528c6749ca52952538ce53946529465094250942519d2739ce7494e75b5276ace739d253ad694a4e939c6329ca51ad2719ce719ce719ce5294a5294252a4a52846929ca3494e328ca72
def zv5 : ℕ := 0x1084a11846118ca328ca9394a52952728ce529425394a509425094650a4e749d2939ca76ad275a4e93a4e72a5694a4a949c6319c631ace72a4a729d271a4a7294a5294652a4a728429294a549ca5284a52
def zv6 : ℕ := 0x1084a308c61094652946749ca51952538ce738c6519ca50942318c2309d2939ca749ce75b5296ace549d273ad693a4eb394a529ca32ad27194e519ce5194a7294a51942329ce518c67294e538ca5284a51
def zv7 : ℕ := 0x1084a308c61194652946749ca52952538ce73946729ca5094251942519d293a4e749ce75b5296ad2749d273ad694a4eb49ca529ca52ad2719ce71a4e719ce7294a5294252a4e528c6939ce5494e528ce72
def zv8 : ℕ := 0x1084a318c61094a5294a949ca51952738ce738c6529ce70942318c630a52949ce94a4e96b5296ace74a5293ada93aceb494a529ca32ad2729ce529d2529ca9394a51946329ce718c67294e7394a7384a52
def zv9 : ℕ := 0x1084a318c61194a5294a949ca52952738ce73946739ce709425194651a5294a5294a4e96b5296ad294a5293ada94aceb59ca529ca52ad272a4e72a5272a4e9394a5294652a4e728c6939ce749ce738ce73
def zv10 : ℕ := 0x1084a318c61194a5294a94a4a52952738ce73946739ce709425194651a5294a5294a5296b5296b5294a5294b5a94aceb59ca529ca52ad272a5272a5272a529494a5294652a4e728c6939ce749ce738ce73
def zv11 : ℕ := 0x108c6318c61194a509ce739ca328ce7394a739ca7394e709465194631a5273a5273a4e95acab5ad6b294ab4a5673ad2959ca528c651a5233a4e93a4e339ce73946328c633a4e7394a739ca739ce7394a53
def zv12 : ℕ := 0x108c6318c61194a509ce73a4a328ce7394a739ca7394e709465194631a5273a5273a5295acab5b56b294ab5ad673ad2959ca528c651a5233a5293a4e339d274946328c633a4e7394a739ca739ce7394a53
def zv13 : ℕ := 0x108c6318c61194a519ce739ca328ce7394a739ca7394e709465194631a5273a5273a4e95aceb5ad6b39ceb4a5673ad2959ca5294651a5253a4e93a4e539ce73946328c633a4e7394a739ca739ce7394a53
def zv14 : ℕ := 0x108c6318c61194a519ce73a4a328ce7394a739ca7394e709465194631a5273a5273a5295aceb5b56b39ceb5ad673ad2959ca5294651a5253a5293a4e539d274946328c633a4e7394a739ca739ce7394a53
def zv15 : ℕ := 0x108c6318c61194a529ce7394a328ce7394a739ca7394e709465194631a5273a5273a5295ad2b5a56b4a52b39d673ad2959ca528c651a5273a4a93a4e739ca72946328c633a4e7394a739ca739ce7394a53
def zv16 : ℕ := 0x108ca318c61194a539ce9494a329527394e739ca739ce709465194651a5273a5294a5296b56b6a56b5ad6b3a5a93ad2b59ca5294652ad293a4a93a5293a4a929463294653a4e7394a939ce749ce7394e73
def zv17 : ℕ := 0x108ca318c61194a539ce949ca329527394e739ca739ce709465194651a5273a5294a4e96b56b6ad6b5ad6b4ada93ad2b59ca5294652ad293a4e93a5293a4e939463294653a4e7394a939ce749ce7394e73
def zv18 : ℕ := 0x1094211846118ca329d25194a5294a729c652a4a5384a5094a5094610a4e749d2939ca749d2b3a56d3a4eb494e94a52549c6319c6319ce74a4ab49ca7394a3294a5294654a4a7494a52942529ca5294212
def zv19 : ℕ := 0x10942308c21194652a4e329c652946329c673a4e728ca508c6309421194e93a4e749ce729d2d4adab49d2b59ce749d674946529ca5294e5294ab3a46738ce328c652942539ca3394a329423294e529c632
def zv20 : ℕ := 0x10942308c61194652a4e329ca5294a539c673a4e728ca5094a51942119d293a4e749ce73a52d4adab49d2b59ce94a56749ca529ca529d2739ceb3a46738ce3294a5294254a4e549ce539c65294e529c632
def zv21 : ℕ := 0x10942318c21194a52a52529c652946529c673a4e738ce708c630946119ce94a5294a4e939d2d4adad4a52d59d274a5675946529ca5294e539cab4a4a7494e538c652946539ca5394a32942529ce739c633
def zv22 : ℕ := 0x10946308c61194653a4e139ca528ce539ca73a4e7294a5094a51942319d293a4e539ce72ad6d5adab5956b5a4a74a56949ca5294a51a52939ceb3a429384e1294a528c234a4e549ce739ca5394e529ca52
def zv23 : ℕ := 0x10946308c61194653a4e339ca528ce539ca73a4e7294a5094a51942319d293a4e739ce73ad6d5adab59d6b5a4e74a56949ca5294a51a52939ceb3a46938ce3294a528c234a4e549ce739ca5394e529ca52
def zv24 : ℕ := 0x10946308c61194653a4e33a4a528ce539ca73a4e7294a5094a51942319d293a4e739d273ad6d5b5ab59d6b6ace74a56949ca5294a51a52939d2b3a46938d23394a528c234a4e549ce739ca5394e529ca52
def zv25 : ℕ := 0x10946308c61194653a4e5394a528ce539ca73a4e7294a5094a51942319d293a4e539d274ad6d5a5ab5a56b49d274a56949ca5294a51a52939cab3a4a9394a5194a528c234a4e549ce739ca5394e529ca52
def zv26 : ℕ := 0x10946318c21194a53a52739c6528c6529ca73a4e7394e708c630946319ce94a5273a4e939d6d5adad5ad6d5a5674a56959465294a5194e539cab4a4e949ce738c6528c6339ca5394a32942539ce739ca53
def zv27 : ℕ := 0x10946318c61194a53a52739ca528ce739ca73a4e7394e7094a5194631a5294a5273a4e95ad6d5adad5ad6d59d674ad6959ca5294a51a5294a4eb4a4e949ce7394a528c634a4e749ce739ca739ce739ca53
def zv28 : ℕ := 0x10946318c61194a53a52739ca528ce739ca73a4e7394e7094a5194631a5294a5273a4e95ad6d5adad5ad6d5a5674ad6959ca5294a51a5294a4eb4a4e949ce7394a528c634a4e749ce739ca739ce739ca53
def zv29 : ℕ := 0x1094a118c6118ca549d2948ca52952739ce53a4e5394a7094a5094651a52749d2949ce96b5ab69d6d5b5ab39da94ad6949c6329ca51ad2b4a46b49d2b4a467194a5294654a4a7494e929ca549ce539ca73
def zv30 : ℕ := 0x1094a308c21194654a4e749c65294e129ce73a4e729ca508c630942519ce93a4e749ce73adad6adab6adab5ad674956b4946529ca52a4e918cab3a4eb39ce728c652942539ca1394a7294a1494e529ce72
def zv31 : ℕ := 0x1094a308c61194654a4e749ca52952539ce73a4e729ca5094a51942519d293a4e749ce75b5ad6adab6adab5ad694a56b49ca529ca52ad2b39ceb3a4eb39ce7194a5294254a4e549ce939ce5494e529ce72
def zv32 : ℕ := 0x1094a318461194a34a52938ca52952729ce72a4a739ce5094a5194650a4e94a5293a4e76adad59dad6b56d39d694a52b59ca519c632aceb4a46b4a52b3a469194a5294654a4e749ca9394e749ca7294e52
def zv33 : ℕ := 0x1094a318c21194a54a52949c65294e529ce73a4e739ce708c630946519ce94a5294a4e95adad6adad6b5ad5ada74a56b5946529ca52a4e939cab4a52b4a4e938c652946539ca5394a7294a549ce739ce73
def zv34 : ℕ := 0x1094a318c61094a54a52949ca51952739ce739ce529ce7094a318c630a52949ce94a4e96b5ad6ad6b6b5ad5ada93ad6b494a529ca32ad2b49ce949d2949ca9394a51946349ce739ce7294e7394a7394a52
def zv35 : ℕ := 0x1094a318c61194a54a52948ca52952739ce73a4e739ce7094a5194651a5294a5294a4e96b5ad69dad6b5ad39da94ad6b59ca529ca52ad2b4a46b4a52b4a469194a5294654a4e749ce939ce749ce739ce73
def zv36 : ℕ := 0x1094a318c61194a54a529494a52952739ce73a4e739ce7094a5194651a5294a5294a5296b5ad6a5ad6b5ad4a5a94ad6b59ca529ca52ad2b4a4ab4a52b4a4a9294a5294654a4e749ce939ce749ce739ce73
def zv37 : ℕ := 0x1184a118c6118ce728ca9494e339d2738ce539465394a719425094651ad6739d6b59cab6b5276a4e93a5272a5ab3ace94a463394671ad272a4a729d272a4a729c6339ca72a4a72846929ca549ce538ca73
def zv38 : ℕ := 0x1184a118c6118ce728ca949ce339d2738ce539465394a719425094651ad6739d6b59ceb6b5276ace93a5273adab3ace94a463394671ad272a4e729d272a4e739c6339ca72a4a72846929ca549ce538ca73
def zv39 : ℕ := 0x1184a118c61194e728ca948ce339d2738ce539465394a719425094651ad653a56b5a4ab6b52769ce93a52739dab3ace94a4a5394672ad272a46729d272a46719c6339ca72a4a72846929ca549ce538ca73
def zv40 : ℕ := 0x1184a308c6119c672946749ce339d2538ce73946729ca5194251942519d673ace759d275b5296ad2749d273ad6b3a4eb4a4e7394673ad2719ce71a4e719ce729c6339c272a4e528c6939ce5494e528ce72
def zv41 : ℕ := 0x1184a308c6119ca729467494e339d2538ce73946729ca519425194251a5672ad295a4e95b5296a52749d274a56b3a4eb4a4e7394673ad2719ca71a4e719ca719c6339c672a4e528c6939ce5494e528ce72
def zv42 : ℕ := 0x1184a318c6119ce7294a948ce339d2738ce73946739ce719425194651ad673ad6b5acab6b52969d294a52939dab3aceb5a4e7394673ad272a4672a5272a46919c6339ca72a4e728c6939ce749ce738ce73
def zv43 : ℕ := 0x1184a318c6119ce7294a9494e339d2738ce73946739ce719425194651ad673ad6b5acab6b5296a5294a5292a5ab3aceb5a4e7394673ad272a4a72a5272a4a929c6339ca72a4e728c6939ce749ce738ce73
def zv44 : ℕ := 0x1184a318c6119ce7294a949ce339d2738ce73946739ce719425194651ad673ad6b5acab6b5296ad294a5293adab3aceb5a4e7394673ad272a4e72a5272a4e939c6339ca72a4e728c6939ce749ce738ce73
def zv45 : ℕ := 0x1184a318c6119ce7294a949ce339d2738ce73946739ce719425194651ad673ad6b5aceb6b5296ad294a5293adab3aceb5a4e7394673ad272a4e72a5272a4e939c6339ca72a4e728c6939ce749ce738ce73
def zv46 : ℕ := 0x118c2318c6119ce719ce5294e538ca73946739ca738ce719465194611ad694ad673aceb4a4eb4a56b39ceb3a5274ad275a4e738ca719d253a4a93a4a5394a529ca538ca33a4e7394a539c6729ce7394633
def zv47 : ℕ := 0x118c2318c6119ce719ce529ce338ca73946739ca738ce719465194611ad673ad673ad2b4a4eb4ad6b39ceb49d273ad275a4e73946719d253a4e93a4a5394e539c6338ca33a4e7394a539c6729ce7394633
def zv48 : ℕ := 0x118c2318c6119ce719ce52a4e338ca73946739ca738ce719465194611ad673ad673ad6b4a4eb4b56b39ceb5a5273ad275a4e73946719d253a5293a4a53952549c6338ca33a4e7394a539c6729ce7394633
def zv49 : ℕ := 0x118c6118c61194e7294e739ce5394e7394a539ca538ca719465094631ad674a5694a52b5ad295ad2b3a5294a5694ad274a4a5394a71a5273a4e939ce739ce539ca5394a53a4a738ca729c6539ce5394653
def zv50 : ℕ := 0x118c6308c6119ca729ca539ce5394e5394a739ca7294a519465194231a5693ad274a5294ad2b5ad6949d294a5294a5294a4e7394a72a52729ce92a4a7294e529ca5394653a4e5394a739ca5394e5294a52
def zv51 : ℕ := 0x118c6308c6119ca729ca53a4e5394e5394a739ca7294a519465194231a5693ad274a5694ad2b5b56949d295ad294a5294a4e7394a72a52729d292a4a72952539ca5394653a4e5394a739ca5394e5294a52
def zv52 : ℕ := 0x118c631846119ce529ce729ce5394e7294a729c67394e519465194630ad294ad693ad295a52b4ad6b4a4eb4a5294a4e95a4e7294652a4e73a4e93a4e729ce739ca5394a53a4e739467394a739ca728ca32
def zv53 : ℕ := 0x118c6318c2119ce729ce73a4a5394a5294a739ca7394e718c23094631a5294ad694ad6b4a52b5b56b4a52b5ad674a52959ca7394a729ce529ce93a4e739d2749465394a529ca528c652946539ce7394a53
def zv54 : ℕ := 0x118c6318c6109ce729ce73a4e5294e7394a7394a5294e71946318c610ad694a5294ad6b5ad2b5b5294a52b5ad693ad2949ce7394a52a52739d2739ce5394e749ca5294a339ce7294a5294a7294a738c632
def zv55 : ℕ := 0x118c6318c6119ce729ce739ce5394e7394a739ca7394e719465194631ad694ad694ad2b5ad2b5ad6b4a52b4a5694ad295a4e7394a72a5273a4e93a4e739ce739ca5394a53a4e7394a739ca739ce7394a53
def zv56 : ℕ := 0x118c6318c6119ce729ce73a4e5394e7394a739ca7394e719465194631ad694ad694ad6b5ad2b5b56b4a52b5ad694ad295a4e7394a72a5273a5293a4e739d2749ca5394a53a4e7394a739ca739ce7394a53
def zv57 : ℕ := 0x118ca108c61194a7394a749ce539d25394e539ca52946519465094251a5673a52959d295b5696ad294a5674ad6b4a5293a4a539ca72ad2929ce929ce929ce529ca539c673a4a538ca929ca3494e3294a72
def zv58 : ℕ := 0x118ca118c61194e7394e9494e539d27394e539ca5394a719465094651ad674a56b5a4eb6b5696a52b4ad693a5ab4ad294a4a539ca72ad293a4a939d293a4a729ca539ca73a4a738ca929ca549ce5394a73
def zv59 : ℕ := 0x118ca118c61194e7394e949ce539d27394e539ca5394a719465094651ad674a56b5a52b6b5696ad2b4ad694adab4ad294a4a539ca72ad293a4e939d293a4e739ca539ca73a4a738ca929ca549ce5394a73
def zv60 : ℕ := 0x118ca308c6119ca739ca749ce539d25394e739ca729ca519465194251a5693ad295a5295b56b6ad695a5694ad6b4a52b4a4e739ca73ad2929ce92a4e929ce729ca539c673a4e5394a939ce5494e5294e72
def zv61 : ℕ := 0x118ca308c6119ca739ca74a4e539d25394e739ca729ca519465194251a5693ad295a5695b56b6b5695a5695b56b4a52b4a4e739ca73ad2929d292a4e929d2739ca539c673a4e5394a939ce5494e5294e72
def zv62 : ℕ := 0x118ca31846119ce539ce9394e539d27294e729c6739ce519465194650ad294ad6b4ace96ad6b5a56b5ad2b3a56b4a4eb5a4e729c653ace93a4a93a5292a4a929ca539ca73a4e739469394e749ca728ce52
def zv63 : ℕ := 0x118ca31846119ce539ce939ce539d27294e729c6739ce519465194650ad294ad6b4ad296ad6b5ad6b5ad2b4ad6b4a4eb5a4e729c653ace93a4e93a5292a4e939ca539ca73a4e739469394e749ca728ce52
def zv64 : ℕ := 0x118ca318c2119ce739ce949ca539ce5294e739ca739ce718c23094651a5294ad6b5ad2b5ad6b6ad6b5ad6b4ada94a52b59ca739ca73a4e729ca93a5293a4e93946539ca729ca528c67294a549ce7394e73
def zv65 : ℕ := 0x118ca318c2119ce739ce94a4a539ce5294e739ca739ce718c23094651a5294ad6b5ad6b5ad6b6b56b5ad6b5b5a94a52b59ca739ca73a4e729ce93a5293a5294946539ca729ca528c67294a549ce7394e73
def zv66 : ℕ := 0x118ca318c6109ce739ce949ce529d27394e7394a529ce71946318c630ad694a52b5ad2b6b56b6ad295ad6b4adab3ad2b49ce739ca53ad2939ce739d2739ca939ca529ca539ce7294a7294e7394a738ca52
def zv67 : ℕ := 0x118ca318c6109ce739ce94a4e529d27394e7394a529ce71946318c630ad694a52b5ad6b6b56b6b5295ad6b5b5ab3ad2b49ce739ca53ad2939d2739d2739ce949ca529ca539ce7294a7294e7394a738ca52
def zv68 : ℕ := 0x118ca318c6119ce739ce9494e339d27394e739ca739ce719465194651ad673ad6b5aceb6b56b6a56b5ad6b3a5ab3ad2b5a4e7394673ad293a4a93a5293a4a929c6339ca73a4e7394a939ce749ce7394e73
def zv69 : ℕ := 0x118ca318c6119ce739ce9494e539d27394e739ca739ce719465194651ad694ad6b5aceb6b56b6a56b5ad6b3a5ab4ad2b5a4e739ca73ad293a4a93a5293a4a929ca539ca73a4e7394a939ce749ce7394e73
def zv70 : ℕ := 0x118ca318c6119ce739ce949ce539d27394e739ca739ce719465194651ad694ad6b5ad2b6b56b6ad6b5ad6b4adab4ad2b5a4e739ca73ad293a4e93a5293a4e939ca539ca73a4e7394a939ce749ce7394e73
def zv71 : ℕ := 0x118ca318c6119ce739ce94a4e539d27394e739ca739ce719465194651ad694ad6b5ad6b6b56b6b56b5ad6b5b5ab4ad2b5a4e739ca73ad293a5293a5293a52949ca539ca73a4e7394a939ce749ce7394e73
def zv72 : ℕ := 0x11942118c61184e729d2529ce738ca739c653a4e5384a7194a5094611ad6559567394ab4a52b4ad6d3a52b59d275ad654a421394e709d274a4eb49ca7494e339ce738ca34a4a7494e529c2529ce539c233
def zv73 : ℕ := 0x11942118c6118ce729d25294e738ca739c653a4e5384a7194a5094611ad6759d6739cab4a52b4a56d3a52b495275ad654a463394e719d274a4ab49ca7494a329ce738ca34a4a7494e529c2529ce539c233
def zv74 : ℕ := 0x11942118c6118ce729d2529ce738ca739c653a4e5384a7194a5094611ad6759d6739ceb4a52b4ad6d3a52b59d275ad654a463394e719d274a4eb49ca7494e339ce738ca34a4a7494e529c2529ce539c233
def zv75 : ℕ := 0x11942308c6119c672a4e329ce738ca539c673a4e728ca5194a51942119d6b3ace739d273a52d4adab49d2b59ce75a5674a4e7394e719d2739ceb3a46738ce329ce738c234a4e549ce539c65294e529c632
def zv76 : ℕ := 0x11942308c6119ca72a4e3294e738ca539c673a4e728ca5194a5194211a56b4ad253a4e93a52d4a5ab49d2b4a4e75a5674a4e7394e719d2739cab3a46738ca319ce738c634a4e549ce539c65294e529c632
def zv77 : ℕ := 0x1194231846119ce52a52518ce738ca729c672a4a738ce5194a5194610ad2b5ad672aca949d2d39dad4a4ed39ce75a5275a4e7294a519ce74a46b4a4a73946519ce738ca34a4e749ca53946729ca7294612
def zv78 : ℕ := 0x11942318c2119ce72a525294a738c6529c673a4e738ce718c63094611a52b5ad673aceb39d2d4a5ad4a52d4a5255a56759ca7394e7194e539c6b4a4a7494a5294a738ca339ca5394a32942529ce739c633
def zv79 : ℕ := 0x11942318c6119ce72a52528ce738ca739c673a4e738ce7194a5194611ad6b5ad673acab4a52d49dad4a52d39d275ad675a4e7394e719d274a46b4a4a74946519ce738ca34a4e749ce539c6729ce739c633
def zv80 : ℕ := 0x11942318c6119ce72a525294e738ca739c673a4e738ce7194a5194611ad6b5ad673acab4a52d4a5ad4a52d495275ad675a4e7394e719d274a4ab4a4a7494a529ce738ca34a4e749ce539c6729ce739c633
def zv81 : ℕ := 0x11942318c6119ce72a525294e738ca739c673a4e738ce7194a5194611ad6b5ad673aceb4a52d4a5ad4a52d4a5275ad675a4e7394e719d274a4ab4a4a7494a529ce738ca34a4e749ce539c6729ce739c633
def zv82 : ℕ := 0x11942318c6119ce72a52529ce738ca739c673a4e738ce7194a5194611ad6b5ad673acab4a52d4adad4a52d59d275ad675a4e7394e719d274a4eb4a4a7494e539ce738ca34a4e749ce539c6729ce739c633
def zv83 : ℕ := 0x11942318c6119ce72a52529ce738ca739c673a4e738ce7194a5194611ad6b5ad673aceb4a52d4adad4a52d59d275ad675a4e7394e719d274a4eb4a4a7494e539ce738ca34a4e749ce539c6729ce739c633
def zv84 : ℕ := 0x11946108c61194a739ce5394e7394e539ca53a4e528c65194a5094231a5694a52749ce94ad6b5a56b4a56949d295a5673a4a539ce71a52939cab39ca9394a319ce7394654a4a5494e729c63394e329c652
def zv85 : ℕ := 0x11946108c61194a739ce539ce7394e539ca53a4e528c65194a5094231a5694a52749d294ad6b5ad6b4a5695a5295a5673a4a539ce71a52939ceb39ca9394e329ce7394654a4a5494e729c63394e329c652
def zv86 : ℕ := 0x11946118461194e539d27294e7394e729ca52a4a538ca5194a5094630ad295a5693a4e95a56b4a56d4ad2b49d295a5274a4a529ca51a4e94a4ab49ce939ca529ce7394a54a4a7494a72946539ca5294632
def zv87 : ℕ := 0x11946118c61194e739d27394e7394e739ca53a4e538ca7194a5094631ad695a5694a4eb5ad6b5a56d4ad6b49d695ad674a4a539ce71a5294a4ab49ce949ca529ce7394a54a4a7494e729c6539ce539c653
def zv88 : ℕ := 0x11946118c61194e739d2739ce7394e739ca53a4e538ca7194a5094631ad695a5694a52b5ad6b5ad6d4ad6b5a5695ad674a4a539ce71a5294a4eb49ce949ce539ce7394a54a4a7494e729c6539ce539c653
def zv89 : ℕ := 0x1194630846119ca53a4e5294e7394e529ca72a4a7294a3194a5194230a52b4ad273a4e74a56d4a5ab5a52b49ce959d294a4e729ca52a4e939cab3a4a9294a519ce7394654a4e549ca7394a5394a5194a31
def zv90 : ℕ := 0x1194630846119ca53a4e529ce7394e529ca72a4a7294a3194a5194230a52b4ad273a5274a56d4adab5a52b5a4e959d294a4e729ca52a4e939ceb3a4a9294e529ce7394654a4e549ca7394a5394a5194a31
def zv91 : ℕ := 0x11946308c6109ca73a4e539ce7294e539ca739ce5194a5194a318c210a56b4a4e74a5294ad6d5ad695a56b5a5294a56939ce739ce52a529394e939ca738ca529ce72946349ce539ce5294a528ca5294631
def zv92 : ℕ := 0x11946308c6109ca73a4e53a4e7294e539ca739ce5194a5194a318c210a56b4a4e74a5694ad6d5b5695a56b6ad294a56939ce739ce52a5293952939ca738ce539ce72946349ce539ce5294a528ca5294631
def zv93 : ℕ := 0x11946308c6119ca73a4e539ce7394e539ca73a4e7294a5194a5194231a56b4ad274a5294ad6d5adab5a56b5a5295a5694a4e739ce72a52939ceb3a4a9394e529ce7394654a4e549ce739ca5394e529ca52
def zv94 : ℕ := 0x11946308c6119ca73a4e53a4e7394e539ca73a4e7294a5194a5194231a56b4ad274a5694ad6d5b5ab5a56b6ad295a5694a4e739ce72a52939d2b3a4a93952539ce7394654a4e549ce739ca5394e529ca52
def zv95 : ℕ := 0x1194631846119ce53a527294e7394e729ca72a4a7394e5194a5194630ad2b5ad693ace95a56d4a5ad5ad2d49d295a5295a4e729ca52a4e94a4ab4a4e939ca729ce7394a54a4e749ca7394a739ca7294a32
def zv96 : ℕ := 0x1194631846119ce53a52729ce7394e729ca72a4a7394e5194a5194630ad2b5ad693ad295a56d4adad5ad2d5a5295a5295a4e729ca52a4e94a4eb4a4e939ce739ce7394a54a4e749ca7394a739ca7294a32
def zv97 : ℕ := 0x11946318c2119ce73a52739ca7394a529ca73a4e7394e718c63094631a52b5ad694ad2b4a56d5adad5ad6d5a5675a56959ca739ce729ce739cab4a4e949ce7394a7394a539ca5394a52946539ce739ca53
def zv98 : ℕ := 0x11946318c2119ce73a5273a4a7394a529ca73a4e7394e718c63094631a52b5ad694ad6b4a56d5b5ad5ad6d6ad675a56959ca739ce729ce739ceb4a4e949d27494a7394a539ca5394a52946539ce739ca53
def zv99 : ℕ := 0x11946318c6109ce73a52739ce7294e739ca739ce5294e7194a318c610ad6b5a5294ad2b5ad6d5ad6b5ad6d5a5694ad6949ce739ce52a52949ce949ce7494a739ce7294a349ce739ce5294a7294a7394632
def zv100 : ℕ := 0x11946318c6119ce73a52729ce7394e739ca73a4e7394e7194a5194631ad6b5ad693ad2b5a56d4adad5ad2d59d295ad695a4e739ce72a5294a4eb4a4e949ce739ce7394a54a4e749ce739ca739ce739ca33
def zv101 : ℕ := 0x11946318c6119ce73a527394e7394e739ca73a4e7394e7194a5194631ad6b5ad694aceb5ad6d5a5ad5ad6d49d695ad695a4e739ce72a5294a4ab4a4e949ca729ce7394a54a4e749ce739ca739ce739ca53
def zv102 : ℕ := 0x11946318c6119ce73a52739ce7394e739ca73a4e7394e7194a5194631ad6b5ad694ad2b5ad6d5adad5ad6d5a5695ad695a4e739ce72a5294a4eb4a4e949ce739ce7394a54a4e749ce739ca739ce739ca53
def zv103 : ℕ := 0x1194a108461194a549ce7394e739d2529ce52a4a529463194a5094250a5294a52949ce75adab5a56b5ad694a52b59d293a4a52a4a52aceb39cab39ceb29ca519ce739c674a4a5494a9294a3494a3194a51
def zv104 : ℕ := 0x1194a108c61194a749ce7494e739d2539ce53a4e529465194a5094251a5694a52959ce95b5ab6a56b5ada94a56b5a5693a4a53a4e72ad2b39cab39ceb39ca519ce739c674a4a5494e929ca3494e329ca72
def zv105 : ℕ := 0x1194a108c61194a749ce749ce739d2539ce53a4e529465194a5094251a5694a52959d295b5ab6ad6b5ada95ad6b5a5693a4a53a4e72ad2b39ceb39ceb39ce529ce739c674a4a5494e929ca3494e329ca72
def zv106 : ℕ := 0x1194a118461194e549d29394e739d2729ce52a4a5394a5194a5094650ad295a56b4a4e96adab5a56d5b56b4a56b5a5294a4a52a4a52aceb4a4ab49d2b3a4a729ce739ca74a4a7494a9294a549ca5294a52
def zv107 : ℕ := 0x1194a118c61094e749d29494e729d2739ce539ce3294a7194a308c630ad6959d2b5a4eb6b5ab6a52b5b5ab4a5ab4ad6939ca53a4e52ad2b49ca94952949c6729ce729ca549ca7394e7194a5394a5394652
def zv108 : ℕ := 0x1194a118c61094e749d2949ce729d2739ce539ce3294a7194a308c630ad6959d2b5a52b6b5ab6ad2b5b5ab5adab4ad6939ca53a4e52ad2b49ce94952949ca739ce729ca549ca7394e7194a5394a5394652
def zv109 : ℕ := 0x1194a118c6118ce749d2948ce739d2739ce53a4e5394a7194a5094651ad6759d6b59ceb6b5ab69d6d5b5ab39dab5ad694a4633a4e71ad2b4a46b49d2b4a46719ce739ca74a4a7494e929ca549ce539ca73
def zv110 : ℕ := 0x1194a118c61194e749d29494e739d2739ce53a4e5394a7194a5094651ad695a56b5a4eb6b5ab6a56d5b5ab4a5ab5ad694a4a53a4e72ad2b4a4ab49d2b4a4a729ce739ca74a4a7494e929ca549ce539ca73
def zv111 : ℕ := 0x1194a118c61194e749d2949ce739d2739ce53a4e5394a7194a5094651ad695a56b5a52b6b5ab6ad6d5b5ab5adab5ad694a4a53a4e72ad2b4a4eb49d2b4a4e739ce739ca74a4a7494e929ca549ce539ca73
def zv112 : ℕ := 0x1194a30846119ca54a4e7394e739d2529ce72a4a729ca3194a5194250a52b4ad294a4e75adad5a5ab6ad6b4a52b59d2b4a4e72a4a53aceb39cab3a4eb29ca719ce739c674a4e549ca9394e5494a5194e51
def zv113 : ℕ := 0x1194a30846119ca54a4e739ce739d2529ce72a4a729ca3194a5194250a52b4ad294a5275adad5adab6ad6b5ad2b59d2b4a4e72a4a53aceb39ceb3a4eb29ce729ce739c674a4e549ca9394e5494a5194e51
def zv114 : ℕ := 0x1194a308c2119ca74a4e749ca739ce329ce73a4e729ca518c630942519d2b4ad295a5294adad6adab6adab5ad6959d6b49ca73a4e73a4e9294ab3a4eb39ce7294a739c6739ca3394a7294a3494e529ce72
def zv115 : ℕ := 0x1194a308c6109ca74a4e749ce729d2539ce739ce519ca5194a318c230a56b4a4e95a5295b5ad6ad696adab5ad6b4a56b39ce73a4e53ad2b394e939ce9394a729ce729c6549ce539ce7294e538ca5294a51
def zv116 : ℕ := 0x1194a308c6119c674a4e7494e739d2539ce73a4e729ca5194a51942519d6b3ace759ce75b5ad6a5ab6adab4a56b5a56b4a4e73a4e73ad2b39cab3a4eb39ca719ce739c274a4e549ce939ce5494e529ce72
def zv117 : ℕ := 0x1194a308c6119ca74a4e7494e739d2539ce73a4e729ca5194a5194251a56b4ad295a4e95b5ad6a5ab6adab4a56b5a56b4a4e73a4e73ad2b39cab3a4eb39ca719ce739c674a4e549ce939ce5494e529ce72
def zv118 : ℕ := 0x1194a308c6119ca74a4e749ce739d2539ce73a4e729ca5194a5194251a56b4ad295a5295b5ad6adab6adab5ad6b5a56b4a4e73a4e73ad2b39ceb3a4eb39ce729ce739c674a4e549ce939ce5494e529ce72
def zv119 : ℕ := 0x1194a308c6119ca74a4e74a4e739d2539ce73a4e729ca5194a5194251a56b4ad295a5695b5ad6b5ab6adab6b56b5a56b4a4e73a4e73ad2b39d2b3a4eb39d2739ce739c674a4e549ce939ce5494e529ce72
def zv120 : ℕ := 0x1194a31842119ce54a529394a739ce519ce72a4a739ce518c63094650a4eb5ad6b4ace95a5ad5a5ad6b56d4a56959d2b59ca72a4a53a4a939c6b4a52b3a4a9294a739ca739ca53946728ca549ca7294e52
def zv121 : ℕ := 0x1194a31842119ce54a52939ca739ce519ce72a4a739ce518c63094650a4eb5ad6b4ad295a5ad5adad6b56d5ad6959d2b59ca72a4a53a4a939cab4a52b3a4e9394a739ca739ca53946728ca549ca7294e52
def zv122 : ℕ := 0x1194a318c2109ce74a52949ca729ce529ce739ce529ce718c6108c630a52b5a52b5ad2b5adad6ad6b6b5ad5ada94a56b494a73a4e53a4e9394a949d2949ca9394a729ca5394a5294a518ca5394a7394a52
def zv123 : ℕ := 0x1194a318c2119ce74a5294946739ce529ce73a4e739ce718c630946519ceb5ad6b5aceb5adad6a5ad6b5ad4a5a75a56b594673a4e73a4e939c6b4a52b4a4a928c6739ca739ca5394a7294a549ce739ce73
def zv124 : ℕ := 0x1194a318c2119ce74a529494a739ce529ce73a4e739ce718c63094651a52b5ad6b5aceb5adad6a5ad6b5ad4a5a95a56b59ca73a4e73a4e939c6b4a52b4a4a9294a739ca739ca5394a7294a549ce739ce73
def zv125 : ℕ := 0x1194a318c2119ce74a52949ca739ce529ce73a4e739ce718c63094651a52b5ad6b5ad2b5adad6adad6b5ad5ada95a56b59ca73a4e73a4e939cab4a52b4a4e9394a739ca739ca5394a7294a549ce739ce73
def zv126 : ℕ := 0x1194a318c2119ce74a5294a4a739ce529ce73a4e739ce718c63094651a52b5ad6b5ad6b5adad6b5ad6b5ad6b5a95a56b59ca73a4e73a4e939ceb4a52b4a529494a739ca739ca5394a7294a549ce739ce73
def zv127 : ℕ := 0x1194a318c6109ce74a529494e729d2739ce739ce529ce7194a318c630ad6b5a52b5aceb6b5ad6a56b6b5ad4a5ab4ad6b49ce73a4e53ad2b49ca949d2949c6929ce729ca549ce739ce7294e7394a7394a52
def zv128 : ℕ := 0x1194a318c6109ce74a52949ce729d2739ce739ce529ce7194a318c630ad6b5a52b5aceb6b5ad6ad6b6b5ad5adab4ad6b49ce73a4e53ad2b49ce949d2949ca939ce729ca549ce739ce7294e7394a7394a52
def zv129 : ℕ := 0x1194a318c6109ce74a52949ce729d2739ce739ce529ce7194a318c630ad6b5a52b5ad2b6b5ad6ad6b6b5ad5adab4ad6b49ce73a4e53ad2b49ce949d2949ca939ce729ca549ce739ce7294e7394a7394a52
def zv130 : ℕ := 0x1194a318c6119ce74a529494e739d2739ce73a4e739ce7194a5194651ad6b5ad6b5aceb6b5ad6a5ad6b5ad4a5ab5ad6b5a4e73a4e73ad2b4a4ab4a52b4a4a929ce739ca74a4e749ce939ce749ce739ce73
def zv131 : ℕ := 0x1194a318c6119ce74a52949ce739d2739ce73a4e739ce7194a5194651ad6b5ad6b5ad2b6b5ad6adad6b5ad5adab5ad6b5a4e73a4e73ad2b4a4eb4a52b4a4e939ce739ca74a4e749ce939ce749ce739ce73
def zv132 : ℕ := 0x12846118c6119d2918ca738d2549ce738ca53946538ca729425094631b5a74adab5aced5ace759ce929ce73956b4ace74ace7494a92a5252a46729ce529c651a4a549ce72a4a72846729c6539ce538c653
def zv133 : ℕ := 0x12846308c611a4e91946538d2549ce538ca739467294a529425194231ada93b5695aceb4ace959d27394e73952b4a4e94ad29494a93a52519c671a4a5194650a4a549ca72a4e528c6739ca5394e528ca52
def zv134 : ℕ := 0x12846308c611a4e9194653952549ce538ca739467294a529425194231ada93b5695ad2b4ace95a527394e749d2b4a4e94ad29494a93a52519ca71a4a5194a51a4a549ca72a4e528c6739ca5394e528ca52
def zv135 : ℕ := 0x12846308c611a4e9194653a52549ce538ca739467294a529425194231ada93b5695adab4ace95b527394e74ad2b4a4e94ad29494a93a52519d271a4a5195253a4a549ca72a4e528c6739ca5394e528ca52
def zv136 : ℕ := 0x128463184611a527194a728d2549ce728ca729427394e529425194630b5694b5ab4b4eb5a4e949d2939ca93952b4a4a95ad29394673a4e52a4672a4e519c671a4a549ce72a4e728c27394a739ca7284a32
def zv137 : ℕ := 0x12846318c611a529194a738d2549ce738ca739467394e729425194631b5a94b5ab5b4ed5ace959d2939ce93956b4ace95ad29494a93a5252a4672a4e529c671a4a549ce72a4e728c6739ca739ce738ca53
def zv138 : ℕ := 0x12846318c611a529194a739d2549ce738ca739467394e729425194631b5a94b5ab5b56d5ace95ad2939ce939d6b4ace95ad29494a93a5252a4e72a4e529ce73a4a549ce72a4e728c6739ca739ce738ca53
def zv139 : ℕ := 0x12846318c611a529194a739d2549ce738ca739467394e729425194631b5a94b5ab5b56d5ace95ad2939ce93a56b4ace95ad29494a93a5252a4e72a4e529ce73a4a549ce72a4e728c6739ca739ce738ca53
def zv140 : ℕ := 0x128c2308c611a4e919ca329527494a53946739ca728ca529465194211adab4b5674ad2b3a4eb4a569394e93a4e95a5274ad29494e929d2529ca92a46528ca31a4e7494a53a4e5394a539c65294e5294632
def zv141 : ℕ := 0x128c2308c611a4e919ca32a527494a53946739ca728ca529465194211adab4b5674adab3a4eb4b569394e95a4e95a5274ad29494e929d2529d292a46528d233a4e7494a53a4e5394a539c65294e5294632
def zv142 : ℕ := 0x128c2318c611a52919ce528d27494a73946739ca738ce729465194611b5ab5b5a94b4ed4a4eb49d6b39ceb29d295ad275ad29494e929d253a4693a4a5394651a4e7494e53a4e7394a539c6729ce7394633
def zv143 : ℕ := 0x128c2318c611a52919ce529527494a73946739ca738ce729465194611b5ab5b5a94b52d4a4eb4a56b39ceb3a5295ad275ad29494e929d253a4a93a4a5394a52a4e7494e53a4e7394a539c6729ce7394633
def zv144 : ℕ := 0x128c2318c611a52919ce529d27494a73946739ca738ce729465194611b5ab5b5a94b56d4a4eb4ad6b39ceb49d295ad275ad29494e929d253a4e93a4a5394e53a4e7494e53a4e7394a539c6729ce7394633
def zv145 : ℕ := 0x128c6108c6119ce9294a539d2749ce5394a539ca528c6529465094231ada94ad695a56b4ad295ad2939d274a52b5a5273ace749ce92a52729ce929ca7294e32a4e749ca73a4a538ca729c63394e3294652
def zv146 : ℕ := 0x128c611846119d27294e72952749ce7294a529c6538ca529465094630b5695adab4ad2b5a5294a52b3a4e939d2b5a4e74ace739ca72a4e73a4a939ce729ca52a4e749ce73a4a738c672946539ca528c632
def zv147 : ℕ := 0x128c6118c6109d29294e739d2739ce7394a5394a328ca72946308c610b5a95a56b5ad6d5ad295ace93a5294a56b4ad273a4e749ce72a52739ce7394e5394a53a4e739ce539ca728ca519465294a538c232
def zv148 : ℕ := 0x128c6118c6119d29294e73952749ce7394a539ca538ca729465094631b5a95adab5ad2d5ad295a52b3a52939d6b5ad274ace749ce92a5273a4a939ce739ca52a4e749ce73a4a738ca729c6539ce5394653
def zv149 : ℕ := 0x128c6118c6119d29294e739d2749ce7394a539ca538ca729465094631b5a95adab5ad6d5ad295ad2b3a5294a56b5ad274ace749ce92a5273a4e939ce739ce53a4e749ce73a4a738ca729c6539ce5394653
def zv150 : ℕ := 0x128c6308c211a4e929ca539ce749ca3294a739ca7294a528c23094231a56b4b5695ad6b3a52b5ad6949d294a52959d294a4e949ce939ce5194a92a4a7294e529ca749ca729ca328c6529463394e5294a52
def zv151 : ℕ := 0x128c6308c610a4e929ca539d2739ce5394a7394a5194a52946318c210adab4ad295ad6b4ad2b5ad2749d294a52b4a5293a52949ce73a527294e729ca528ca52a4e739ca539ce5294a5294a528ca528c631
def zv152 : ℕ := 0x128c6308c611a4e929ca53952749ce5394a739ca7294a529465194231adab4b5695ad2b4ad2b5a56949d2939d2b5a5294ad2949ce93a52729ca92a4a7294a51a4e749ca73a4e5394a739ca5394e5294a52
def zv153 : ℕ := 0x128c6308c611a4e929ca539d2749ce5394a739ca7294a529465194231adab4b5695ad6b4ad2b5ad6949d294a52b5a5294ad2949ce93a52729ce92a4a7294e52a4e749ca73a4e5394a739ca5394e5294a52
def zv154 : ℕ := 0x128c6308c611a4e929ca53a52749ce5394a739ca7294a529465194231adab4b5695adab4ad2b5b56949d295ad2b5a5294ad2949ce93a52729d292a4a7295253a4e749ca73a4e5394a739ca5394e5294a52
def zv155 : ℕ := 0x128c63184211a52729ce729ce749ca5194a729c67394e528c23094630ad2b5b5ab4b56b49d2b4ad6b4a4eb4a52959ce95a4e939ca739ca529ca93a4e729ce739ca749ce729ca528c2528c6539ca728ca32
def zv156 : ℕ := 0x128c63184611a52729ce72952749ce7294a729c67394e529465194630b56b5b5ab4b52b5a52b4a56b4a4eb39d2b5a4e95ad2939ca73a4e73a4a93a4e729ca72a4e749ce73a4e739467394a739ca728ca32
def zv157 : ℕ := 0x128c63184611a52729ce729d2749ce7294a729c67394e529465194630b56b5b5ab4b56b5a52b4ad6b4a4eb4a52b5a4e95ad2939ca73a4e73a4e93a4e729ce73a4e749ce73a4e739467394a739ca728ca32
def zv158 : ℕ := 0x128c6318c210a52929ce739ce739ca5294a7394a5294e728c2108c610ad6b5ad6b5b56d4a52b5ad294a52b4a5694a52949ce949ce739ce5294a739ce5394a739ca739ce5294a518c6318c65294a738c632
def zv159 : ℕ := 0x128c6318c211a52929ce739ce749ca5294a739ca7394e728c23094631ad6b5b5ab5b56d4a52b5ad6b4a52b4a5695a5295a4e949ce939ce529ca93a4e739ce739ca749ce729ca528c652946539ce7394a53
def zv160 : ℕ := 0x128c6318c211a52929ce73a4e749ca5294a739ca7394e728c23094631ad6b5b5ab5b5ad4a52b5b56b4a52b5ad695a5295a4e949ce939ce529ce93a4e739d2749ca749ce729ca528c652946539ce7394a53
def zv161 : ℕ := 0x128c6318c610a52929ce739d2739ce7394a7394a5294e72946318c610b5ab5ad6b5b56d5ad2b5ad294a52b4a56b4ad294a52949ce73a52739ce739ce5394a73a4e739ce539ce7294a5294a7294a738c632
def zv162 : ℕ := 0x128c6318c610a52929ce73a52739ce7394a7394a5294e72946318c610b5ab5ad6b5b5ad5ad2b5b5294a52b5ad6b4ad294a52949ce73a52739d2739ce5394e74a4e739ce539ce7294a5294a7294a738c632
def zv163 : ℕ := 0x128c6318c611a52919ce738d2749ce7394a739ca7394e729465194631b5ab5b5ab5b4ed5aceb59d6b39ceb2956b5ad295ad29494e93a5253a4693a4e539c671a4e749ce73a4e7394a739ca739ce7394a53
def zv164 : ℕ := 0x128c6318c611a52919ce73952749ce7394a739ca7394e729465194631b5ab5b5ab5b52d5aceb5a56b39ceb39d6b5ad295ad29494e93a5253a4a93a4e539ca72a4e749ce73a4e7394a739ca739ce7394a53
def zv165 : ℕ := 0x128c6318c611a52919ce739d2749ce7394a739ca7394e729465194631b5ab5b5ab5b56d5aceb5ad6b39ceb4a56b5ad295ad29494e93a5253a4e93a4e539ce73a4e749ce73a4e7394a739ca739ce7394a53
def zv166 : ℕ := 0x128c6318c611a52929ce729d2749ce7394a739ca7394e729465194631b5ab5b5ab4b56d5a52b4ad6b4a4eb49d2b5ad295ad2949ce93a5273a4e93a4e739ce73a4e749ce73a4e7394a739ca739ce7394a33
def zv167 : ℕ := 0x128c6318c611a52929ce73952749ce7394a739ca7394e729465194631b5ab5b5ab5b52d5ad2b5a56b4a52b39d6b5ad295ad2949ce93a5273a4a93a4e739ca72a4e749ce73a4e7394a739ca739ce7394a53
def zv168 : ℕ := 0x128c6318c611a52929ce739d2749ce7394a739ca7394e729465194631b5ab5b5ab5b56d5ad2b5ad6b4a52b49d6b5ad295ad2949ce93a5273a4e93a4e739ce73a4e749ce73a4e7394a739ca739ce7394a53
def zv169 : ℕ := 0x128c6318c611a52929ce739d2749ce7394a739ca7394e729465194631b5ab5b5ab5b56d5ad2b5ad6b4a52b4a56b5ad295ad2949ce93a5273a4e93a4e739ce73a4e749ce73a4e7394a739ca739ce7394a53
def zv170 : ℕ := 0x128c6318c611a52929ce73a52749ce7394a739ca7394e729465194631b5ab5b5ab5b5ad5ad2b5b56b4a52b5ad6b5ad295ad2949ce93a5273a5293a4e739d274a4e749ce73a4e7394a739ca739ce7394a53
def zv171 : ℕ := 0x128ca10846119ce7394a7395274a525294e529c652946329465094250ad694ad6b5a5295ad695a5294a5273a52d59ce93ace73a4a73ace929ca929ce919ca51a4e74a4a93a4a538c69294a3494a318ca51
def zv172 : ℕ := 0x128ca11846119d27394e9395274a527294e529c65394a529465094650b5695adad5ad2b6ad695a52b4ad293a56d5a4e94ace73a4a73ace93a4a939d292a4a72a4e74a4e93a4a738c69294a549ca528ca52
def zv173 : ℕ := 0x128ca3084611a4e739ca7395274a525294e729c6729ca329465194250ad6b4b56b5ad295ad6b5a5695a5293a52d59ceb4ad293a4a74ace929ca92a4e919ca71a4e74a4a93a4e539469394e5494a518ce51
def zv174 : ℕ := 0x128ca308c210a4e939ca749ce73a4e3294e7394a519ca528c2108c230a56b4ad2b6ad6b4ad6b6ad275a5694ad6b49d2b39ce94a4e74a4e718ca729ce7294a729ca73a4a7294a318c6518ca338ca528ca51
def zv175 : ℕ := 0x128ca308c211a4e939ca749ce74a4e3294e739ca729ca528c23094251a56b4b56b6ad6b4ad6b6ad695a5694ad6b59d2b4a4e94a4e94a4e7194a92a4e929ce729ca74a4a929ca328c67294a3494e5294e72
def zv176 : ℕ := 0x128ca308c610a4e939ca749d273a525394e7394a519ca52946318c230adab4ad2b6ad6b5b56b6ad275a5694ad6d4a52b3a5294a4e74ad29294e729ce7294a72a4e73a4a739ce5294a7294e538ca528ca51
def zv177 : ℕ := 0x128ca308c611a4e939ca7495274a525394e739ca729ca529465194251adab4b56b6ad2b5b56b6a5695a5693a56d5a52b4ad294a4e94ad2929ca92a4e929ca71a4e74a4a93a4e5394a939ce5494e5294e72
def zv178 : ℕ := 0x128ca308c611a4e939ca749d274a525394e739ca729ca529465194251adab4b56b6ad6b5b56b6ad695a5694ad6d5a52b4ad294a4e94ad2929ce92a4e929ce72a4e74a4a93a4e5394a939ce5494e5294e72
def zv179 : ℕ := 0x128ca3184211a52739ce9394e74a4e5194e729c6739ce528c23094650ad2b5b5ad5b52b5a56b5a56b5ad2b3a56b59ceb5a4e93a4a74a4a729c693a5292a4a929ca74a4e929ca528c2728ca549ca728ce52
def zv180 : ℕ := 0x128ca318c210a52939ce949ce73a4e5294e7394a529ce728c2108c630ad6b5ad6d6b56d5ad6b6ad295ad6b4adab4a52b49ce94a4e74a4e7294a739d2739ca939ca73a4e7294a518c6518ca5394a738ca52
def zv181 : ℕ := 0x128ca318c211a52939ce949ce74a4e5294e739ca739ce728c23094651ad6b5b5ad6b56d5ad6b6ad6b5ad6b4adab5a52b5a4e94a4e94a4e729ca93a5293a4e939ca74a4e929ca528c67294a549ce7394e73
def zv182 : ℕ := 0x128ca318c211a52939ce94a4e74a4e5294e739ca739ce728c23094651ad6b5b5ad6b5ad5ad6b6b56b5ad6b5b5ab5a52b5a4e94a4e94a4e729ce93a5293a52949ca74a4e929ca528c67294a549ce7394e73
def zv183 : ℕ := 0x128ca318c610a52939ce9495273a527394e7394a529ce72946318c630b5ab5ad6d6b52d6b56b6a5295ad6b3a5ad4ad2b4a5294a4e74ad2939ca739d2739c692a4e73a4e739ce7294a7294e7394a738ca52
def zv184 : ℕ := 0x128ca318c610a52939ce949d273a527394e7394a529ce72946318c630b5ab5ad6d6b56d6b56b6ad295ad6b4adad4ad2b4a5294a4e74ad2939ce739d2739ca93a4e73a4e739ce7294a7294e7394a738ca52
def zv185 : ℕ := 0x12942308c211a4e92a4e3294e94946329c673a4e728ca528c63094211a56d5b5674ad2b29d2d4a5ab49d2b4a4e769d674a4e949d29294e52946b3a46738ca319ce9494a539ca3394a329423294e529c632
def zv186 : ℕ := 0x12942308c611a4e92a4e329d29494a539c673a4e728ca5294a5194211adad5b5674ad6b3a52d4adab49d2b59ce96a5674ad2949d2929d2739ceb3a46738ce32a529494a54a4e549ce539c65294e529c632
def zv187 : ℕ := 0x129423184611a5272a52518d29494a729c672a4a738ce5294a5194610b56d6b5a93b4eb49d2d39dad4a4ed39ce96a5275ad2939ce729ce74a46b4a4a7394651a529494e54a4e749ca53946729ca7294612
def zv188 : ℕ := 0x12942318c211a5292a52528ce94946529c673a4e738ce728c63094611ad6d6b5a94b4ed39d2d49dad4a52d39d276a5675a4e949d29294e539c2b4a4a74946519ce9494e539ca5394a32942529ce739c633
def zv189 : ℕ := 0x12942318c611a5292a52528d29494a739c673a4e738ce7294a5194611b5ad6b5a94b4ed4a52d49dad4a52d39d296ad675ad2949d2929d274a46b4a4a7494651a529494e54a4e749ce539c6729ce739c633
def zv190 : ℕ := 0x12942318c611a5292a52529529494a739c673a4e738ce7294a5194611b5ad6b5a94b52d4a52d4a5ad4a52d4a5296ad675ad2949d2929d274a4ab4a4a7494a52a529494e54a4e749ce539c6729ce739c633
def zv191 : ℕ := 0x1294610846119ce739ce52952949ce529ca52a4a528c63294a5094230ad6b5ad694a5294a56b4a56b4a52949ceb69d273ace73a4e72a4e939cab39ca9294a31a52949ca74a4a5494a729463394a3194631
def zv192 : ℕ := 0x12946108c6119ce939ce53952949ce539ca53a4e528c65294a5094231adab5ad695a52b4ad6b5a56b4a56949d2b6a5673ace74a5292a52939cab39ca9394a31a52949ca74a4a5494e729c63394e329c652
def zv193 : ℕ := 0x12946108c6119ce939ce539d2949ce539ca53a4e528c65294a5094231adab5ad695a56b4ad6b5ad6b4a5695a52b6a5673ace74a5292a52939ceb39ca9394e32a52949ca74a4a5494e729c63394e329c652
def zv194 : ℕ := 0x1294611846119d2739d272952949ce729ca52a4a538ca5294a5094630b56b6adab4ad2b5a56b4a56d4ad2b49d2b6a5274ace73a4e72a4e94a4ab49ce939ca52a52949ce74a4a7494a72946539ca5294632
def zv195 : ℕ := 0x12946118c6109d2939d273952939ce739ca539ce328ca7294a308c610b5ab6a56b5ad2d5ad6b5a52b4ad6b49d6b5ad673a4e74a5272a52949ca9494e7494652a52939ce549ca7394e519465294a5394232
def zv196 : ℕ := 0x12946118c6119d2939d273952949ce739ca53a4e538ca7294a5094631b5ab6adab5ad2d5ad6b5a56d4ad6b49d6b6ad674ace74a5292a5294a4ab49ce949ca52a52949ce74a4a7494e729c6539ce539c653
def zv197 : ℕ := 0x12946118c6119d2939d2739d2949ce739ca53a4e538ca7294a5094631b5ab6adab5ad6d5ad6b5ad6d4ad6b5a56b6ad674ace74a5292a5294a4eb49ce949ce53a52949ce74a4a7494e729c6539ce539c653
def zv198 : ℕ := 0x129463084611a4e73a4e52952949ce529ca72a4a7294a3294a5194230ad6d5b5694ad294a56d4a5ab5a52b49ceb69d294ad293a4e73a4e939cab3a4a9294a51a52949ca74a4e549ca7394a5394a5194a31
def zv199 : ℕ := 0x129463084611a4e73a4e529d2949ce529ca72a4a7294a3294a5194230ad6d5b5694ad694a56d4adab5a52b5a4eb69d294ad293a4e73a4e939ceb3a4a9294e52a52949ca74a4e549ca7394a5394a5194a31
def zv200 : ℕ := 0x12946308c210a4e93a4e539ce939ca329ca739ce5194a528c6108c210a56d5ad295ad6b3a56d5ad695a56b5a52959d6939ce94a52739ce728ca939ca738ca529ce939ca5394a3294a318c6328ca5294631
def zv201 : ℕ := 0x12946308c211a4e93a4e539ce949ca329ca73a4e7294a528c63094231a56d5b5695ad6b3a56d5adab5a56b5a52969d694a4e94a52939ce7294ab3a4a9394e529ce949ca739ca3394a529463394e529ca52
def zv202 : ℕ := 0x12946308c610a4e93a4e539d2939ce539ca739ce5194a5294a318c210adad5ad295ad6b4ad6d5ad695a56b5a52b5a5693a5294a5273a529394e939ca738ca52a52939ca549ce539ce5294a528ca5294631
def zv203 : ℕ := 0x12946308c610a4e93a4e53a52939ce539ca739ce5194a5294a318c210adad5ad295adab4ad6d5b5695a56b6ad2b5a5693a5294a5273a5293952939ca738ce53a52939ca549ce539ce5294a528ca5294631
def zv204 : ℕ := 0x12946308c611a4e93a4e13952949ce539ca73a4e7294a5294a5194231adad5b5655ad2b2ad6d5a5ab5956b49cab6a5694ad294a5293a52939cab3a429384a11a52949ca74a4e549ce739ca5394e529ca52
def zv205 : ℕ := 0x12946308c611a4e93a4e338d2949ce539ca73a4e7294a5294a5194231adad5b5675aceb3ad6d59dab59d6b394eb6a5694ad294a5293a52939c6b3a46938c630a52949ca74a4e549ce739ca5394e529ca52
def zv206 : ℕ := 0x12946308c611a4e93a4e33952949ce539ca73a4e7294a5294a5194231adad5b5675ad2b3ad6d5a5ab59d6b49ceb6a5694ad294a5293a52939cab3a46938ca31a52949ca74a4e549ce739ca5394e529ca52
def zv207 : ℕ := 0x12946308c611a4e93a4e339d2949ce539ca73a4e7294a5294a5194231adad5b5675ad6b3ad6d5adab59d6b5a4eb6a5694ad294a5293a52939ceb3a46938ce32a52949ca74a4e549ce739ca5394e529ca52
def zv208 : ℕ := 0x12946308c611a4e93a4e529d2949ce539ca73a4e7294a5294a5194231adad5b5694ad6b4a56d4adab5a52b59ceb6a5694ad294a5293a52939ceb3a4a9394e52a52949ca74a4e549ce739ca5394e529ca32
def zv209 : ℕ := 0x12946308c611a4e93a4e53952949ce539ca73a4e7294a5294a5194231adad5b5695ad2b4ad6d5a5ab5a56b49d2b6a5694ad294a5293a52939cab3a4a9394a51a52949ca74a4e549ce739ca5394e529ca52
def zv210 : ℕ := 0x12946308c611a4e93a4e539d2949ce539ca73a4e7294a3294a5194231adad5b5695ad694ad6d5adab5a56b5a4eb69d694ad294a5293a52939ceb3a4a9294e51a52949ca74a4e549ce739ca5394e519ca51
def zv211 : ℕ := 0x12946308c611a4e93a4e539d2949ce539ca73a4e7294a5294a5194231adad5b5695ad6b4ad6d5adab5a56b5a52b6a5694ad294a5293a52939ceb3a4a9394e52a52949ca74a4e549ce739ca5394e529ca52
def zv212 : ℕ := 0x12946308c611a4e93a4e53a52949ce539ca73a4e7294a5294a5194231adad5b5695adab4ad6d5b5ab5a56b6ad2b6a5694ad294a5293a52939d2b3a4a9395253a52949ca74a4e549ce739ca5394e529ca52
def zv213 : ℕ := 0x129463184211a5273a527294e949ca519ca72a4a7394e528c63094630ad2d6b5ab4b52b49d6d4a5ad5ad2d49d2969d295a4e93a4e739ca739c6b4a4e939ca729ce949ce739ca53946528c6539ca7294a32
def zv214 : ℕ := 0x129463184611a5273a52718d2949ce729ca72a4a7394e5294a5194630b56d6b5ab3b4eb59d6d39dad5aced39ceb6a5295ad293a4e73a4e94a46b4a4e939c671a52949ce74a4e749ca7394a739ca7294a12
def zv215 : ℕ := 0x129463184611a5273a5272952949ce729ca72a4a7394e5294a5194630b56d6b5ab4b52b5a56d4a5ad5ad2d49d2b6a5295ad293a4e73a4e94a4ab4a4e939ca72a52949ce74a4e749ca7394a739ca7294a32
def zv216 : ℕ := 0x129463184611a5273a52729d2949ce729ca72a4a7394e5294a5194630b56d6b5ab4b56b5a56d4adad5ad2d5a52b6a5295ad293a4e73a4e94a4eb4a4e939ce73a52949ce74a4e749ca7394a739ca7294a32
def zv217 : ℕ := 0x12946318c210a5293a52739ce939ca529ca739ce5294e728c6108c610ad6d6ad6b5b56d4a56d5ad6b5ad6d5a5695a56949ce94a52739ce7394a949ce7494a739ce939ce5394a5294a318c65294a7394632
def zv218 : ℕ := 0x12946318c211a5293a52729ce949ca529ca73a4e7394e728c63094631ad6d6b5ab4b56d49d6d4adad5ad2d59d296a5695a4e94a52939ce739cab4a4e949ce739ce949ce739ca5394a52946539ce739ca33
def zv219 : ℕ := 0x12946318c211a5293a52738ce949c6529ca73a4e7394e728c63094631ad6d6b5ab5b4ed39d6d59dad5ad6d395676a5695a4e94a529394e539c2b4a4e949c6719ce949ce739ca5394a32942539ce739ca53
def zv220 : ℕ := 0x12946318c211a5293a527394e949c6529ca73a4e7394e728c63094631ad6d6b5ab5b52d39d6d5a5ad5ad6d49d676a5695a4e94a529394e539c6b4a4e949ca729ce949ce739ca5394a32942539ce739ca53
def zv221 : ℕ := 0x12946318c211a5293a527394e949ca529ca73a4e7394e728c63094631ad6d6b5ab5b52d4a56d5a5ad5ad6d49d696a5695a4e94a52939ce739c6b4a4e949ca729ce949ce739ca5394a52946539ce739ca53
def zv222 : ℕ := 0x12946318c211a5293a52739ce949ca529ca73a4e7394e728c63094631ad6d6b5ab5b56d4a56d5adad5ad6d5a5696a5695a4e94a52939ce739cab4a4e949ce739ce949ce739ca5394a52946539ce739ca53
def zv223 : ℕ := 0x12946318c211a5293a5273a4e949ca529ca73a4e7394e728c63094631ad6d6b5ab5b5ad4a56d5b5ad5ad6d6ad696a5695a4e94a52939ce739ceb4a4e949d2749ce949ce739ca5394a52946539ce739ca53
def zv224 : ℕ := 0x12946318c610a5293a52719d2939ce739ca739ce5294e7294a318c610b5ad6ad6b3b56d59d6d3ad6b5aced594eb5ad694a5294a5273a52949ce949ce7494a73a52939ce549ce739ce5294a7294a7394632
def zv225 : ℕ := 0x12946318c610a5293a5273952939ce739ca739ce5294e7294a318c610b5ad6ad6b5b52d5ad6d5a56b5ad6d4956b5ad694a5294a5273a52949ca949ce7494672a52939ce549ce739ce5294a7294a7394632
def zv226 : ℕ := 0x12946318c610a5293a5273952939ce739ca739ce5294e7294a318c610b5ad6ad6b5b52d5ad6d5a56b5ad6d49d6b5ad694a5294a5273a52949ca949ce7494672a52939ce549ce739ce5294a7294a7394632
def zv227 : ℕ := 0x12946318c610a5293a52739d2939ce739ca739ce5294e7294a318c610b5ad6ad6b5b56d5ad6d5ad6b5ad6d5956b5ad694a5294a5273a52949ce949ce7494a73a52939ce549ce739ce5294a7294a7394632
def zv228 : ℕ := 0x12946318c610a5293a52739d2939ce739ca739ce5294e7294a318c610b5ad6ad6b5b56d5ad6d5ad6b5ad6d5a56b5ad694a5294a5273a52949ce949ce7494a73a52939ce549ce739ce5294a7294a7394632
def zv229 : ℕ := 0x12946318c611a5293a5271952949ce739ca73a4e7394e7294a5194631b5ad6b5ab3b52d59d6d3a5ad5aced49ceb6ad695ad294a5293a5294a4ab4a4e949ca72a52949ce74a4e749ce739ca739ce739ca13
def zv230 : ℕ := 0x12946318c611a5293a52728d2949ce739ca73a4e7394e7294a5194631b5ad6b5ab4b4ed5a56d49dad5ad2d39d2b6ad695ad294a5293a5294a46b4a4e949c671a52949ce74a4e749ce739ca739ce739ca33
def zv231 : ℕ := 0x12946318c611a5293a5272952949ce739ca73a4e7394e7294a5194631b5ad6b5ab4b52d5a56d4a5ad5ad2d4a52b6ad695ad294a5293a5294a4ab4a4e949ca72a52949ce74a4e749ce739ca739ce739ca33
def zv232 : ℕ := 0x12946318c611a5293a5273952949ce739ca73a4e7394e7294a5194631b5ad6b5ab5b52d5ad6d5a5ad5ad6d49d6b6ad695ad294a5293a5294a4ab4a4e949ca72a52949ce74a4e749ce739ca739ce739ca53
def zv233 : ℕ := 0x12946318c611a5293a52739d2949ce739ca73a4e7394e7294a5194631b5ad6b5ab5b56d5ad6d5adad5ad6d5a56b6ad695ad294a5293a5294a4eb4a4e949ce73a52949ce74a4e749ce739ca739ce739ca53
def zv234 : ℕ := 0x1294a11846119d2749d29395294a52729ce52a4a5394a5294a5094650b56b6adad5ad2b6adab5a56d5b56b4a56d6a5294ace73ace73aceb4a4ab49d2b3a4a72a5294a4e94a4a7494a9294a549ca5294a52
def zv235 : ℕ := 0x1294a11846119d2749d2939d294a52729ce52a4a5394a5294a5094650b56b6adad5ad6b6adab5ad6d5b56b5ad6d6a5294ace73ace73aceb4a4eb49d2b3a4e73a5294a4e94a4a7494a9294a549ca5294a52
def zv236 : ℕ := 0x1294a3084211a4e74a4e7394e94a4e319ce72a4a729ca328c63094250a52d5b56b5ad294a5ad5a5ab6ad6b4a52b6952b4a4e93ace74a4a92946b3a4eb29ca719ce94a4a939ca33946728ca3494a5194e51
def zv237 : ℕ := 0x1294a3084611a4e74a4e738d294a52529ce72a4a729ca1294a5194250ad6d5b56b5ace75adad59dab6ad6b39ced6952b4ad293ace74aceb39c6b3a4eb19c671a5294a4a94a4e549ca9394e5494a5094e50
def zv238 : ℕ := 0x1294a3084611a4e74a4e7395294a52529ce72a4a729ca3294a5194250ad6d5b56b5ad295adad5a5ab6ad6b4a52d69d2b4ad293ace74aceb39cab3a4eb29ca71a5294a4a94a4e549ca9394e5494a5194e51
def zv239 : ℕ := 0x1294a3084611a4e74a4e739d294a52529ce72a4a729ca3294a5194250ad6d5b56b5ad695adad5adab6ad6b5ad2d69d2b4ad293ace74aceb39ceb3a4eb29ce72a5294a4a94a4e549ca9394e5494a5194e51
def zv240 : ℕ := 0x1294a308c210a4e94a4e749ce93a4e329ce739ce519ca528c6108c230a56d5ad2b6ad6b4adad6ad696adab5ad6b59d6b39ce94ad274a4e928ca939ce9394a729ce93a4a7394a3294a518ca338ca5294a51
def zv241 : ℕ := 0x1294a308c211a4e94a4e748ce94a4e129ce73a4e729ca528c630942519d6d5b56b6aceb3adad69dab6adab39d6b6956b4a4e94ad294a4e918c2b3a4eb39c6709ce94a4a939ca1394a7294a1494e529ce72
def zv242 : ℕ := 0x1294a308c211a4e94a4e7494e94a4e129ce73a4e729ca528c630942519d6d5b56b6ad2b3adad6a5ab6adab4a56b6956b4a4e94ad294a4e918c6b3a4eb39ca719ce94a4a939ca1394a7294a1494e529ce72
def zv243 : ℕ := 0x1294a308c211a4e94a4e749ce94a4e329ce73a4e729ca328c63094251a56d5b56b6ad694adad6adab6adab5ad2b6956b4a4e94ad294a4e9294ab3a4eb29ce719ce94a4a939ca3394a7294a3494e519ce71
def zv244 : ℕ := 0x1294a308c211a4e94a4e749ce94a4e329ce73a4e729ca528c63094251a56d5b56b6ad6b4adad6adab6adab5ad6b69d6b4a4e94ad294a4e9294ab3a4eb39ce729ce94a4a939ca3394a7294a3494e529ce72
def zv245 : ℕ := 0x1294a308c211a4e94a4e74a4e94a4e329ce73a4e729ca528c63094251a56d5b56b6adab4adad6b5ab6adab6b56b69d6b4a4e94ad294a4e9294eb3a4eb39d2739ce94a4a939ca3394a7294a3494e529ce72
def zv246 : ℕ := 0x1294a308c610a4e94a4e749d293a52539ce739ce519ca5294a318c230adad5ad2b6ad6b5b5ad6ad696adab5ad6d5a56b3a5294ad274ad2b394e939ce9394a72a5293a4a749ce539ce7294e538ca5294a51
def zv247 : ℕ := 0x1294a308c611a4e94a4e748d294a52539ce73a4e729ca3294a5194251adad5b56b6ace95b5ad69dab6adab39d2d69d6b4ad294ad294ad2b39c6b3a4eb29c671a5294a4a94a4e549ce939ce5494e519ce71
def zv248 : ℕ := 0x1294a308c611a4e94a4e7495294a52539ce73a4e729ca3294a5194251adad5b56b6ad295b5ad6a5ab6adab4a52d69d6b4ad294ad294ad2b39cab3a4eb29ca72a5294a4a94a4e549ce939ce5494e519ce71
def zv249 : ℕ := 0x1294a308c611a4e94a4e7495294a52539ce73a4e729ca5294a5194251adad5b56b6ad2b5b5ad6a5ab6adab4a56d6a56b4ad294ad294ad2b39cab3a4eb39ca71a5294a4a94a4e549ce939ce5494e529ce72
def zv250 : ℕ := 0x1294a308c611a4e94a4e749d294a52539ce73a4e729ca5294a5194251adad5b56b6ad6b5b5ad6adab6adab5ad6d6a56b4ad294ad294ad2b39ceb3a4eb39ce72a5294a4a94a4e549ce939ce5494e529ce72
def zv251 : ℕ := 0x1294a3184211a5274a529394e94a4e519ce72a4a739ce528c63094650ad2d6b5ad5b52b5a5ad5a5ad6b56d4a56b69d2b5a4e93ace74a4a939c6b4a52b3a4a929ce94a4e939ca53946728ca549ca7294e52
def zv252 : ℕ := 0x1294a3184211a5274a52939ce94a4e519ce72a4a739ce528c63094650ad2d6b5ad5b56b5a5ad5adad6b56d5ad6b69d2b5a4e93ace74a4a939cab4a52b3a4e939ce94a4e939ca53946728ca549ca7294e52
def zv253 : ℕ := 0x1294a318c210a5294a52949ce93a4e529ce739ce529ce728c6108c630ad6d6ad6d6b56d5adad6ad6b6b5ad5adab5a56b49ce94ad274a4e9394a949d2949ca939ce93a4e7394a5294a518ca5394a7394a52
def zv254 : ℕ := 0x1294a318c211a5294a52948ce94a4e519ce73a4e739ce728c63094651ad2d6b5ad6b4ed5a5ad69dad6b5ad39dab69d6b5a4e94ad294a4a939c6b4a52b4a46919ce94a4e939ca53946728ca549ce739ce73
def zv255 : ℕ := 0x1294a318c211a5294a529494e94a4e519ce73a4e739ce728c63094651ad2d6b5ad6b52d5a5ad6a5ad6b5ad4a5ab69d6b5a4e94ad294a4a939cab4a52b4a4a929ce94a4e939ca53946728ca549ce739ce73
def zv256 : ℕ := 0x1294a318c211a5294a52949ce94a4e529ce73a4e739ce728c63094651ad6d6b5ad6b56d5adad6adad6b5ad5adab6a56b5a4e94ad294a4e939cab4a52b4a4e939ce94a4e939ca5394a7294a549ce739ce73
def zv257 : ℕ := 0x1294a318c610a5294a529495293a52739ce739ce529ce7294a318c630b5ad6ad6d6b52d6b5ad6a56b6b5ad4a5ad5ad6b4a5294ad274ad2b49ca949d2949c692a5293a4e749ce739ce7294e7394a7394a52
def zv258 : ℕ := 0x1294a318c610a5294a52949d293a52739ce739ce529ce7294a318c630b5ad6ad6d6b56d6b5ad6ad6b6b5ad5adad5ad6b4a5294ad274ad2b49ce949d2949ca93a5293a4e749ce739ce7294e7394a7394a52
def s3_0 : Saved := (12, 0, zv14, [u97, u77, u66, u54, u33, u26, u21, u18, u11, u4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_0 : look gl gm gg 13 12 0 zv14 [u97, u77, u66, u54, u33, u26, u21, u18, u11, u4] = false := by decide +kernel
def s3_1 : Saved := (12, 0, zv56, [u99, u97, u77, u66, u54, u33, u26, u21, u20, u18])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_1 : look gl gm gg 13 12 0 zv56 [u99, u97, u77, u66, u54, u33, u26, u21, u20, u18] = false := by decide +kernel
def s3_2 : Saved := (12, 0, zv56, [u110, u97, u77, u66, u54, u33, u26, u21, u20, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_2 : look gl gm gg 13 12 0 zv56 [u110, u97, u77, u66, u54, u33, u26, u21, u20, u11] = false := by decide +kernel
def s3_3 : Saved := (12, 0, zv12, [u97, u77, u66, u54, u33, u26, u21, u20, u18, u11, u4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_3 : look gl gm gg 13 12 0 zv12 [u97, u77, u66, u54, u33, u26, u21, u20, u18, u11, u4] = false := by decide +kernel
def s3_4 : Saved := (12, 0, zv49, [u98, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_4 : look gl gm gg 13 12 0 zv49 [u98, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_5 : Saved := (12, 0, zv52, [u105, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_5 : look gl gm gg 13 12 0 zv52 [u105, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_6 : Saved := (12, 0, zv54, [u115, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_6 : look gl gm gg 13 12 0 zv54 [u115, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_7 : Saved := (12, 0, zv53, [u120, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_7 : look gl gm gg 13 12 0 zv53 [u120, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_8 : Saved := (12, 0, zv51, [u101, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_8 : look gl gm gg 13 12 0 zv51 [u101, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_9 : Saved := (12, 0, zv149, [u97, u77, u66, u54, u33, u28, u26, u21, u20, u18])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_9 : look gl gm gg 13 12 0 zv149 [u97, u77, u66, u54, u33, u28, u26, u21, u20, u18] = false := by decide +kernel
def s3_10 : Saved := (12, 0, zv157, [u97, u77, u66, u54, u38, u33, u26, u21, u20, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_10 : look gl gm gg 13 12 0 zv157 [u97, u77, u66, u54, u38, u33, u26, u21, u20, u11] = false := by decide +kernel
def s3_11 : Saved := (12, 0, zv162, [u97, u77, u67, u66, u54, u33, u26, u21, u20, u18])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_11 : look gl gm gg 13 12 0 zv162 [u97, u77, u67, u66, u54, u33, u26, u21, u20, u18] = false := by decide +kernel
def s3_12 : Saved := (12, 0, zv160, [u97, u79, u77, u66, u54, u33, u26, u21, u20, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_12 : look gl gm gg 13 12 0 zv160 [u97, u79, u77, u66, u54, u33, u26, u21, u20, u11] = false := by decide +kernel
def s3_13 : Saved := (12, 0, zv154, [u97, u77, u66, u58, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_13 : look gl gm gg 13 12 0 zv154 [u97, u77, u66, u58, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_14 : Saved := (12, 0, zv146, [u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_14 : look gl gm gg 13 12 0 zv146 [u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_15 : Saved := (12, 0, zv135, [u97, u77, u66, u56, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_15 : look gl gm gg 13 12 0 zv135 [u97, u77, u66, u56, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_16 : Saved := (12, 0, zv141, [u97, u77, u66, u57, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_16 : look gl gm gg 13 12 0 zv141 [u97, u77, u66, u57, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_17 : Saved := (12, 0, zv147, [u97, u77, u70, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_17 : look gl gm gg 13 12 0 zv147 [u97, u77, u70, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_18 : Saved := (12, 0, zv155, [u97, u82, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_18 : look gl gm gg 13 12 0 zv155 [u97, u82, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_19 : Saved := (12, 0, zv56, [u111, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_19 : look gl gm gg 13 12 0 zv56 [u111, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_20 : Saved := (12, 0, zv96, [u105, u97, u77, u66, u54, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_20 : look gl gm gg 13 12 0 zv96 [u105, u97, u77, u66, u54, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_21 : Saved := (12, 0, zv194, [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_21 : look gl gm gg 13 12 0 zv194 [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_22 : Saved := (12, 0, zv199, [u97, u77, u66, u57, u54, u38, u33, u26, u21, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_22 : look gl gm gg 13 12 0 zv199 [u97, u77, u66, u57, u54, u38, u33, u26, u21, u11] = false := by decide +kernel
def s3_23 : Saved := (12, 0, zv2, [u97, u77, u66, u54, u38, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_23 : look gl gm gg 13 12 0 zv2 [u97, u77, u66, u54, u38, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_24 : Saved := (12, 0, zv86, [u98, u97, u77, u66, u54, u38, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_24 : look gl gm gg 13 12 0 zv86 [u98, u97, u77, u66, u54, u38, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_25 : Saved := (12, 0, zv90, [u101, u97, u77, u66, u54, u38, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_25 : look gl gm gg 13 12 0 zv90 [u101, u97, u77, u66, u54, u38, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_26 : Saved := (12, 0, zv5, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_26 : look gl gm gg 13 12 0 zv5 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_27 : Saved := (12, 0, zv18, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_27 : look gl gm gg 13 12 0 zv18 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u0] = false := by decide +kernel
def s3_28 : Saved := (12, 0, zv172, [u97, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_28 : look gl gm gg 13 12 0 zv172 [u97, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_29 : Saved := (12, 0, zv171, [u97, u77, u66, u56, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_29 : look gl gm gg 13 12 0 zv171 [u97, u77, u66, u56, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_30 : Saved := (12, 0, zv1, [u97, u77, u66, u57, u54, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_30 : look gl gm gg 13 12 0 zv1 [u97, u77, u66, u57, u54, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_31 : Saved := (12, 0, zv24, [u97, u77, u66, u54, u53, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_31 : look gl gm gg 13 12 0 zv24 [u97, u77, u66, u54, u53, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_32 : Saved := (12, 0, zv94, [u101, u97, u77, u66, u57, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_32 : look gl gm gg 13 12 0 zv94 [u101, u97, u77, u66, u57, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_33 : Saved := (12, 0, zv85, [u98, u97, u77, u66, u57, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_33 : look gl gm gg 13 12 0 zv85 [u98, u97, u77, u66, u57, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_34 : Saved := (12, 0, zv191, [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_34 : look gl gm gg 13 12 0 zv191 [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_35 : Saved := (12, 0, zv90, [u105, u97, u77, u66, u57, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_35 : look gl gm gg 13 12 0 zv90 [u105, u97, u77, u66, u57, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_36 : Saved := (12, 0, zv145, [u97, u77, u66, u57, u54, u33, u28, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_36 : look gl gm gg 13 12 0 zv145 [u97, u77, u66, u57, u54, u33, u28, u26, u21, u18, u11] = false := by decide +kernel
def s3_37 : Saved := (12, 0, zv193, [u97, u77, u66, u59, u57, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_37 : look gl gm gg 13 12 0 zv193 [u97, u77, u66, u59, u57, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_38 : Saved := (12, 0, zv203, [u97, u77, u73, u66, u57, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_38 : look gl gm gg 13 12 0 zv203 [u97, u77, u73, u66, u57, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_39 : Saved := (12, 0, zv94, [u112, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_39 : look gl gm gg 13 12 0 zv94 [u112, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_40 : Saved := (12, 0, zv92, [u115, u97, u77, u66, u57, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_40 : look gl gm gg 13 12 0 zv92 [u115, u97, u77, u66, u57, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_41 : Saved := (12, 0, zv98, [u120, u97, u79, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_41 : look gl gm gg 13 12 0 zv98 [u120, u97, u79, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_42 : Saved := (12, 0, zv4, [u97, u77, u66, u59, u54, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_42 : look gl gm gg 13 12 0 zv4 [u97, u77, u66, u59, u54, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_43 : Saved := (12, 0, zv63, [u105, u99, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_43 : look gl gm gg 13 12 0 zv63 [u105, u99, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_44 : Saved := (12, 0, zv65, [u120, u99, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_44 : look gl gm gg 13 12 0 zv65 [u120, u99, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_45 : Saved := (12, 0, zv53, [u99, u97, u79, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_45 : look gl gm gg 13 12 0 zv53 [u99, u97, u79, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_46 : Saved := (12, 0, zv61, [u103, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_46 : look gl gm gg 13 12 0 zv61 [u103, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_47 : Saved := (12, 0, zv59, [u100, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_47 : look gl gm gg 13 12 0 zv59 [u100, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_48 : Saved := (12, 0, zv52, [u99, u97, u77, u66, u54, u38, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_48 : look gl gm gg 13 12 0 zv52 [u99, u97, u77, u66, u54, u38, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_49 : Saved := (12, 0, zv48, [u97, u77, u66, u54, u33, u26, u21, u18, u11, u6])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_49 : look gl gm gg 13 12 0 zv48 [u97, u77, u66, u54, u33, u26, u21, u18, u11, u6] = false := by decide +kernel
def s3_50 : Saved := (12, 0, zv67, [u117, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_50 : look gl gm gg 13 12 0 zv67 [u117, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_51 : Saved := (12, 0, zv74, [u97, u77, u66, u54, u33, u26, u21, u18, u11, u1])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_51 : look gl gm gg 13 12 0 zv74 [u97, u77, u66, u54, u33, u26, u21, u18, u11, u1] = false := by decide +kernel
def s3_52 : Saved := (12, 0, zv108, [u116, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_52 : look gl gm gg 13 12 0 zv108 [u116, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_53 : Saved := (12, 0, zv59, [u98, u97, u77, u66, u54, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_53 : look gl gm gg 13 12 0 zv59 [u98, u97, u77, u66, u54, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_54 : Saved := (12, 0, zv105, [u101, u98, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_54 : look gl gm gg 13 12 0 zv105 [u101, u98, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_55 : Saved := (12, 0, zv57, [u98, u97, u77, u66, u56, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_55 : look gl gm gg 13 12 0 zv57 [u98, u97, u77, u66, u56, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_56 : Saved := (12, 0, zv72, [u98, u97, u77, u66, u54, u33, u26, u21, u18, u11, u1])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_56 : look gl gm gg 13 12 0 zv72 [u98, u97, u77, u66, u54, u33, u26, u21, u18, u11, u1] = false := by decide +kernel
def s3_57 : Saved := (12, 0, zv88, [u110, u98, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_57 : look gl gm gg 13 12 0 zv88 [u110, u98, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_58 : Saved := (12, 0, zv106, [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_58 : look gl gm gg 13 12 0 zv106 [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_59 : Saved := (12, 0, zv38, [u97, u77, u66, u54, u33, u26, u21, u18, u11, u8])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_59 : look gl gm gg 13 12 0 zv38 [u97, u77, u66, u54, u33, u26, u21, u18, u11, u8] = false := by decide +kernel
def s3_60 : Saved := (12, 0, zv61, [u101, u97, u77, u66, u56, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_60 : look gl gm gg 13 12 0 zv61 [u101, u97, u77, u66, u56, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_61 : Saved := (12, 0, zv113, [u105, u101, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_61 : look gl gm gg 13 12 0 zv113 [u105, u101, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_62 : Saved := (12, 0, zv57, [u101, u97, u77, u66, u54, u33, u28, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_62 : look gl gm gg 13 12 0 zv57 [u101, u97, u77, u66, u54, u33, u28, u26, u21, u18, u11] = false := by decide +kernel
def s3_63 : Saved := (12, 0, zv103, [u101, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_63 : look gl gm gg 13 12 0 zv103 [u101, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_64 : Saved := (12, 0, zv105, [u102, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_64 : look gl gm gg 13 12 0 zv105 [u102, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_65 : Saved := (12, 0, zv121, [u122, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_65 : look gl gm gg 13 12 0 zv121 [u122, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_66 : Saved := (12, 0, zv169, [u97, u77, u66, u54, u48, u33, u28, u21, u20, u18])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_66 : look gl gm gg 13 12 0 zv169 [u97, u77, u66, u54, u48, u33, u28, u21, u20, u18] = false := by decide +kernel
def s3_67 : Saved := (12, 0, zv169, [u97, u77, u66, u54, u48, u38, u26, u21, u20, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_67 : look gl gm gg 13 12 0 zv169 [u97, u77, u66, u54, u48, u38, u26, u21, u20, u11] = false := by decide +kernel
def s3_68 : Saved := (12, 0, zv161, [u97, u77, u70, u66, u54, u48, u33, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_68 : look gl gm gg 13 12 0 zv161 [u97, u77, u70, u66, u54, u48, u33, u21, u20, u18, u11] = false := by decide +kernel
def s3_69 : Saved := (12, 0, zv159, [u97, u82, u77, u66, u54, u48, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_69 : look gl gm gg 13 12 0 zv159 [u97, u82, u77, u66, u54, u48, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_70 : Saved := (12, 0, zv161, [u97, u77, u67, u66, u54, u48, u33, u26, u21, u20, u18])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_70 : look gl gm gg 13 12 0 zv161 [u97, u77, u67, u66, u54, u48, u33, u26, u21, u20, u18] = false := by decide +kernel
def s3_71 : Saved := (12, 0, zv159, [u97, u79, u77, u66, u54, u48, u33, u26, u21, u20, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_71 : look gl gm gg 13 12 0 zv159 [u97, u79, u77, u66, u54, u48, u33, u26, u21, u20, u11] = false := by decide +kernel
def s3_72 : Saved := (12, 0, zv13, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_72 : look gl gm gg 13 12 0 zv13 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u4] = false := by decide +kernel
def s3_73 : Saved := (12, 0, zv153, [u97, u77, u66, u58, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_73 : look gl gm gg 13 12 0 zv153 [u97, u77, u66, u58, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_74 : Saved := (12, 0, zv55, [u106, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_74 : look gl gm gg 13 12 0 zv55 [u106, u97, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_75 : Saved := (12, 0, zv164, [u97, u77, u66, u54, u33, u26, u21, u18, u16, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_75 : look gl gm gg 13 12 0 zv164 [u97, u77, u66, u54, u33, u26, u21, u18, u16, u11] = false := by decide +kernel
def s3_76 : Saved := (12, 0, zv158, [u97, u92, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_76 : look gl gm gg 13 12 0 zv158 [u97, u92, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_77 : Saved := (12, 0, zv169, [u97, u77, u66, u54, u52, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_77 : look gl gm gg 13 12 0 zv169 [u97, u77, u66, u54, u52, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_78 : Saved := (12, 0, zv50, [u101, u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_78 : look gl gm gg 13 12 0 zv50 [u101, u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_79 : Saved := (12, 0, zv11, [u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11, u4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_79 : look gl gm gg 13 12 0 zv11 [u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11, u4] = false := by decide +kernel
def s3_80 : Saved := (12, 0, zv161, [u97, u77, u71, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_80 : look gl gm gg 13 12 0 zv161 [u97, u77, u71, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_81 : Saved := (12, 0, zv159, [u97, u89, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_81 : look gl gm gg 13 12 0 zv159 [u97, u89, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_82 : Saved := (12, 0, zv161, [u97, u77, u69, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_82 : look gl gm gg 13 12 0 zv161 [u97, u77, u69, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_83 : Saved := (12, 0, zv159, [u97, u81, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_83 : look gl gm gg 13 12 0 zv159 [u97, u81, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_84 : Saved := (12, 0, zv165, [u97, u77, u66, u54, u52, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_84 : look gl gm gg 13 12 0 zv165 [u97, u77, u66, u54, u52, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_85 : Saved := (12, 0, zv153, [u97, u77, u66, u59, u54, u48, u33, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_85 : look gl gm gg 13 12 0 zv153 [u97, u77, u66, u59, u54, u48, u33, u21, u20, u18, u11] = false := by decide +kernel
def s3_86 : Saved := (12, 0, zv153, [u97, u77, u66, u60, u54, u48, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_86 : look gl gm gg 13 12 0 zv153 [u97, u77, u66, u60, u54, u48, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_87 : Saved := (12, 0, zv139, [u97, u77, u66, u54, u48, u33, u28, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_87 : look gl gm gg 13 12 0 zv139 [u97, u77, u66, u54, u48, u33, u28, u21, u20, u18, u11] = false := by decide +kernel
def s3_88 : Saved := (12, 0, zv144, [u97, u77, u66, u54, u48, u38, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_88 : look gl gm gg 13 12 0 zv144 [u97, u77, u66, u54, u48, u38, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_89 : Saved := (12, 0, zv55, [u99, u97, u77, u66, u54, u48, u33, u26, u21, u20, u18])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_89 : look gl gm gg 13 12 0 zv55 [u99, u97, u77, u66, u54, u48, u33, u26, u21, u20, u18] = false := by decide +kernel
def s3_90 : Saved := (12, 0, zv55, [u110, u97, u77, u66, u54, u48, u33, u26, u21, u20, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_90 : look gl gm gg 13 12 0 zv55 [u110, u97, u77, u66, u54, u48, u33, u26, u21, u20, u11] = false := by decide +kernel
def s3_91 : Saved := (12, 0, zv148, [u97, u77, u66, u54, u48, u33, u28, u26, u21, u20, u18])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_91 : look gl gm gg 13 12 0 zv148 [u97, u77, u66, u54, u48, u33, u28, u26, u21, u20, u18] = false := by decide +kernel
def s3_92 : Saved := (12, 0, zv156, [u97, u77, u66, u54, u48, u38, u33, u26, u21, u20, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_92 : look gl gm gg 13 12 0 zv156 [u97, u77, u66, u54, u48, u38, u33, u26, u21, u20, u11] = false := by decide +kernel
def s3_93 : Saved := (12, 0, zv167, [u97, u77, u66, u54, u52, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_93 : look gl gm gg 13 12 0 zv167 [u97, u77, u66, u54, u52, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_94 : Saved := (12, 0, zv153, [u97, u77, u66, u63, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_94 : look gl gm gg 13 12 0 zv153 [u97, u77, u66, u63, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_95 : Saved := (12, 0, zv163, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u16, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_95 : look gl gm gg 13 12 0 zv163 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u16, u11] = false := by decide +kernel
def s3_96 : Saved := (12, 0, zv15, [u97, u77, u66, u54, u40, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_96 : look gl gm gg 13 12 0 zv15 [u97, u77, u66, u54, u40, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_97 : Saved := (12, 0, zv55, [u111, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_97 : look gl gm gg 13 12 0 zv55 [u111, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_98 : Saved := (12, 0, zv139, [u97, u77, u66, u54, u50, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_98 : look gl gm gg 13 12 0 zv139 [u97, u77, u66, u54, u50, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_99 : Saved := (12, 0, zv144, [u97, u77, u66, u54, u51, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_99 : look gl gm gg 13 12 0 zv144 [u97, u77, u66, u54, u51, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_100 : Saved := (12, 0, zv148, [u97, u77, u66, u54, u48, u33, u30, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_100 : look gl gm gg 13 12 0 zv148 [u97, u77, u66, u54, u48, u33, u30, u26, u21, u18, u11] = false := by decide +kernel
def s3_101 : Saved := (12, 0, zv156, [u97, u77, u66, u54, u48, u39, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_101 : look gl gm gg 13 12 0 zv156 [u97, u77, u66, u54, u48, u39, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_102 : Saved := (12, 0, zv151, [u97, u77, u73, u66, u54, u48, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_102 : look gl gm gg 13 12 0 zv151 [u97, u77, u73, u66, u54, u48, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_103 : Saved := (12, 0, zv150, [u97, u85, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_103 : look gl gm gg 13 12 0 zv150 [u97, u85, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s3_104 : Saved := (12, 0, zv196, [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_104 : look gl gm gg 13 12 0 zv196 [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_105 : Saved := (12, 0, zv132, [u97, u77, u66, u54, u33, u29, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_105 : look gl gm gg 13 12 0 zv132 [u97, u77, u66, u54, u33, u29, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_106 : Saved := (12, 0, zv192, [u97, u77, u66, u57, u54, u48, u33, u29, u26, u21, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_106 : look gl gm gg 13 12 0 zv192 [u97, u77, u66, u57, u54, u48, u33, u29, u26, u21, u11] = false := by decide +kernel
def s3_107 : Saved := (12, 0, zv87, [u98, u97, u77, u66, u54, u48, u33, u29, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_107 : look gl gm gg 13 12 0 zv87 [u98, u97, u77, u66, u54, u48, u33, u29, u21, u18, u11] = false := by decide +kernel
def s3_108 : Saved := (12, 0, zv148, [u97, u77, u66, u54, u48, u33, u29, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_108 : look gl gm gg 13 12 0 zv148 [u97, u77, u66, u54, u48, u33, u29, u28, u21, u18, u11] = false := by decide +kernel
def s3_109 : Saved := (12, 0, zv87, [u106, u97, u77, u66, u54, u33, u29, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_109 : look gl gm gg 13 12 0 zv87 [u106, u97, u77, u66, u54, u33, u29, u26, u21, u18, u11] = false := by decide +kernel
def s3_110 : Saved := (12, 0, zv169, [u97, u77, u66, u54, u48, u38, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_110 : look gl gm gg 13 12 0 zv169 [u97, u77, u66, u54, u48, u38, u28, u21, u18, u11] = false := by decide +kernel
def s3_111 : Saved := (12, 0, zv211, [u97, u77, u66, u57, u54, u48, u38, u26, u21, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_111 : look gl gm gg 13 12 0 zv211 [u97, u77, u66, u57, u54, u48, u38, u26, u21, u11] = false := by decide +kernel
def s3_112 : Saved := (12, 0, zv102, [u106, u97, u77, u66, u54, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_112 : look gl gm gg 13 12 0 zv102 [u106, u97, u77, u66, u54, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_113 : Saved := (12, 0, zv153, [u97, u77, u66, u56, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_113 : look gl gm gg 13 12 0 zv153 [u97, u77, u66, u56, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_114 : Saved := (12, 0, zv161, [u97, u77, u67, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_114 : look gl gm gg 13 12 0 zv161 [u97, u77, u67, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_115 : Saved := (12, 0, zv228, [u97, u77, u70, u66, u54, u48, u38, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_115 : look gl gm gg 13 12 0 zv228 [u97, u77, u70, u66, u54, u48, u38, u21, u18, u11] = false := by decide +kernel
def s3_116 : Saved := (12, 0, zv3, [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_116 : look gl gm gg 13 12 0 zv3 [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_117 : Saved := (12, 0, zv222, [u97, u83, u77, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_117 : look gl gm gg 13 12 0 zv222 [u97, u83, u77, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_118 : Saved := (12, 0, zv224, [u97, u77, u54, u48, u38, u26, u21, u18, u11, u2])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_118 : look gl gm gg 13 12 0 zv224 [u97, u77, u54, u48, u38, u26, u21, u18, u11, u2] = false := by decide +kernel
def s3_119 : Saved := (12, 0, zv211, [u97, u77, u66, u59, u54, u48, u38, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_119 : look gl gm gg 13 12 0 zv211 [u97, u77, u66, u59, u54, u48, u38, u21, u18, u11] = false := by decide +kernel
def s3_120 : Saved := (12, 0, zv93, [u101, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_120 : look gl gm gg 13 12 0 zv93 [u101, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_121 : Saved := (12, 0, zv231, [u97, u77, u66, u54, u34, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_121 : look gl gm gg 13 12 0 zv231 [u97, u77, u66, u54, u34, u26, u21, u18, u11] = false := by decide +kernel
def s3_122 : Saved := (12, 0, zv211, [u97, u77, u66, u61, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_122 : look gl gm gg 13 12 0 zv211 [u97, u77, u66, u61, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_123 : Saved := (12, 0, zv208, [u97, u77, u66, u61, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_123 : look gl gm gg 13 12 0 zv208 [u97, u77, u66, u61, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_124 : Saved := (12, 0, zv230, [u97, u77, u66, u54, u48, u34, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_124 : look gl gm gg 13 12 0 zv230 [u97, u77, u66, u54, u48, u34, u26, u21, u18, u11] = false := by decide +kernel
def s3_125 : Saved := (12, 0, zv228, [u97, u77, u71, u66, u54, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_125 : look gl gm gg 13 12 0 zv228 [u97, u77, u71, u66, u54, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_126 : Saved := (12, 0, zv202, [u97, u77, u73, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_126 : look gl gm gg 13 12 0 zv202 [u97, u77, u73, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_127 : Saved := (12, 0, zv100, [u113, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_127 : look gl gm gg 13 12 0 zv100 [u113, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_128 : Saved := (12, 0, zv228, [u97, u77, u68, u66, u54, u48, u38, u26, u21, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_128 : look gl gm gg 13 12 0 zv228 [u97, u77, u68, u66, u54, u48, u38, u26, u21, u11] = false := by decide +kernel
def s3_129 : Saved := (12, 0, zv218, [u97, u83, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_129 : look gl gm gg 13 12 0 zv218 [u97, u83, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_130 : Saved := (12, 0, zv137, [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_130 : look gl gm gg 13 12 0 zv137 [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_131 : Saved := (12, 0, zv101, [u106, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_131 : look gl gm gg 13 12 0 zv101 [u106, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_132 : Saved := (12, 0, zv87, [u98, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_132 : look gl gm gg 13 12 0 zv87 [u98, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_133 : Saved := (12, 0, zv217, [u97, u92, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_133 : look gl gm gg 13 12 0 zv217 [u97, u92, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_134 : Saved := (12, 0, zv229, [u97, u77, u66, u54, u38, u34, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_134 : look gl gm gg 13 12 0 zv229 [u97, u77, u66, u54, u38, u34, u26, u21, u18, u11] = false := by decide +kernel
def s3_135 : Saved := (12, 0, zv167, [u97, u77, u66, u54, u50, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_135 : look gl gm gg 13 12 0 zv167 [u97, u77, u66, u54, u50, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_136 : Saved := (12, 0, zv99, [u115, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_136 : look gl gm gg 13 12 0 zv99 [u115, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_137 : Saved := (12, 0, zv166, [u97, u77, u66, u54, u48, u39, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_137 : look gl gm gg 13 12 0 zv166 [u97, u77, u66, u54, u48, u39, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_138 : Saved := (12, 0, zv148, [u97, u77, u66, u54, u48, u38, u28, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_138 : look gl gm gg 13 12 0 zv148 [u97, u77, u66, u54, u48, u38, u28, u26, u21, u18, u11] = false := by decide +kernel
def s3_139 : Saved := (12, 0, zv201, [u97, u85, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_139 : look gl gm gg 13 12 0 zv201 [u97, u85, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_140 : Saved := (12, 0, zv186, [u97, u77, u66, u57, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_140 : look gl gm gg 13 12 0 zv186 [u97, u77, u66, u57, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_141 : Saved := (12, 0, zv195, [u97, u77, u70, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_141 : look gl gm gg 13 12 0 zv195 [u97, u77, u70, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_142 : Saved := (12, 0, zv226, [u97, u77, u71, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_142 : look gl gm gg 13 12 0 zv226 [u97, u77, u71, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_143 : Saved := (12, 0, zv95, [u105, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_143 : look gl gm gg 13 12 0 zv95 [u105, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_144 : Saved := (12, 0, zv214, [u97, u77, u66, u54, u34, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_144 : look gl gm gg 13 12 0 zv214 [u97, u77, u66, u54, u34, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_145 : Saved := (12, 0, zv156, [u97, u77, u66, u54, u48, u38, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_145 : look gl gm gg 13 12 0 zv156 [u97, u77, u66, u54, u48, u38, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_146 : Saved := (12, 0, zv198, [u97, u77, u66, u57, u54, u48, u38, u33, u26, u21, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_146 : look gl gm gg 13 12 0 zv198 [u97, u77, u66, u57, u54, u48, u38, u33, u26, u21, u11] = false := by decide +kernel
def s3_147 : Saved := (12, 0, zv136, [u97, u77, u66, u54, u38, u33, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_147 : look gl gm gg 13 12 0 zv136 [u97, u77, u66, u54, u38, u33, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_148 : Saved := (12, 0, zv213, [u97, u82, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_148 : look gl gm gg 13 12 0 zv213 [u97, u82, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_149 : Saved := (12, 0, zv198, [u97, u77, u66, u60, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_149 : look gl gm gg 13 12 0 zv198 [u97, u77, u66, u60, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_150 : Saved := (12, 0, zv95, [u113, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_150 : look gl gm gg 13 12 0 zv95 [u113, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_151 : Saved := (12, 0, zv215, [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_151 : look gl gm gg 13 12 0 zv215 [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_152 : Saved := (12, 0, zv95, [u106, u97, u77, u66, u54, u38, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_152 : look gl gm gg 13 12 0 zv95 [u106, u97, u77, u66, u54, u38, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_153 : Saved := (12, 0, zv156, [u97, u77, u66, u54, u50, u38, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_153 : look gl gm gg 13 12 0 zv156 [u97, u77, u66, u54, u50, u38, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_154 : Saved := (12, 0, zv198, [u97, u77, u66, u59, u54, u48, u38, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_154 : look gl gm gg 13 12 0 zv198 [u97, u77, u66, u59, u54, u48, u38, u33, u21, u18, u11] = false := by decide +kernel
def s3_155 : Saved := (12, 0, zv140, [u97, u77, u66, u56, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_155 : look gl gm gg 13 12 0 zv140 [u97, u77, u66, u56, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s3_156 : Saved := (12, 0, zv190, [u97, u77, u66, u54, u33, u26, u23, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_156 : look gl gm gg 13 12 0 zv190 [u97, u77, u66, u54, u33, u26, u23, u18, u11] = false := by decide +kernel
def s3_157 : Saved := (12, 0, zv77, [u105, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_157 : look gl gm gg 13 12 0 zv77 [u105, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s3_158 : Saved := (12, 0, zv76, [u101, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_158 : look gl gm gg 13 12 0 zv76 [u101, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s3_159 : Saved := (12, 0, zv190, [u97, u78, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_159 : look gl gm gg 13 12 0 zv190 [u97, u78, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_160 : Saved := (12, 0, zv143, [u97, u77, u66, u54, u33, u26, u21, u18, u17, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_160 : look gl gm gg 13 12 0 zv143 [u97, u77, u66, u54, u33, u26, u21, u18, u17, u11] = false := by decide +kernel
def s3_161 : Saved := (12, 0, zv187, [u97, u77, u66, u54, u34, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_161 : look gl gm gg 13 12 0 zv187 [u97, u77, u66, u54, u34, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_162 : Saved := (12, 0, zv190, [u97, u77, u66, u54, u34, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_162 : look gl gm gg 13 12 0 zv190 [u97, u77, u66, u54, u34, u26, u21, u18, u11] = false := by decide +kernel
def s3_163 : Saved := (12, 0, zv46, [u99, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_163 : look gl gm gg 13 12 0 zv46 [u99, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s3_164 : Saved := (12, 0, zv81, [u104, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_164 : look gl gm gg 13 12 0 zv81 [u104, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_165 : Saved := (12, 0, zv142, [u97, u77, u66, u54, u48, u33, u28, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_165 : look gl gm gg 13 12 0 zv142 [u97, u77, u66, u54, u48, u33, u28, u21, u18, u13, u11] = false := by decide +kernel
def s3_166 : Saved := (12, 0, zv189, [u97, u77, u66, u54, u48, u33, u26, u23, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_166 : look gl gm gg 13 12 0 zv189 [u97, u77, u66, u54, u48, u33, u26, u23, u18, u11] = false := by decide +kernel
def s3_167 : Saved := (12, 0, zv189, [u97, u78, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_167 : look gl gm gg 13 12 0 zv189 [u97, u78, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_168 : Saved := (12, 0, zv189, [u97, u77, u66, u54, u48, u34, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_168 : look gl gm gg 13 12 0 zv189 [u97, u77, u66, u54, u48, u34, u26, u21, u18, u11] = false := by decide +kernel
def s3_169 : Saved := (12, 0, zv79, [u106, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_169 : look gl gm gg 13 12 0 zv79 [u106, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s3_170 : Saved := (12, 0, zv188, [u97, u82, u77, u66, u54, u48, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_170 : look gl gm gg 13 12 0 zv188 [u97, u82, u77, u66, u54, u48, u26, u21, u18, u13, u11] = false := by decide +kernel
def s3_171 : Saved := (12, 0, zv211, [u97, u77, u66, u57, u54, u51, u33, u26, u21, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_171 : look gl gm gg 13 12 0 zv211 [u97, u77, u66, u57, u54, u51, u33, u26, u21, u11] = false := by decide +kernel
def s3_172 : Saved := (12, 0, zv3, [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_172 : look gl gm gg 13 12 0 zv3 [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_173 : Saved := (12, 0, zv211, [u97, u77, u66, u65, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_173 : look gl gm gg 13 12 0 zv211 [u97, u77, u66, u65, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_174 : Saved := (12, 0, zv228, [u97, u77, u70, u66, u54, u51, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_174 : look gl gm gg 13 12 0 zv228 [u97, u77, u70, u66, u54, u51, u33, u21, u18, u11] = false := by decide +kernel
def s3_175 : Saved := (12, 0, zv102, [u114, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_175 : look gl gm gg 13 12 0 zv102 [u114, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_176 : Saved := (12, 0, zv153, [u97, u77, u66, u56, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_176 : look gl gm gg 13 12 0 zv153 [u97, u77, u66, u56, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_177 : Saved := (12, 0, zv93, [u101, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_177 : look gl gm gg 13 12 0 zv93 [u101, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_178 : Saved := (12, 0, zv27, [u97, u77, u66, u54, u42, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_178 : look gl gm gg 13 12 0 zv27 [u97, u77, u66, u54, u42, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_179 : Saved := (12, 0, zv87, [u98, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_179 : look gl gm gg 13 12 0 zv87 [u98, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_180 : Saved := (12, 0, zv168, [u97, u77, u66, u54, u52, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_180 : look gl gm gg 13 12 0 zv168 [u97, u77, u66, u54, u52, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_181 : Saved := (12, 0, zv222, [u97, u90, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_181 : look gl gm gg 13 12 0 zv222 [u97, u90, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_182 : Saved := (12, 0, zv55, [u99, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_182 : look gl gm gg 13 12 0 zv55 [u99, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_183 : Saved := (12, 0, zv201, [u97, u85, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_183 : look gl gm gg 13 12 0 zv201 [u97, u85, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_184 : Saved := (12, 0, zv95, [u105, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_184 : look gl gm gg 13 12 0 zv95 [u105, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_185 : Saved := (12, 0, zv97, [u120, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_185 : look gl gm gg 13 12 0 zv97 [u120, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_186 : Saved := (12, 0, zv148, [u97, u77, u66, u54, u51, u33, u28, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_186 : look gl gm gg 13 12 0 zv148 [u97, u77, u66, u54, u51, u33, u28, u26, u21, u18, u11] = false := by decide +kernel
def s3_187 : Saved := (12, 0, zv227, [u97, u77, u54, u51, u33, u26, u25, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_187 : look gl gm gg 13 12 0 zv227 [u97, u77, u54, u51, u33, u26, u25, u21, u18, u11] = false := by decide +kernel
def s3_188 : Saved := (12, 0, zv192, [u97, u77, u66, u59, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_188 : look gl gm gg 13 12 0 zv192 [u97, u77, u66, u59, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_189 : Saved := (12, 0, zv202, [u97, u77, u73, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_189 : look gl gm gg 13 12 0 zv202 [u97, u77, u73, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_190 : Saved := (12, 0, zv138, [u97, u77, u66, u54, u33, u26, u21, u18, u11, u10])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_190 : look gl gm gg 13 12 0 zv138 [u97, u77, u66, u54, u33, u26, u21, u18, u11, u10] = false := by decide +kernel
def s3_191 : Saved := (12, 0, zv167, [u97, u77, u66, u54, u51, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_191 : look gl gm gg 13 12 0 zv167 [u97, u77, u66, u54, u51, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_192 : Saved := (12, 0, zv225, [u97, u77, u54, u48, u33, u26, u25, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_192 : look gl gm gg 13 12 0 zv225 [u97, u77, u54, u48, u33, u26, u25, u21, u18, u11] = false := by decide +kernel
def s3_193 : Saved := (12, 0, zv101, [u106, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_193 : look gl gm gg 13 12 0 zv101 [u106, u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_194 : Saved := (12, 0, zv167, [u97, u77, u66, u54, u51, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_194 : look gl gm gg 13 12 0 zv167 [u97, u77, u66, u54, u51, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_195 : Saved := (12, 0, zv221, [u97, u82, u77, u66, u54, u51, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_195 : look gl gm gg 13 12 0 zv221 [u97, u82, u77, u66, u54, u51, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_196 : Saved := (12, 0, zv209, [u97, u77, u66, u59, u54, u51, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_196 : look gl gm gg 13 12 0 zv209 [u97, u77, u66, u59, u54, u51, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_197 : Saved := (12, 0, zv226, [u97, u77, u70, u66, u54, u51, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_197 : look gl gm gg 13 12 0 zv226 [u97, u77, u70, u66, u54, u51, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_198 : Saved := (12, 0, zv209, [u97, u77, u66, u57, u54, u51, u48, u33, u26, u21, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_198 : look gl gm gg 13 12 0 zv209 [u97, u77, u66, u57, u54, u51, u48, u33, u26, u21, u11] = false := by decide +kernel
def s3_199 : Saved := (12, 0, zv209, [u97, u77, u66, u60, u54, u51, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_199 : look gl gm gg 13 12 0 zv209 [u97, u77, u66, u60, u54, u51, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_200 : Saved := (12, 0, zv137, [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_200 : look gl gm gg 13 12 0 zv137 [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_201 : Saved := (12, 0, zv221, [u97, u89, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_201 : look gl gm gg 13 12 0 zv221 [u97, u89, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_202 : Saved := (12, 0, zv206, [u97, u77, u66, u54, u33, u26, u21, u18, u14, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_202 : look gl gm gg 13 12 0 zv206 [u97, u77, u66, u54, u33, u26, u21, u18, u14, u11] = false := by decide +kernel
def s3_203 : Saved := (12, 0, zv153, [u97, u77, u66, u57, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_203 : look gl gm gg 13 12 0 zv153 [u97, u77, u66, u57, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_204 : Saved := (12, 0, zv211, [u97, u77, u66, u59, u57, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_204 : look gl gm gg 13 12 0 zv211 [u97, u77, u66, u59, u57, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_205 : Saved := (12, 0, zv93, [u101, u97, u77, u66, u57, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_205 : look gl gm gg 13 12 0 zv93 [u101, u97, u77, u66, u57, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_206 : Saved := (12, 0, zv93, [u106, u97, u77, u66, u57, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_206 : look gl gm gg 13 12 0 zv93 [u106, u97, u77, u66, u57, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_207 : Saved := (12, 0, zv0, [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_207 : look gl gm gg 13 12 0 zv0 [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_208 : Saved := (12, 0, zv201, [u97, u86, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_208 : look gl gm gg 13 12 0 zv201 [u97, u86, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_209 : Saved := (12, 0, zv23, [u97, u77, u66, u54, u53, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_209 : look gl gm gg 13 12 0 zv23 [u97, u77, u66, u54, u53, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_210 : Saved := (12, 0, zv134, [u97, u77, u66, u57, u54, u33, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_210 : look gl gm gg 13 12 0 zv134 [u97, u77, u66, u57, u54, u33, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_211 : Saved := (12, 0, zv202, [u97, u77, u70, u66, u57, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_211 : look gl gm gg 13 12 0 zv202 [u97, u77, u70, u66, u57, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_212 : Saved := (12, 0, zv201, [u97, u82, u77, u66, u57, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_212 : look gl gm gg 13 12 0 zv201 [u97, u82, u77, u66, u57, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_213 : Saved := (12, 0, zv202, [u97, u77, u73, u66, u57, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_213 : look gl gm gg 13 12 0 zv202 [u97, u77, u73, u66, u57, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_214 : Saved := (12, 0, zv153, [u97, u77, u66, u57, u54, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_214 : look gl gm gg 13 12 0 zv153 [u97, u77, u66, u57, u54, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_215 : Saved := (12, 0, zv207, [u97, u77, u66, u61, u57, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_215 : look gl gm gg 13 12 0 zv207 [u97, u77, u66, u61, u57, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_216 : Saved := (12, 0, zv202, [u97, u77, u74, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_216 : look gl gm gg 13 12 0 zv202 [u97, u77, u74, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_217 : Saved := (12, 0, zv205, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u14, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_217 : look gl gm gg 13 12 0 zv205 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u14, u11] = false := by decide +kernel
def s3_218 : Saved := (12, 0, zv192, [u97, u77, u66, u59, u57, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_218 : look gl gm gg 13 12 0 zv192 [u97, u77, u66, u59, u57, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_219 : Saved := (12, 0, zv201, [u97, u89, u77, u66, u57, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_219 : look gl gm gg 13 12 0 zv201 [u97, u89, u77, u66, u57, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_220 : Saved := (12, 0, zv84, [u98, u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_220 : look gl gm gg 13 12 0 zv84 [u98, u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_221 : Saved := (12, 0, zv93, [u112, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_221 : look gl gm gg 13 12 0 zv93 [u112, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_222 : Saved := (12, 0, zv133, [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_222 : look gl gm gg 13 12 0 zv133 [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_223 : Saved := (12, 0, zv202, [u97, u77, u71, u66, u57, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_223 : look gl gm gg 13 12 0 zv202 [u97, u77, u71, u66, u57, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_224 : Saved := (12, 0, zv25, [u97, u77, u66, u57, u54, u40, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_224 : look gl gm gg 13 12 0 zv25 [u97, u77, u66, u57, u54, u40, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_225 : Saved := (12, 0, zv204, [u97, u77, u66, u57, u54, u33, u26, u21, u18, u14, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_225 : look gl gm gg 13 12 0 zv204 [u97, u77, u66, u57, u54, u33, u26, u21, u18, u14, u11] = false := by decide +kernel
def s3_226 : Saved := (12, 0, zv22, [u97, u77, u66, u57, u54, u53, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_226 : look gl gm gg 13 12 0 zv22 [u97, u77, u66, u57, u54, u53, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_227 : Saved := (12, 0, zv198, [u97, u77, u66, u61, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_227 : look gl gm gg 13 12 0 zv198 [u97, u77, u66, u61, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_228 : Saved := (12, 0, zv151, [u97, u77, u67, u66, u57, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_228 : look gl gm gg 13 12 0 zv151 [u97, u77, u67, u66, u57, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_229 : Saved := (12, 0, zv209, [u97, u77, u66, u65, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_229 : look gl gm gg 13 12 0 zv209 [u97, u77, u66, u65, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_230 : Saved := (12, 0, zv186, [u97, u77, u66, u57, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_230 : look gl gm gg 13 12 0 zv186 [u97, u77, u66, u57, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_231 : Saved := (12, 0, zv91, [u115, u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_231 : look gl gm gg 13 12 0 zv91 [u115, u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_232 : Saved := (12, 0, zv50, [u99, u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_232 : look gl gm gg 13 12 0 zv50 [u99, u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_233 : Saved := (12, 0, zv152, [u97, u77, u66, u57, u54, u50, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_233 : look gl gm gg 13 12 0 zv152 [u97, u77, u66, u57, u54, u50, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_234 : Saved := (12, 0, zv89, [u105, u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_234 : look gl gm gg 13 12 0 zv89 [u105, u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_235 : Saved := (12, 0, zv178, [u97, u77, u66, u60, u54, u48, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_235 : look gl gm gg 13 12 0 zv178 [u97, u77, u66, u60, u54, u48, u28, u21, u18, u11] = false := by decide +kernel
def s3_236 : Saved := (12, 0, zv178, [u97, u77, u66, u60, u56, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_236 : look gl gm gg 13 12 0 zv178 [u97, u77, u66, u60, u56, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_237 : Saved := (12, 0, zv246, [u97, u77, u70, u66, u60, u54, u48, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_237 : look gl gm gg 13 12 0 zv246 [u97, u77, u70, u66, u60, u54, u48, u21, u18, u11] = false := by decide +kernel
def s3_238 : Saved := (12, 0, zv246, [u97, u77, u73, u66, u60, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_238 : look gl gm gg 13 12 0 zv246 [u97, u77, u73, u66, u60, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_239 : Saved := (12, 0, zv248, [u97, u77, u66, u54, u35, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_239 : look gl gm gg 13 12 0 zv248 [u97, u77, u66, u54, u35, u26, u21, u18, u11] = false := by decide +kernel
def s3_240 : Saved := (12, 0, zv247, [u97, u77, u66, u54, u48, u35, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_240 : look gl gm gg 13 12 0 zv247 [u97, u77, u66, u54, u48, u35, u26, u21, u18, u11] = false := by decide +kernel
def s3_241 : Saved := (12, 0, zv176, [u97, u77, u67, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_241 : look gl gm gg 13 12 0 zv176 [u97, u77, u67, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_242 : Saved := (12, 0, zv20, [u97, u77, u66, u60, u54, u48, u26, u21, u18, u11, u0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_242 : look gl gm gg 13 12 0 zv20 [u97, u77, u66, u60, u54, u48, u26, u21, u18, u11, u0] = false := by decide +kernel
def s3_243 : Saved := (12, 0, zv7, [u97, u77, u66, u60, u54, u48, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_243 : look gl gm gg 13 12 0 zv7 [u97, u77, u66, u60, u54, u48, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_244 : Saved := (12, 0, zv244, [u97, u88, u77, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_244 : look gl gm gg 13 12 0 zv244 [u97, u88, u77, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_245 : Saved := (12, 0, zv177, [u97, u77, u66, u60, u54, u50, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_245 : look gl gm gg 13 12 0 zv177 [u97, u77, u66, u60, u54, u50, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_246 : Saved := (12, 0, zv117, [u106, u97, u77, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_246 : look gl gm gg 13 12 0 zv117 [u106, u97, u77, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_247 : Saved := (12, 0, zv210, [u97, u77, u66, u61, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_247 : look gl gm gg 13 12 0 zv210 [u97, u77, u66, u61, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_248 : Saved := (12, 0, zv201, [u97, u79, u77, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_248 : look gl gm gg 13 12 0 zv201 [u97, u79, u77, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_249 : Saved := (12, 0, zv104, [u98, u97, u77, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_249 : look gl gm gg 13 12 0 zv104 [u98, u97, u77, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_250 : Saved := (12, 0, zv243, [u97, u88, u77, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_250 : look gl gm gg 13 12 0 zv243 [u97, u88, u77, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_251 : Saved := (12, 0, zv115, [u115, u97, u77, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_251 : look gl gm gg 13 12 0 zv115 [u115, u97, u77, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_252 : Saved := (12, 0, zv237, [u97, u77, u66, u54, u35, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_252 : look gl gm gg 13 12 0 zv237 [u97, u77, u66, u54, u35, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_253 : Saved := (12, 0, zv112, [u105, u97, u77, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_253 : look gl gm gg 13 12 0 zv112 [u105, u97, u77, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_254 : Saved := (12, 0, zv173, [u97, u77, u66, u60, u56, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_254 : look gl gm gg 13 12 0 zv173 [u97, u77, u66, u60, u56, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_255 : Saved := (12, 0, zv173, [u97, u77, u66, u60, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_255 : look gl gm gg 13 12 0 zv173 [u97, u77, u66, u60, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_256 : Saved := (12, 0, zv112, [u108, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_256 : look gl gm gg 13 12 0 zv112 [u108, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_257 : Saved := (12, 0, zv173, [u97, u77, u66, u60, u54, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_257 : look gl gm gg 13 12 0 zv173 [u97, u77, u66, u60, u54, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_258 : Saved := (12, 0, zv238, [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_258 : look gl gm gg 13 12 0 zv238 [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_259 : Saved := (12, 0, zv178, [u97, u77, u66, u64, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_259 : look gl gm gg 13 12 0 zv178 [u97, u77, u66, u64, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_260 : Saved := (12, 0, zv118, [u109, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_260 : look gl gm gg 13 12 0 zv118 [u109, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_261 : Saved := (12, 0, zv7, [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_261 : look gl gm gg 13 12 0 zv7 [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_262 : Saved := (12, 0, zv20, [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11, u0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_262 : look gl gm gg 13 12 0 zv20 [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11, u0] = false := by decide +kernel
def s3_263 : Saved := (12, 0, zv246, [u97, u77, u75, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_263 : look gl gm gg 13 12 0 zv246 [u97, u77, u75, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_264 : Saved := (12, 0, zv244, [u97, u91, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_264 : look gl gm gg 13 12 0 zv244 [u97, u91, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_265 : Saved := (12, 0, zv31, [u97, u77, u66, u62, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_265 : look gl gm gg 13 12 0 zv31 [u97, u77, u66, u62, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_266 : Saved := (12, 0, zv60, [u99, u97, u77, u66, u63, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_266 : look gl gm gg 13 12 0 zv60 [u99, u97, u77, u66, u63, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_267 : Saved := (12, 0, zv129, [u119, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_267 : look gl gm gg 13 12 0 zv129 [u119, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_268 : Saved := (12, 0, zv184, [u97, u77, u71, u67, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_268 : look gl gm gg 13 12 0 zv184 [u97, u77, u71, u67, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_269 : Saved := (12, 0, zv246, [u97, u77, u73, u71, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_269 : look gl gm gg 13 12 0 zv246 [u97, u77, u73, u71, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_270 : Saved := (12, 0, zv8, [u97, u77, u71, u66, u54, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_270 : look gl gm gg 13 12 0 zv8 [u97, u77, u71, u66, u54, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_271 : Saved := (12, 0, zv217, [u97, u79, u77, u71, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_271 : look gl gm gg 13 12 0 zv217 [u97, u79, u77, u71, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_272 : Saved := (12, 0, zv253, [u97, u96, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_272 : look gl gm gg 13 12 0 zv253 [u97, u96, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_273 : Saved := (12, 0, zv176, [u97, u77, u71, u66, u56, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_273 : look gl gm gg 13 12 0 zv176 [u97, u77, u71, u66, u56, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_274 : Saved := (12, 0, zv184, [u97, u77, u72, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_274 : look gl gm gg 13 12 0 zv184 [u97, u77, u72, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_275 : Saved := (12, 0, zv127, [u119, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_275 : look gl gm gg 13 12 0 zv127 [u119, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_276 : Saved := (12, 0, zv127, [u106, u97, u77, u71, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_276 : look gl gm gg 13 12 0 zv127 [u106, u97, u77, u71, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_277 : Saved := (12, 0, zv183, [u97, u77, u71, u66, u54, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_277 : look gl gm gg 13 12 0 zv183 [u97, u77, u71, u66, u54, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_278 : Saved := (12, 0, zv181, [u97, u82, u80, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_278 : look gl gm gg 13 12 0 zv181 [u97, u82, u80, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_279 : Saved := (12, 0, zv181, [u97, u80, u77, u66, u54, u48, u33, u28, u21, u18])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_279 : look gl gm gg 13 12 0 zv181 [u97, u80, u77, u66, u54, u48, u33, u28, u21, u18] = false := by decide +kernel
def s3_280 : Saved := (12, 0, zv180, [u97, u80, u77, u70, u66, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_280 : look gl gm gg 13 12 0 zv180 [u97, u80, u77, u70, u66, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_281 : Saved := (12, 0, zv180, [u97, u94, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_281 : look gl gm gg 13 12 0 zv180 [u97, u94, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_282 : Saved := (12, 0, zv175, [u97, u87, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_282 : look gl gm gg 13 12 0 zv175 [u97, u87, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_283 : Saved := (12, 0, zv217, [u97, u79, u77, u70, u66, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_283 : look gl gm gg 13 12 0 zv217 [u97, u79, u77, u70, u66, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_284 : Saved := (12, 0, zv159, [u97, u79, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_284 : look gl gm gg 13 12 0 zv159 [u97, u79, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_285 : Saved := (12, 0, zv222, [u97, u82, u79, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_285 : look gl gm gg 13 12 0 zv222 [u97, u82, u79, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_286 : Saved := (12, 0, zv158, [u97, u79, u77, u67, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_286 : look gl gm gg 13 12 0 zv158 [u97, u79, u77, u67, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_287 : Saved := (12, 0, zv201, [u97, u79, u77, u66, u59, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_287 : look gl gm gg 13 12 0 zv201 [u97, u79, u77, u66, u59, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_288 : Saved := (12, 0, zv217, [u97, u92, u79, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_288 : look gl gm gg 13 12 0 zv217 [u97, u92, u79, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_289 : Saved := (12, 0, zv222, [u97, u89, u79, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_289 : look gl gm gg 13 12 0 zv222 [u97, u89, u79, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_290 : Saved := (12, 0, zv97, [u120, u97, u79, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_290 : look gl gm gg 13 12 0 zv97 [u120, u97, u79, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_291 : Saved := (12, 0, zv217, [u97, u93, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_291 : look gl gm gg 13 12 0 zv217 [u97, u93, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_292 : Saved := (12, 0, zv220, [u97, u77, u66, u54, u33, u32, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_292 : look gl gm gg 13 12 0 zv220 [u97, u77, u66, u54, u33, u32, u26, u21, u18, u11] = false := by decide +kernel
def s3_293 : Saved := (12, 0, zv97, [u106, u97, u79, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_293 : look gl gm gg 13 12 0 zv97 [u106, u97, u79, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_294 : Saved := (12, 0, zv219, [u97, u77, u66, u54, u48, u33, u32, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_294 : look gl gm gg 13 12 0 zv219 [u97, u77, u66, u54, u48, u33, u32, u26, u21, u18, u11] = false := by decide +kernel
def s3_295 : Saved := (12, 0, zv200, [u97, u79, u77, u73, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_295 : look gl gm gg 13 12 0 zv200 [u97, u79, u77, u73, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_296 : Saved := (12, 0, zv213, [u97, u82, u79, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_296 : look gl gm gg 13 12 0 zv213 [u97, u82, u79, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_297 : Saved := (12, 0, zv26, [u97, u77, u76, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_297 : look gl gm gg 13 12 0 zv26 [u97, u77, u76, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_298 : Saved := (12, 0, zv159, [u97, u79, u77, u66, u54, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_298 : look gl gm gg 13 12 0 zv159 [u97, u79, u77, u66, u54, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_299 : Saved := (12, 0, zv253, [u97, u82, u77, u70, u66, u54, u48, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_299 : look gl gm gg 13 12 0 zv253 [u97, u82, u77, u70, u66, u54, u48, u21, u18, u11] = false := by decide +kernel
def s3_300 : Saved := (12, 0, zv180, [u97, u82, u77, u67, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_300 : look gl gm gg 13 12 0 zv180 [u97, u82, u77, u67, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_301 : Saved := (12, 0, zv181, [u97, u82, u77, u66, u54, u48, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_301 : look gl gm gg 13 12 0 zv181 [u97, u82, u77, u66, u54, u48, u28, u21, u18, u11] = false := by decide +kernel
def s3_302 : Saved := (12, 0, zv253, [u97, u92, u82, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_302 : look gl gm gg 13 12 0 zv253 [u97, u92, u82, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_303 : Saved := (12, 0, zv244, [u97, u85, u82, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_303 : look gl gm gg 13 12 0 zv244 [u97, u85, u82, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_304 : Saved := (12, 0, zv21, [u97, u82, u77, u66, u54, u48, u26, u21, u18, u11, u0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_304 : look gl gm gg 13 12 0 zv21 [u97, u82, u77, u66, u54, u48, u26, u21, u18, u11, u0] = false := by decide +kernel
def s3_305 : Saved := (12, 0, zv244, [u97, u82, u77, u66, u59, u54, u48, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_305 : look gl gm gg 13 12 0 zv244 [u97, u82, u77, u66, u59, u54, u48, u21, u18, u11] = false := by decide +kernel
def s3_306 : Saved := (12, 0, zv240, [u97, u82, u77, u73, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_306 : look gl gm gg 13 12 0 zv240 [u97, u82, u77, u73, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_307 : Saved := (12, 0, zv175, [u97, u82, u77, u66, u56, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_307 : look gl gm gg 13 12 0 zv175 [u97, u82, u77, u66, u56, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_308 : Saved := (12, 0, zv254, [u97, u77, u66, u54, u48, u36, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_308 : look gl gm gg 13 12 0 zv254 [u97, u77, u66, u54, u48, u36, u26, u21, u18, u11] = false := by decide +kernel
def s3_309 : Saved := (12, 0, zv181, [u97, u82, u77, u66, u54, u50, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_309 : look gl gm gg 13 12 0 zv181 [u97, u82, u77, u66, u54, u50, u26, u21, u18, u11] = false := by decide +kernel
def s3_310 : Saved := (12, 0, zv217, [u97, u82, u77, u68, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_310 : look gl gm gg 13 12 0 zv217 [u97, u82, u77, u68, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_311 : Saved := (12, 0, zv255, [u97, u77, u66, u54, u36, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_311 : look gl gm gg 13 12 0 zv255 [u97, u77, u66, u54, u36, u26, u21, u18, u11] = false := by decide +kernel
def s3_312 : Saved := (12, 0, zv120, [u122, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_312 : look gl gm gg 13 12 0 zv120 [u122, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_313 : Saved := (12, 0, zv251, [u97, u89, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_313 : look gl gm gg 13 12 0 zv251 [u97, u89, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_314 : Saved := (12, 0, zv179, [u97, u82, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_314 : look gl gm gg 13 12 0 zv179 [u97, u82, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_315 : Saved := (12, 0, zv236, [u97, u85, u82, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_315 : look gl gm gg 13 12 0 zv236 [u97, u85, u82, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_316 : Saved := (12, 0, zv120, [u105, u97, u82, u77, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_316 : look gl gm gg 13 12 0 zv120 [u105, u97, u82, u77, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s3_317 : Saved := (12, 0, zv244, [u97, u85, u77, u66, u59, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_317 : look gl gm gg 13 12 0 zv244 [u97, u85, u77, u66, u59, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_318 : Saved := (12, 0, zv19, [u97, u85, u77, u66, u54, u48, u33, u26, u21, u18, u11, u0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_318 : look gl gm gg 13 12 0 zv19 [u97, u85, u77, u66, u54, u48, u33, u26, u21, u18, u11, u0] = false := by decide +kernel
def s3_319 : Saved := (12, 0, zv175, [u97, u85, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_319 : look gl gm gg 13 12 0 zv175 [u97, u85, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_320 : Saved := (12, 0, zv240, [u97, u85, u77, u70, u66, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_320 : look gl gm gg 13 12 0 zv240 [u97, u85, u77, u70, u66, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_321 : Saved := (12, 0, zv242, [u97, u77, u66, u54, u33, u31, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_321 : look gl gm gg 13 12 0 zv242 [u97, u77, u66, u54, u33, u31, u26, u21, u18, u11] = false := by decide +kernel
def s3_322 : Saved := (12, 0, zv175, [u97, u85, u77, u66, u56, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_322 : look gl gm gg 13 12 0 zv175 [u97, u85, u77, u66, u56, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_323 : Saved := (12, 0, zv114, [u120, u97, u85, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_323 : look gl gm gg 13 12 0 zv114 [u120, u97, u85, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_324 : Saved := (12, 0, zv244, [u97, u89, u85, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_324 : look gl gm gg 13 12 0 zv244 [u97, u89, u85, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_325 : Saved := (12, 0, zv240, [u97, u95, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_325 : look gl gm gg 13 12 0 zv240 [u97, u95, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_326 : Saved := (12, 0, zv114, [u106, u97, u85, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_326 : look gl gm gg 13 12 0 zv114 [u106, u97, u85, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_327 : Saved := (12, 0, zv185, [u97, u85, u77, u66, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_327 : look gl gm gg 13 12 0 zv185 [u97, u85, u77, u66, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s3_328 : Saved := (12, 0, zv30, [u97, u84, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_328 : look gl gm gg 13 12 0 zv30 [u97, u84, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_329 : Saved := (12, 0, zv174, [u97, u85, u77, u67, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_329 : look gl gm gg 13 12 0 zv174 [u97, u85, u77, u67, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_330 : Saved := (12, 0, zv175, [u97, u85, u77, u66, u54, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_330 : look gl gm gg 13 12 0 zv175 [u97, u85, u77, u66, u54, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_331 : Saved := (12, 0, zv241, [u97, u77, u66, u54, u48, u33, u31, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_331 : look gl gm gg 13 12 0 zv241 [u97, u77, u66, u54, u48, u33, u31, u26, u21, u18, u11] = false := by decide +kernel
def s3_332 : Saved := (12, 0, zv253, [u97, u92, u77, u70, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_332 : look gl gm gg 13 12 0 zv253 [u97, u92, u77, u70, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_333 : Saved := (12, 0, zv180, [u97, u92, u77, u67, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_333 : look gl gm gg 13 12 0 zv180 [u97, u92, u77, u67, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_334 : Saved := (12, 0, zv180, [u97, u92, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_334 : look gl gm gg 13 12 0 zv180 [u97, u92, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_335 : Saved := (12, 0, zv8, [u97, u77, u70, u66, u54, u48, u33, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_335 : look gl gm gg 13 12 0 zv8 [u97, u77, u70, u66, u54, u48, u33, u21, u18, u11, u3] = false := by decide +kernel
def s3_336 : Saved := (12, 0, zv6, [u97, u77, u73, u66, u54, u48, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_336 : look gl gm gg 13 12 0 zv6 [u97, u77, u73, u66, u54, u48, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s3_337 : Saved := (12, 0, zv9, [u97, u77, u66, u54, u48, u33, u27, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_337 : look gl gm gg 13 12 0 zv9 [u97, u77, u66, u54, u48, u33, u27, u21, u18, u11] = false := by decide +kernel
def s3_338 : Saved := (12, 0, zv7, [u97, u77, u66, u59, u54, u48, u33, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_338 : look gl gm gg 13 12 0 zv7 [u97, u77, u66, u59, u54, u48, u33, u21, u18, u11, u3] = false := by decide +kernel
def s3_339 : Saved := (12, 0, zv3, [u97, u77, u66, u54, u48, u33, u26, u21, u19, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_339 : look gl gm gg 13 12 0 zv3 [u97, u77, u66, u54, u48, u33, u26, u21, u19, u18, u11] = false := by decide +kernel
def s3_340 : Saved := (12, 0, zv9, [u97, u77, u66, u54, u48, u37, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_340 : look gl gm gg 13 12 0 zv9 [u97, u77, u66, u54, u48, u37, u26, u21, u18, u11] = false := by decide +kernel
def s3_341 : Saved := (12, 0, zv7, [u97, u77, u66, u55, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_341 : look gl gm gg 13 12 0 zv7 [u97, u77, u66, u55, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_342 : Saved := (12, 0, zv9, [u97, u77, u66, u54, u48, u33, u26, u21, u19, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_342 : look gl gm gg 13 12 0 zv9 [u97, u77, u66, u54, u48, u33, u26, u21, u19, u11] = false := by decide +kernel
def s3_343 : Saved := (12, 0, zv9, [u97, u77, u66, u54, u48, u33, u26, u22, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_343 : look gl gm gg 13 12 0 zv9 [u97, u77, u66, u54, u48, u33, u26, u22, u18, u11] = false := by decide +kernel
def s3_344 : Saved := (12, 0, zv9, [u97, u77, u66, u54, u49, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_344 : look gl gm gg 13 12 0 zv9 [u97, u77, u66, u54, u49, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_345 : Saved := (12, 0, zv9, [u97, u77, u66, u55, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_345 : look gl gm gg 13 12 0 zv9 [u97, u77, u66, u55, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_346 : Saved := (12, 0, zv68, [u97, u77, u66, u54, u43, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_346 : look gl gm gg 13 12 0 zv68 [u97, u77, u66, u54, u43, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_347 : Saved := (12, 0, zv70, [u107, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_347 : look gl gm gg 13 12 0 zv70 [u107, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_348 : Saved := (12, 0, zv47, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u6])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_348 : look gl gm gg 13 12 0 zv47 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u6] = false := by decide +kernel
def s3_349 : Saved := (12, 0, zv55, [u99, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_349 : look gl gm gg 13 12 0 zv55 [u99, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_350 : Saved := (12, 0, zv58, [u100, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_350 : look gl gm gg 13 12 0 zv58 [u100, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_351 : Saved := (12, 0, zv60, [u103, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_351 : look gl gm gg 13 12 0 zv60 [u103, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_352 : Saved := (12, 0, zv69, [u107, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_352 : look gl gm gg 13 12 0 zv69 [u107, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_353 : Saved := (12, 0, zv17, [u106, u99, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_353 : look gl gm gg 13 12 0 zv17 [u106, u99, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_354 : Saved := (12, 0, zv64, [u120, u99, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_354 : look gl gm gg 13 12 0 zv64 [u120, u99, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_355 : Saved := (12, 0, zv60, [u99, u97, u77, u66, u59, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_355 : look gl gm gg 13 12 0 zv60 [u99, u97, u77, u66, u59, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_356 : Saved := (12, 0, zv66, [u117, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_356 : look gl gm gg 13 12 0 zv66 [u117, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_357 : Saved := (12, 0, zv66, [u99, u97, u77, u71, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_357 : look gl gm gg 13 12 0 zv66 [u99, u97, u77, u71, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_358 : Saved := (12, 0, zv62, [u105, u99, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_358 : look gl gm gg 13 12 0 zv62 [u105, u99, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_359 : Saved := (12, 0, zv64, [u99, u97, u89, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_359 : look gl gm gg 13 12 0 zv64 [u99, u97, u89, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_360 : Saved := (12, 0, zv73, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u1])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_360 : look gl gm gg 13 12 0 zv73 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u1] = false := by decide +kernel
def s3_361 : Saved := (12, 0, zv39, [u98, u97, u77, u66, u54, u33, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_361 : look gl gm gg 13 12 0 zv39 [u98, u97, u77, u66, u54, u33, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_362 : Saved := (12, 0, zv58, [u98, u97, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_362 : look gl gm gg 13 12 0 zv58 [u98, u97, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_363 : Saved := (12, 0, zv110, [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_363 : look gl gm gg 13 12 0 zv110 [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_364 : Saved := (12, 0, zv37, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u8])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_364 : look gl gm gg 13 12 0 zv37 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u8] = false := by decide +kernel
def s3_365 : Saved := (12, 0, zv107, [u116, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_365 : look gl gm gg 13 12 0 zv107 [u116, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_366 : Saved := (12, 0, zv109, [u97, u77, u66, u54, u44, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_366 : look gl gm gg 13 12 0 zv109 [u97, u77, u66, u54, u44, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_367 : Saved := (12, 0, zv104, [u98, u97, u77, u66, u59, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_367 : look gl gm gg 13 12 0 zv104 [u98, u97, u77, u66, u59, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_368 : Saved := (12, 0, zv104, [u101, u98, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_368 : look gl gm gg 13 12 0 zv104 [u101, u98, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_369 : Saved := (12, 0, zv58, [u98, u97, u77, u66, u54, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_369 : look gl gm gg 13 12 0 zv58 [u98, u97, u77, u66, u54, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_370 : Saved := (12, 0, zv104, [u102, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_370 : look gl gm gg 13 12 0 zv104 [u102, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_371 : Saved := (12, 0, zv29, [u97, u77, u66, u54, u44, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_371 : look gl gm gg 13 12 0 zv29 [u97, u77, u66, u54, u44, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_372 : Saved := (12, 0, zv32, [u97, u77, u66, u54, u47, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_372 : look gl gm gg 13 12 0 zv32 [u97, u77, u66, u54, u47, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_373 : Saved := (12, 0, zv16, [u97, u77, u66, u54, u45, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_373 : look gl gm gg 13 12 0 zv16 [u97, u77, u66, u54, u45, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_374 : Saved := (12, 0, zv70, [u106, u97, u77, u66, u54, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_374 : look gl gm gg 13 12 0 zv70 [u106, u97, u77, u66, u54, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_375 : Saved := (12, 0, zv118, [u106, u101, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_375 : look gl gm gg 13 12 0 zv118 [u106, u101, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_376 : Saved := (12, 0, zv60, [u106, u97, u77, u66, u56, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_376 : look gl gm gg 13 12 0 zv60 [u106, u97, u77, u66, u56, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_377 : Saved := (12, 0, zv125, [u124, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_377 : look gl gm gg 13 12 0 zv125 [u124, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_378 : Saved := (12, 0, zv45, [u97, u77, u66, u54, u33, u26, u21, u18, u11, u9])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_378 : look gl gm gg 13 12 0 zv45 [u97, u77, u66, u54, u33, u26, u21, u18, u11, u9] = false := by decide +kernel
def s3_379 : Saved := (12, 0, zv83, [u97, u77, u66, u54, u33, u26, u21, u18, u15, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_379 : look gl gm gg 13 12 0 zv83 [u97, u77, u66, u54, u33, u26, u21, u18, u15, u11] = false := by decide +kernel
def s3_380 : Saved := (12, 0, zv44, [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11, u9])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_380 : look gl gm gg 13 12 0 zv44 [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11, u9] = false := by decide +kernel
def s3_381 : Saved := (12, 0, zv82, [u106, u97, u77, u66, u54, u33, u26, u21, u18, u15, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_381 : look gl gm gg 13 12 0 zv82 [u106, u97, u77, u66, u54, u33, u26, u21, u18, u15, u11] = false := by decide +kernel
def s3_382 : Saved := (12, 0, zv66, [u106, u97, u77, u67, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_382 : look gl gm gg 13 12 0 zv66 [u106, u97, u77, u67, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_383 : Saved := (12, 0, zv115, [u106, u97, u77, u73, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_383 : look gl gm gg 13 12 0 zv115 [u106, u97, u77, u73, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_384 : Saved := (12, 0, zv34, [u115, u106, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_384 : look gl gm gg 13 12 0 zv34 [u115, u106, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_385 : Saved := (12, 0, zv33, [u120, u106, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_385 : look gl gm gg 13 12 0 zv33 [u120, u106, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_386 : Saved := (12, 0, zv58, [u106, u97, u77, u66, u54, u33, u28, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_386 : look gl gm gg 13 12 0 zv58 [u106, u97, u77, u66, u54, u33, u28, u26, u21, u18, u11] = false := by decide +kernel
def s3_387 : Saved := (12, 0, zv28, [u110, u106, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_387 : look gl gm gg 13 12 0 zv28 [u110, u106, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_388 : Saved := (12, 0, zv128, [u119, u106, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_388 : look gl gm gg 13 12 0 zv128 [u119, u106, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_389 : Saved := (12, 0, zv43, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u9])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_389 : look gl gm gg 13 12 0 zv43 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u9] = false := by decide +kernel
def s3_390 : Saved := (12, 0, zv80, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u15, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_390 : look gl gm gg 13 12 0 zv80 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u15, u11] = false := by decide +kernel
def s3_391 : Saved := (12, 0, zv69, [u106, u97, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_391 : look gl gm gg 13 12 0 zv69 [u106, u97, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_392 : Saved := (12, 0, zv69, [u106, u97, u77, u66, u54, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_392 : look gl gm gg 13 12 0 zv69 [u106, u97, u77, u66, u54, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_393 : Saved := (12, 0, zv42, [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_393 : look gl gm gg 13 12 0 zv42 [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_394 : Saved := (12, 0, zv117, [u106, u97, u77, u66, u59, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_394 : look gl gm gg 13 12 0 zv117 [u106, u97, u77, u66, u59, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_395 : Saved := (12, 0, zv124, [u124, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_395 : look gl gm gg 13 12 0 zv124 [u124, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_396 : Saved := (12, 0, zv127, [u106, u97, u77, u70, u66, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_396 : look gl gm gg 13 12 0 zv127 [u106, u97, u77, u70, u66, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_397 : Saved := (12, 0, zv60, [u101, u97, u77, u66, u56, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_397 : look gl gm gg 13 12 0 zv60 [u101, u97, u77, u66, u56, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_398 : Saved := (12, 0, zv60, [u101, u97, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_398 : look gl gm gg 13 12 0 zv60 [u101, u97, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_399 : Saved := (12, 0, zv41, [u101, u97, u77, u66, u54, u33, u26, u21, u18, u11, u7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_399 : look gl gm gg 13 12 0 zv41 [u101, u97, u77, u66, u54, u33, u26, u21, u18, u11, u7] = false := by decide +kernel
def s3_400 : Saved := (12, 0, zv60, [u101, u97, u77, u66, u54, u50, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_400 : look gl gm gg 13 12 0 zv60 [u101, u97, u77, u66, u54, u50, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_401 : Saved := (12, 0, zv116, [u97, u77, u66, u54, u41, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_401 : look gl gm gg 13 12 0 zv116 [u97, u77, u66, u54, u41, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_402 : Saved := (12, 0, zv112, [u105, u101, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_402 : look gl gm gg 13 12 0 zv112 [u105, u101, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_403 : Saved := (12, 0, zv117, [u106, u101, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_403 : look gl gm gg 13 12 0 zv117 [u106, u101, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_404 : Saved := (12, 0, zv40, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u5])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_404 : look gl gm gg 13 12 0 zv40 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u5] = false := by decide +kernel
def s3_405 : Saved := (12, 0, zv75, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u12, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_405 : look gl gm gg 13 12 0 zv75 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u12, u11] = false := by decide +kernel
def s3_406 : Saved := (12, 0, zv115, [u118, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_406 : look gl gm gg 13 12 0 zv115 [u118, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_407 : Saved := (12, 0, zv114, [u121, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_407 : look gl gm gg 13 12 0 zv114 [u121, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_408 : Saved := (12, 0, zv64, [u120, u97, u77, u66, u54, u48, u33, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_408 : look gl gm gg 13 12 0 zv64 [u120, u97, u77, u66, u54, u48, u33, u28, u21, u18, u11] = false := by decide +kernel
def s3_409 : Saved := (12, 0, zv78, [u120, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_409 : look gl gm gg 13 12 0 zv78 [u120, u97, u77, u66, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s3_410 : Saved := (12, 0, zv123, [u97, u77, u66, u54, u46, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_410 : look gl gm gg 13 12 0 zv123 [u97, u77, u66, u54, u46, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_411 : Saved := (12, 0, zv114, [u120, u97, u77, u66, u59, u54, u48, u33, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_411 : look gl gm gg 13 12 0 zv114 [u120, u97, u77, u66, u59, u54, u48, u33, u21, u18, u11] = false := by decide +kernel
def s3_412 : Saved := (12, 0, zv97, [u120, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_412 : look gl gm gg 13 12 0 zv97 [u120, u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s3_413 : Saved := (12, 0, zv122, [u120, u97, u77, u71, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_413 : look gl gm gg 13 12 0 zv122 [u120, u97, u77, u71, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_414 : Saved := (12, 0, zv97, [u123, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_414 : look gl gm gg 13 12 0 zv97 [u123, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s3_415 : Saved := (12, 1, zv169, [u97, u77, u66, u54, u48, u38, u26, u21, u20, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_415 : look gl gm gg 13 12 1 zv169 [u97, u77, u66, u54, u48, u38, u26, u21, u20, u11] = false := by decide +kernel
def s3_416 : Saved := (12, 1, zv169, [u97, u77, u66, u54, u48, u38, u28, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_416 : look gl gm gg 13 12 1 zv169 [u97, u77, u66, u54, u48, u38, u28, u21, u18, u11] = false := by decide +kernel
def s3_417 : Saved := (12, 1, zv211, [u97, u77, u66, u57, u54, u48, u38, u26, u21, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_417 : look gl gm gg 13 12 1 zv211 [u97, u77, u66, u57, u54, u48, u38, u26, u21, u11] = false := by decide +kernel
def s3_418 : Saved := (12, 1, zv228, [u97, u77, u70, u66, u54, u48, u38, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_418 : look gl gm gg 13 12 1 zv228 [u97, u77, u70, u66, u54, u48, u38, u21, u18, u11] = false := by decide +kernel
def s3_419 : Saved := (12, 1, zv211, [u97, u77, u66, u59, u54, u48, u38, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3_419 : look gl gm gg 13 12 1 zv211 [u97, u77, u66, u59, u54, u48, u38, u21, u18, u11] = false := by decide +kernel
def prop3 (s : Saved) : Prop := look gl gm gg 13 s.1 s.2.1 s.2.2.1 s.2.2.2 = false
def b3_1 : List Saved := [s3_38, s3_61, s3_258, s3_263]
set_option maxRecDepth 100000 in
lemma b3_1_ok (s : Saved) (hs : s ∈ b3_1) : prop3 s := by
  simp only [b3_1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact e3_38
  · exact e3_61
  · exact e3_258
  · exact e3_263
def b3_2 : List Saved := [s3_22, s3_25, s3_94, s3_173, s3_185, s3_247, s3_250, s3_259, s3_260, s3_261, s3_262, s3_264, s3_271, s3_272, s3_290, s3_354, s3_359, s3_375, s3_385, s3_408, s3_412, s3_414]
set_option maxRecDepth 100000 in
lemma b3_2_ok (s : Saved) (hs : s ∈ b3_2) : prop3 s := by
  simp only [b3_2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_22
  · exact e3_25
  · exact e3_94
  · exact e3_173
  · exact e3_185
  · exact e3_247
  · exact e3_250
  · exact e3_259
  · exact e3_260
  · exact e3_261
  · exact e3_262
  · exact e3_264
  · exact e3_271
  · exact e3_272
  · exact e3_290
  · exact e3_354
  · exact e3_359
  · exact e3_375
  · exact e3_385
  · exact e3_408
  · exact e3_412
  · exact e3_414
def b3_3 : List Saved := [s3_85, s3_119, s3_204, s3_317, s3_338, s3_419]
set_option maxRecDepth 100000 in
lemma b3_3_ok (s : Saved) (hs : s ∈ b3_3) : prop3 s := by
  simp only [b3_3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_85
  · exact e3_119
  · exact e3_204
  · exact e3_317
  · exact e3_338
  · exact e3_419
def b3_4 : List Saved := [s3_0, s3_3, s3_29, s3_34, s3_35, s3_49, s3_51, s3_59, s3_63, s3_75, s3_86, s3_121, s3_122, s3_156, s3_159, s3_160, s3_162, s3_190, s3_235, s3_236, s3_239, s3_242, s3_243, s3_244, s3_269, s3_292, s3_311, s3_378, s3_379]
set_option maxRecDepth 100000 in
lemma b3_4_ok (s : Saved) (hs : s ∈ b3_4) : prop3 s := by
  simp only [b3_4, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_0
  · exact e3_3
  · exact e3_29
  · exact e3_34
  · exact e3_35
  · exact e3_49
  · exact e3_51
  · exact e3_59
  · exact e3_63
  · exact e3_75
  · exact e3_86
  · exact e3_121
  · exact e3_122
  · exact e3_156
  · exact e3_159
  · exact e3_160
  · exact e3_162
  · exact e3_190
  · exact e3_235
  · exact e3_236
  · exact e3_239
  · exact e3_242
  · exact e3_243
  · exact e3_244
  · exact e3_269
  · exact e3_292
  · exact e3_311
  · exact e3_378
  · exact e3_379
def b3_5 : List Saved := [s3_73, s3_78, s3_103, s3_111, s3_113, s3_120, s3_139, s3_140, s3_171, s3_176, s3_177, s3_183, s3_188, s3_203, s3_205, s3_206, s3_207, s3_208, s3_214, s3_218, s3_221, s3_222, s3_230, s3_266, s3_282, s3_303, s3_318, s3_319, s3_322, s3_324, s3_326, s3_330, s3_341, s3_351, s3_368, s3_370, s3_376, s3_397, s3_398, s3_400, s3_407, s3_413, s3_417]
set_option maxRecDepth 100000 in
lemma b3_5_ok (s : Saved) (hs : s ∈ b3_5) : prop3 s := by
  simp only [b3_5, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_73
  · exact e3_78
  · exact e3_103
  · exact e3_111
  · exact e3_113
  · exact e3_120
  · exact e3_139
  · exact e3_140
  · exact e3_171
  · exact e3_176
  · exact e3_177
  · exact e3_183
  · exact e3_188
  · exact e3_203
  · exact e3_205
  · exact e3_206
  · exact e3_207
  · exact e3_208
  · exact e3_214
  · exact e3_218
  · exact e3_221
  · exact e3_222
  · exact e3_230
  · exact e3_266
  · exact e3_282
  · exact e3_303
  · exact e3_318
  · exact e3_319
  · exact e3_322
  · exact e3_324
  · exact e3_326
  · exact e3_330
  · exact e3_341
  · exact e3_351
  · exact e3_368
  · exact e3_370
  · exact e3_376
  · exact e3_397
  · exact e3_398
  · exact e3_400
  · exact e3_407
  · exact e3_413
  · exact e3_417
def b3_6 : List Saved := [s3_9, s3_31, s3_105, s3_202, s3_265, s3_321, s3_355, s3_367, s3_401]
set_option maxRecDepth 100000 in
lemma b3_6_ok (s : Saved) (hs : s ∈ b3_6) : prop3 s := by
  simp only [b3_6, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_9
  · exact e3_31
  · exact e3_105
  · exact e3_202
  · exact e3_265
  · exact e3_321
  · exact e3_355
  · exact e3_367
  · exact e3_401
def b3_7 : List Saved := [s3_1, s3_2, s3_4, s3_19, s3_47, s3_53, s3_56, s3_57, s3_92, s3_96, s3_101, s3_106, s3_145, s3_152, s3_153, s3_163, s3_164, s3_178, s3_249, s3_346, s3_361, s3_366, s3_371, s3_373, s3_410]
set_option maxRecDepth 100000 in
lemma b3_7_ok (s : Saved) (hs : s ∈ b3_7) : prop3 s := by
  simp only [b3_7, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_1
  · exact e3_2
  · exact e3_4
  · exact e3_19
  · exact e3_47
  · exact e3_53
  · exact e3_56
  · exact e3_57
  · exact e3_92
  · exact e3_96
  · exact e3_101
  · exact e3_106
  · exact e3_145
  · exact e3_152
  · exact e3_153
  · exact e3_163
  · exact e3_164
  · exact e3_178
  · exact e3_249
  · exact e3_346
  · exact e3_361
  · exact e3_366
  · exact e3_371
  · exact e3_373
  · exact e3_410
def b3_8 : List Saved := [s3_40, s3_137, s3_220, s3_223, s3_226, s3_232, s3_273, s3_323]
set_option maxRecDepth 100000 in
lemma b3_8_ok (s : Saved) (hs : s ∈ b3_8) : prop3 s := by
  simp only [b3_8, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_40
  · exact e3_137
  · exact e3_220
  · exact e3_223
  · exact e3_226
  · exact e3_232
  · exact e3_273
  · exact e3_323
def b3_9 : List Saved := [s3_143, s3_150, s3_184, s3_358]
set_option maxRecDepth 100000 in
lemma b3_9_ok (s : Saved) (hs : s ∈ b3_9) : prop3 s := by
  simp only [b3_9, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact e3_143
  · exact e3_150
  · exact e3_184
  · exact e3_358
def b3_10 : List Saved := [s3_68, s3_70, s3_82, s3_93, s3_114, s3_115, s3_127, s3_128, s3_131, s3_135, s3_174, s3_180, s3_191, s3_193, s3_194, s3_335, s3_352, s3_382, s3_391, s3_392, s3_418]
set_option maxRecDepth 100000 in
lemma b3_10_ok (s : Saved) (hs : s ∈ b3_10) : prop3 s := by
  simp only [b3_10, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_68
  · exact e3_70
  · exact e3_82
  · exact e3_93
  · exact e3_114
  · exact e3_115
  · exact e3_127
  · exact e3_128
  · exact e3_131
  · exact e3_135
  · exact e3_174
  · exact e3_180
  · exact e3_191
  · exact e3_193
  · exact e3_194
  · exact e3_335
  · exact e3_352
  · exact e3_382
  · exact e3_391
  · exact e3_392
  · exact e3_418
def b3_11 : List Saved := [s3_287, s3_305]
set_option maxRecDepth 100000 in
lemma b3_11_ok (s : Saved) (hs : s ∈ b3_11) : prop3 s := by
  simp only [b3_11, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact e3_287
  · exact e3_305
def b3_12 : List Saved := [s3_12, s3_141, s3_248]
set_option maxRecDepth 100000 in
lemma b3_12_ok (s : Saved) (hs : s ∈ b3_12) : prop3 s := by
  simp only [b3_12, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact e3_12
  · exact e3_141
  · exact e3_248
def b3_13 : List Saved := [s3_136, s3_142, s3_212, s3_219, s3_275, s3_276, s3_277, s3_307, s3_356, s3_365, s3_384, s3_388]
set_option maxRecDepth 100000 in
lemma b3_13_ok (s : Saved) (hs : s ∈ b3_13) : prop3 s := by
  simp only [b3_13, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_136
  · exact e3_142
  · exact e3_212
  · exact e3_219
  · exact e3_275
  · exact e3_276
  · exact e3_277
  · exact e3_307
  · exact e3_356
  · exact e3_365
  · exact e3_384
  · exact e3_388
def b3_14 : List Saved := [s3_411]
set_option maxRecDepth 100000 in
lemma b3_14_ok (s : Saved) (hs : s ∈ b3_14) : prop3 s := by
  simp only [b3_14, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e3_411
def b3_15 : List Saved := [s3_7, s3_41, s3_44, s3_45, s3_148, s3_296, s3_314, s3_409]
set_option maxRecDepth 100000 in
lemma b3_15_ok (s : Saved) (hs : s ∈ b3_15) : prop3 s := by
  simp only [b3_15, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_7
  · exact e3_41
  · exact e3_44
  · exact e3_45
  · exact e3_148
  · exact e3_296
  · exact e3_314
  · exact e3_409
def b3_16 : List Saved := [s3_129]
set_option maxRecDepth 100000 in
lemma b3_16_ok (s : Saved) (hs : s ∈ b3_16) : prop3 s := by
  simp only [b3_16, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e3_129
def b3_17 : List Saved := [s3_312, s3_316]
set_option maxRecDepth 100000 in
lemma b3_17_ok (s : Saved) (hs : s ∈ b3_17) : prop3 s := by
  simp only [b3_17, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact e3_312
  · exact e3_316
def b3_18 : List Saved := [s3_8, s3_13, s3_15, s3_16, s3_30, s3_32, s3_37, s3_39, s3_42, s3_46, s3_54, s3_60, s3_64, s3_76, s3_118, s3_133, s3_155, s3_158, s3_187, s3_192, s3_195, s3_201, s3_210, s3_280, s3_281, s3_283, s3_286, s3_288, s3_291, s3_299, s3_300, s3_302, s3_310, s3_327, s3_332, s3_333, s3_334, s3_395, s3_399]
set_option maxRecDepth 100000 in
lemma b3_18_ok (s : Saved) (hs : s ∈ b3_18) : prop3 s := by
  simp only [b3_18, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_8
  · exact e3_13
  · exact e3_15
  · exact e3_16
  · exact e3_30
  · exact e3_32
  · exact e3_37
  · exact e3_39
  · exact e3_42
  · exact e3_46
  · exact e3_54
  · exact e3_60
  · exact e3_64
  · exact e3_76
  · exact e3_118
  · exact e3_133
  · exact e3_155
  · exact e3_158
  · exact e3_187
  · exact e3_192
  · exact e3_195
  · exact e3_201
  · exact e3_210
  · exact e3_280
  · exact e3_281
  · exact e3_283
  · exact e3_286
  · exact e3_288
  · exact e3_291
  · exact e3_299
  · exact e3_300
  · exact e3_302
  · exact e3_310
  · exact e3_327
  · exact e3_332
  · exact e3_333
  · exact e3_334
  · exact e3_395
  · exact e3_399
def b3_19 : List Saved := [s3_154, s3_215, s3_238]
set_option maxRecDepth 100000 in
lemma b3_19_ok (s : Saved) (hs : s ∈ b3_19) : prop3 s := by
  simp only [b3_19, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact e3_154
  · exact e3_215
  · exact e3_238
def b3_20 : List Saved := [s3_10, s3_23, s3_36, s3_62, s3_102, s3_126, s3_144, s3_147, s3_149, s3_161, s3_189, s3_213, s3_216, s3_227, s3_252, s3_254, s3_255, s3_256, s3_257, s3_325, s3_336, s3_383, s3_402, s3_406]
set_option maxRecDepth 100000 in
lemma b3_20_ok (s : Saved) (hs : s ∈ b3_20) : prop3 s := by
  simp only [b3_20, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_10
  · exact e3_23
  · exact e3_36
  · exact e3_62
  · exact e3_102
  · exact e3_126
  · exact e3_144
  · exact e3_147
  · exact e3_149
  · exact e3_161
  · exact e3_189
  · exact e3_213
  · exact e3_216
  · exact e3_227
  · exact e3_252
  · exact e3_254
  · exact e3_255
  · exact e3_256
  · exact e3_257
  · exact e3_325
  · exact e3_336
  · exact e3_383
  · exact e3_402
  · exact e3_406
def b3_21 : List Saved := [s3_33, s3_55, s3_123, s3_134, s3_146, s3_224, s3_225, s3_229, s3_315, s3_403]
set_option maxRecDepth 100000 in
lemma b3_21_ok (s : Saved) (hs : s ∈ b3_21) : prop3 s := by
  simp only [b3_21, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_33
  · exact e3_55
  · exact e3_123
  · exact e3_134
  · exact e3_146
  · exact e3_224
  · exact e3_225
  · exact e3_229
  · exact e3_315
  · exact e3_403
def b3_22 : List Saved := [s3_5, s3_14, s3_20, s3_21, s3_26, s3_27, s3_28, s3_43, s3_58, s3_151, s3_157, s3_196, s3_253, s3_372, s3_394, s3_404, s3_405]
set_option maxRecDepth 100000 in
lemma b3_22_ok (s : Saved) (hs : s ∈ b3_22) : prop3 s := by
  simp only [b3_22, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_5
  · exact e3_14
  · exact e3_20
  · exact e3_21
  · exact e3_26
  · exact e3_27
  · exact e3_28
  · exact e3_43
  · exact e3_58
  · exact e3_151
  · exact e3_157
  · exact e3_196
  · exact e3_253
  · exact e3_372
  · exact e3_394
  · exact e3_404
  · exact e3_405
def b3_23 : List Saved := [s3_11, s3_24, s3_48, s3_66, s3_67, s3_72, s3_74, s3_77, s3_79, s3_84, s3_87, s3_88, s3_95, s3_98, s3_99, s3_104, s3_110, s3_112, s3_116, s3_124, s3_130, s3_165, s3_166, s3_167, s3_168, s3_169, s3_172, s3_175, s3_199, s3_200, s3_234, s3_237, s3_240, s3_241, s3_245, s3_246, s3_294, s3_297, s3_308, s3_337, s3_339, s3_340, s3_342, s3_343, s3_344, s3_345, s3_347, s3_348, s3_360, s3_363, s3_364, s3_374, s3_380, s3_381, s3_389, s3_390, s3_393, s3_415, s3_416]
set_option maxRecDepth 100000 in
lemma b3_23_ok (s : Saved) (hs : s ∈ b3_23) : prop3 s := by
  simp only [b3_23, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_11
  · exact e3_24
  · exact e3_48
  · exact e3_66
  · exact e3_67
  · exact e3_72
  · exact e3_74
  · exact e3_77
  · exact e3_79
  · exact e3_84
  · exact e3_87
  · exact e3_88
  · exact e3_95
  · exact e3_98
  · exact e3_99
  · exact e3_104
  · exact e3_110
  · exact e3_112
  · exact e3_116
  · exact e3_124
  · exact e3_130
  · exact e3_165
  · exact e3_166
  · exact e3_167
  · exact e3_168
  · exact e3_169
  · exact e3_172
  · exact e3_175
  · exact e3_199
  · exact e3_200
  · exact e3_234
  · exact e3_237
  · exact e3_240
  · exact e3_241
  · exact e3_245
  · exact e3_246
  · exact e3_294
  · exact e3_297
  · exact e3_308
  · exact e3_337
  · exact e3_339
  · exact e3_340
  · exact e3_342
  · exact e3_343
  · exact e3_344
  · exact e3_345
  · exact e3_347
  · exact e3_348
  · exact e3_360
  · exact e3_363
  · exact e3_364
  · exact e3_374
  · exact e3_380
  · exact e3_381
  · exact e3_389
  · exact e3_390
  · exact e3_393
  · exact e3_415
  · exact e3_416
def b3_24 : List Saved := [s3_198, s3_211, s3_228, s3_233, s3_320, s3_329]
set_option maxRecDepth 100000 in
lemma b3_24_ok (s : Saved) (hs : s ∈ b3_24) : prop3 s := by
  simp only [b3_24, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_198
  · exact e3_211
  · exact e3_228
  · exact e3_233
  · exact e3_320
  · exact e3_329
def b3_25 : List Saved := [s3_17, s3_91, s3_100, s3_108, s3_109, s3_138, s3_186, s3_209, s3_217, s3_328, s3_331, s3_386]
set_option maxRecDepth 100000 in
lemma b3_25_ok (s : Saved) (hs : s ∈ b3_25) : prop3 s := by
  simp only [b3_25, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_17
  · exact e3_91
  · exact e3_100
  · exact e3_108
  · exact e3_109
  · exact e3_138
  · exact e3_186
  · exact e3_209
  · exact e3_217
  · exact e3_328
  · exact e3_331
  · exact e3_386
def b3_26 : List Saved := [s3_6, s3_50, s3_52, s3_80, s3_89, s3_90, s3_97, s3_107, s3_125, s3_132, s3_179, s3_182, s3_251, s3_267, s3_268, s3_270, s3_274, s3_349, s3_350, s3_353, s3_362, s3_369, s3_387]
set_option maxRecDepth 100000 in
lemma b3_26_ok (s : Saved) (hs : s ∈ b3_26) : prop3 s := by
  simp only [b3_26, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_6
  · exact e3_50
  · exact e3_52
  · exact e3_80
  · exact e3_89
  · exact e3_90
  · exact e3_97
  · exact e3_107
  · exact e3_125
  · exact e3_132
  · exact e3_179
  · exact e3_182
  · exact e3_251
  · exact e3_267
  · exact e3_268
  · exact e3_270
  · exact e3_274
  · exact e3_349
  · exact e3_350
  · exact e3_353
  · exact e3_362
  · exact e3_369
  · exact e3_387
def b3_27 : List Saved := [s3_231]
set_option maxRecDepth 100000 in
lemma b3_27_ok (s : Saved) (hs : s ∈ b3_27) : prop3 s := by
  simp only [b3_27, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e3_231
def b3_28 : List Saved := [s3_18, s3_295, s3_306]
set_option maxRecDepth 100000 in
lemma b3_28_ok (s : Saved) (hs : s ∈ b3_28) : prop3 s := by
  simp only [b3_28, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact e3_18
  · exact e3_295
  · exact e3_306
def b3_29 : List Saved := [s3_197, s3_357, s3_396]
set_option maxRecDepth 100000 in
lemma b3_29_ok (s : Saved) (hs : s ∈ b3_29) : prop3 s := by
  simp only [b3_29, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact e3_197
  · exact e3_357
  · exact e3_396
def b3_30 : List Saved := [s3_65, s3_313]
set_option maxRecDepth 100000 in
lemma b3_30_ok (s : Saved) (hs : s ∈ b3_30) : prop3 s := by
  simp only [b3_30, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact e3_65
  · exact e3_313
def b3_31 : List Saved := [s3_69, s3_71, s3_81, s3_83, s3_117, s3_170, s3_181, s3_278, s3_279, s3_284, s3_285, s3_289, s3_293, s3_298, s3_301, s3_304, s3_309, s3_377]
set_option maxRecDepth 100000 in
lemma b3_31_ok (s : Saved) (hs : s ∈ b3_31) : prop3 s := by
  simp only [b3_31, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e3_69
  · exact e3_71
  · exact e3_81
  · exact e3_83
  · exact e3_117
  · exact e3_170
  · exact e3_181
  · exact e3_278
  · exact e3_279
  · exact e3_284
  · exact e3_285
  · exact e3_289
  · exact e3_293
  · exact e3_298
  · exact e3_301
  · exact e3_304
  · exact e3_309
  · exact e3_377
def pick3 (n : ℕ) : {b : List Saved // ∀ s ∈ b, prop3 s} :=
  if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then (⟨[], by simp⟩) else (⟨b3_1, b3_1_ok⟩)) else (if n < 3 then (⟨b3_2, b3_2_ok⟩) else (⟨b3_3, b3_3_ok⟩))) else (if n < 6 then (if n < 5 then (⟨b3_4, b3_4_ok⟩) else (⟨b3_5, b3_5_ok⟩)) else (if n < 7 then (⟨b3_6, b3_6_ok⟩) else (⟨b3_7, b3_7_ok⟩)))) else (if n < 12 then (if n < 10 then (if n < 9 then (⟨b3_8, b3_8_ok⟩) else (⟨b3_9, b3_9_ok⟩)) else (if n < 11 then (⟨b3_10, b3_10_ok⟩) else (⟨b3_11, b3_11_ok⟩))) else (if n < 14 then (if n < 13 then (⟨b3_12, b3_12_ok⟩) else (⟨b3_13, b3_13_ok⟩)) else (if n < 15 then (⟨b3_14, b3_14_ok⟩) else (⟨b3_15, b3_15_ok⟩))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (⟨b3_16, b3_16_ok⟩) else (⟨b3_17, b3_17_ok⟩)) else (if n < 19 then (⟨b3_18, b3_18_ok⟩) else (⟨b3_19, b3_19_ok⟩))) else (if n < 22 then (if n < 21 then (⟨b3_20, b3_20_ok⟩) else (⟨b3_21, b3_21_ok⟩)) else (if n < 23 then (⟨b3_22, b3_22_ok⟩) else (⟨b3_23, b3_23_ok⟩)))) else (if n < 28 then (if n < 26 then (if n < 25 then (⟨b3_24, b3_24_ok⟩) else (⟨b3_25, b3_25_ok⟩)) else (if n < 27 then (⟨b3_26, b3_26_ok⟩) else (⟨b3_27, b3_27_ok⟩))) else (if n < 30 then (if n < 29 then (⟨b3_28, b3_28_ok⟩) else (⟨b3_29, b3_29_ok⟩)) else (if n < 31 then (⟨b3_30, b3_30_ok⟩) else (⟨b3_31, b3_31_ok⟩)))))
def use3 (l m g f k t z : ℕ) (v : List W) : Bool :=
  if (f == 13 && l == gl && m == gm && g == gg && ((pick3 ((v.foldl (fun a w => a + w.s) z) % 32)).val).any (sameSaved k t z v)) then false
  else look l m g f k t z v
lemma use3_eq (l m g f : ℕ) : use3 l m g f = look l m g f := by
  funext k t z v
  unfold use3
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
    obtain ⟨⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,s,hs,hh⟩ := h
    have he := sameSaved_eq hh
    subst s
    have all := (pick3 ((v.foldl (fun a w => a + w.s) z) % 32)).property _ hs
    change look gl gm gg 13 k t z v = false at all
    exact all.symm
  · rfl

def oneBelow (l m g : ℕ) : ℕ → ℕ → ℕ → ℕ → List W → Bool
  | 0 => look l m g 0
  | n + 1 => oneStep l m g (use3 l m g n)
lemma oneBelow_eq (l m g f : ℕ) : oneBelow l m g f = look l m g f := by
  cases f with
  | zero => rfl
  | succ n => change oneStep l m g (use3 l m g n) = _; rw [use3_eq]; rfl
def s2_0 : Saved := (13, 0, zv170, [u97, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_0 : oneBelow gl gm gg 14 13 0 zv170 [u97, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s2_1 : Saved := (13, 0, zv197, [u97, u77, u66, u54, u33, u29, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_1 : oneBelow gl gm gg 14 13 0 zv197 [u97, u77, u66, u54, u33, u29, u26, u21, u18, u11] = false := by decide +kernel
def s2_2 : Saved := (13, 0, zv216, [u97, u77, u66, u54, u38, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_2 : oneBelow gl gm gg 14 13 0 zv216 [u97, u77, u66, u54, u38, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_3 : Saved := (13, 0, zv234, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_3 : oneBelow gl gm gg 14 13 0 zv234 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_4 : Saved := (13, 0, zv212, [u97, u77, u66, u57, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_4 : oneBelow gl gm gg 14 13 0 zv212 [u97, u77, u66, u57, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_5 : Saved := (13, 0, zv239, [u97, u77, u66, u60, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_5 : oneBelow gl gm gg 14 13 0 zv239 [u97, u77, u66, u60, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_6 : Saved := (13, 0, zv182, [u97, u80, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_6 : oneBelow gl gm gg 14 13 0 zv182 [u97, u80, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_7 : Saved := (13, 0, zv223, [u97, u79, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_7 : oneBelow gl gm gg 14 13 0 zv223 [u97, u79, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_8 : Saved := (13, 0, zv252, [u97, u82, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_8 : oneBelow gl gm gg 14 13 0 zv252 [u97, u82, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_9 : Saved := (13, 0, zv245, [u97, u85, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_9 : oneBelow gl gm gg 14 13 0 zv245 [u97, u85, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_10 : Saved := (13, 0, zv10, [u97, u77, u66, u54, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_10 : oneBelow gl gm gg 14 13 0 zv10 [u97, u77, u66, u54, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s2_11 : Saved := (13, 0, zv71, [u99, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_11 : oneBelow gl gm gg 14 13 0 zv71 [u99, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_12 : Saved := (13, 0, zv111, [u98, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_12 : oneBelow gl gm gg 14 13 0 zv111 [u98, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_13 : Saved := (13, 0, zv119, [u101, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_13 : oneBelow gl gm gg 14 13 0 zv119 [u101, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_14 : Saved := (13, 0, zv126, [u120, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_14 : oneBelow gl gm gg 14 13 0 zv126 [u120, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_15 : Saved := (13, 0, zv169, [u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_15 : oneBelow gl gm gg 14 13 0 zv169 [u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s2_16 : Saved := (13, 0, zv196, [u97, u77, u66, u54, u48, u33, u29, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_16 : oneBelow gl gm gg 14 13 0 zv196 [u97, u77, u66, u54, u48, u33, u29, u26, u21, u18, u11] = false := by decide +kernel
def s2_17 : Saved := (13, 0, zv233, [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_17 : oneBelow gl gm gg 14 13 0 zv233 [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s2_18 : Saved := (13, 0, zv215, [u97, u77, u66, u54, u48, u38, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_18 : oneBelow gl gm gg 14 13 0 zv215 [u97, u77, u66, u54, u48, u38, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_19 : Saved := (13, 0, zv190, [u97, u77, u66, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_19 : oneBelow gl gm gg 14 13 0 zv190 [u97, u77, u66, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s2_20 : Saved := (13, 0, zv189, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_20 : oneBelow gl gm gg 14 13 0 zv189 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s2_21 : Saved := (13, 0, zv233, [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_21 : oneBelow gl gm gg 14 13 0 zv233 [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_22 : Saved := (13, 0, zv232, [u97, u77, u66, u54, u51, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_22 : oneBelow gl gm gg 14 13 0 zv232 [u97, u77, u66, u54, u51, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_23 : Saved := (13, 0, zv211, [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_23 : oneBelow gl gm gg 14 13 0 zv211 [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_24 : Saved := (13, 0, zv250, [u97, u77, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_24 : oneBelow gl gm gg 14 13 0 zv250 [u97, u77, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s2_25 : Saved := (13, 0, zv238, [u97, u77, u66, u60, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_25 : oneBelow gl gm gg 14 13 0 zv238 [u97, u77, u66, u60, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_26 : Saved := (13, 0, zv250, [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_26 : oneBelow gl gm gg 14 13 0 zv250 [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_27 : Saved := (13, 0, zv249, [u97, u77, u66, u63, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_27 : oneBelow gl gm gg 14 13 0 zv249 [u97, u77, u66, u63, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_28 : Saved := (13, 0, zv258, [u97, u77, u71, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_28 : oneBelow gl gm gg 14 13 0 zv258 [u97, u77, u71, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_29 : Saved := (13, 0, zv257, [u97, u77, u71, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_29 : oneBelow gl gm gg 14 13 0 zv257 [u97, u77, u71, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_30 : Saved := (13, 0, zv181, [u97, u80, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_30 : oneBelow gl gm gg 14 13 0 zv181 [u97, u80, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_31 : Saved := (13, 0, zv222, [u97, u79, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_31 : oneBelow gl gm gg 14 13 0 zv222 [u97, u79, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_32 : Saved := (13, 0, zv256, [u97, u82, u77, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_32 : oneBelow gl gm gg 14 13 0 zv256 [u97, u82, u77, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s2_33 : Saved := (13, 0, zv251, [u97, u82, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_33 : oneBelow gl gm gg 14 13 0 zv251 [u97, u82, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_34 : Saved := (13, 0, zv244, [u97, u85, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_34 : oneBelow gl gm gg 14 13 0 zv244 [u97, u85, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_35 : Saved := (13, 0, zv253, [u97, u92, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_35 : oneBelow gl gm gg 14 13 0 zv253 [u97, u92, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_36 : Saved := (13, 0, zv9, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_36 : oneBelow gl gm gg 14 13 0 zv9 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s2_37 : Saved := (13, 0, zv70, [u99, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_37 : oneBelow gl gm gg 14 13 0 zv70 [u99, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_38 : Saved := (13, 0, zv110, [u98, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_38 : oneBelow gl gm gg 14 13 0 zv110 [u98, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_39 : Saved := (13, 0, zv36, [u97, u77, u66, u54, u40, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_39 : oneBelow gl gm gg 14 13 0 zv36 [u97, u77, u66, u54, u40, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_40 : Saved := (13, 0, zv35, [u97, u77, u66, u54, u48, u40, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_40 : oneBelow gl gm gg 14 13 0 zv35 [u97, u77, u66, u54, u48, u40, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_41 : Saved := (13, 0, zv131, [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_41 : oneBelow gl gm gg 14 13 0 zv131 [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_42 : Saved := (13, 0, zv130, [u106, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_42 : oneBelow gl gm gg 14 13 0 zv130 [u106, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_43 : Saved := (13, 0, zv118, [u101, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_43 : oneBelow gl gm gg 14 13 0 zv118 [u101, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_44 : Saved := (13, 0, zv125, [u120, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_44 : oneBelow gl gm gg 14 13 0 zv125 [u120, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_45 : Saved := (13, 1, zv170, [u97, u77, u66, u54, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_45 : oneBelow gl gm gg 14 13 1 zv170 [u97, u77, u66, u54, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s2_46 : Saved := (13, 1, zv216, [u97, u77, u66, u54, u38, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_46 : oneBelow gl gm gg 14 13 1 zv216 [u97, u77, u66, u54, u38, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_47 : Saved := (13, 1, zv234, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_47 : oneBelow gl gm gg 14 13 1 zv234 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_48 : Saved := (13, 1, zv212, [u97, u77, u66, u57, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_48 : oneBelow gl gm gg 14 13 1 zv212 [u97, u77, u66, u57, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_49 : Saved := (13, 1, zv71, [u99, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_49 : oneBelow gl gm gg 14 13 1 zv71 [u99, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_50 : Saved := (13, 1, zv111, [u98, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_50 : oneBelow gl gm gg 14 13 1 zv111 [u98, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_51 : Saved := (13, 1, zv119, [u101, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_51 : oneBelow gl gm gg 14 13 1 zv119 [u101, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_52 : Saved := (13, 1, zv169, [u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_52 : oneBelow gl gm gg 14 13 1 zv169 [u97, u77, u66, u54, u48, u33, u26, u21, u20, u18, u11] = false := by decide +kernel
def s2_53 : Saved := (13, 1, zv233, [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_53 : oneBelow gl gm gg 14 13 1 zv233 [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s2_54 : Saved := (13, 1, zv190, [u97, u77, u66, u54, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_54 : oneBelow gl gm gg 14 13 1 zv190 [u97, u77, u66, u54, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s2_55 : Saved := (13, 1, zv189, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u13, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_55 : oneBelow gl gm gg 14 13 1 zv189 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u13, u11] = false := by decide +kernel
def s2_56 : Saved := (13, 1, zv233, [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_56 : oneBelow gl gm gg 14 13 1 zv233 [u97, u77, u66, u54, u51, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_57 : Saved := (13, 1, zv232, [u97, u77, u66, u54, u51, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_57 : oneBelow gl gm gg 14 13 1 zv232 [u97, u77, u66, u54, u51, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_58 : Saved := (13, 1, zv211, [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_58 : oneBelow gl gm gg 14 13 1 zv211 [u97, u77, u66, u57, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_59 : Saved := (13, 1, zv250, [u97, u77, u66, u60, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_59 : oneBelow gl gm gg 14 13 1 zv250 [u97, u77, u66, u60, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s2_60 : Saved := (13, 1, zv250, [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_60 : oneBelow gl gm gg 14 13 1 zv250 [u97, u77, u66, u63, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_61 : Saved := (13, 1, zv258, [u97, u77, u71, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_61 : oneBelow gl gm gg 14 13 1 zv258 [u97, u77, u71, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_62 : Saved := (13, 1, zv222, [u97, u79, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_62 : oneBelow gl gm gg 14 13 1 zv222 [u97, u79, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_63 : Saved := (13, 1, zv256, [u97, u82, u77, u66, u54, u48, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_63 : oneBelow gl gm gg 14 13 1 zv256 [u97, u82, u77, u66, u54, u48, u26, u21, u18, u11] = false := by decide +kernel
def s2_64 : Saved := (13, 1, zv244, [u97, u85, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_64 : oneBelow gl gm gg 14 13 1 zv244 [u97, u85, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_65 : Saved := (13, 1, zv9, [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_65 : oneBelow gl gm gg 14 13 1 zv9 [u97, u77, u66, u54, u48, u33, u26, u21, u18, u11, u3] = false := by decide +kernel
def s2_66 : Saved := (13, 1, zv70, [u99, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_66 : oneBelow gl gm gg 14 13 1 zv70 [u99, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_67 : Saved := (13, 1, zv110, [u98, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_67 : oneBelow gl gm gg 14 13 1 zv110 [u98, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_68 : Saved := (13, 1, zv131, [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_68 : oneBelow gl gm gg 14 13 1 zv131 [u106, u97, u77, u66, u54, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_69 : Saved := (13, 1, zv130, [u106, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_69 : oneBelow gl gm gg 14 13 1 zv130 [u106, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_70 : Saved := (13, 1, zv118, [u101, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_70 : oneBelow gl gm gg 14 13 1 zv118 [u101, u97, u77, u66, u54, u48, u33, u26, u21, u18, u11] = false := by decide +kernel
def s2_71 : Saved := (13, 2, zv233, [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_71 : oneBelow gl gm gg 14 13 2 zv233 [u97, u77, u66, u54, u48, u38, u26, u21, u18, u11] = false := by decide +kernel
def s2_72 : Saved := (13, 2, zv235, [u97, u77, u66, u54, u48, u24, u21, u18, u11])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2_72 : oneBelow gl gm gg 14 13 2 zv235 [u97, u77, u66, u54, u48, u24, u21, u18, u11] = false := by decide +kernel
def prop2 (s : Saved) : Prop := oneBelow gl gm gg 14 s.1 s.2.1 s.2.2.1 s.2.2.2 = false
def b2_1 : List Saved := [s2_5]
set_option maxRecDepth 100000 in
lemma b2_1_ok (s : Saved) (hs : s ∈ b2_1) : prop2 s := by
  simp only [b2_1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e2_5
def b2_2 : List Saved := [s2_26, s2_44, s2_60]
set_option maxRecDepth 100000 in
lemma b2_2_ok (s : Saved) (hs : s ∈ b2_2) : prop2 s := by
  simp only [b2_2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact e2_26
  · exact e2_44
  · exact e2_60
def b2_3 : List Saved := [s2_72]
set_option maxRecDepth 100000 in
lemma b2_3_ok (s : Saved) (hs : s ∈ b2_3) : prop2 s := by
  simp only [b2_3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e2_72
def b2_4 : List Saved := [s2_0, s2_10, s2_19, s2_24, s2_45, s2_54, s2_59]
set_option maxRecDepth 100000 in
lemma b2_4_ok (s : Saved) (hs : s ∈ b2_4) : prop2 s := by
  simp only [b2_4, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e2_0
  · exact e2_10
  · exact e2_19
  · exact e2_24
  · exact e2_45
  · exact e2_54
  · exact e2_59
def b2_5 : List Saved := [s2_23, s2_34, s2_43, s2_58, s2_64, s2_70]
set_option maxRecDepth 100000 in
lemma b2_5_ok (s : Saved) (hs : s ∈ b2_5) : prop2 s := by
  simp only [b2_5, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact e2_23
  · exact e2_34
  · exact e2_43
  · exact e2_58
  · exact e2_64
  · exact e2_70
def b2_6 : List Saved := [s2_1]
set_option maxRecDepth 100000 in
lemma b2_6_ok (s : Saved) (hs : s ∈ b2_6) : prop2 s := by
  simp only [b2_6, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e2_1
def b2_7 : List Saved := [s2_11, s2_12, s2_18, s2_39, s2_49, s2_50]
set_option maxRecDepth 100000 in
lemma b2_7_ok (s : Saved) (hs : s ∈ b2_7) : prop2 s := by
  simp only [b2_7, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact e2_11
  · exact e2_12
  · exact e2_18
  · exact e2_39
  · exact e2_49
  · exact e2_50
def b2_10 : List Saved := [s2_22, s2_42, s2_57, s2_69]
set_option maxRecDepth 100000 in
lemma b2_10_ok (s : Saved) (hs : s ∈ b2_10) : prop2 s := by
  simp only [b2_10, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact e2_22
  · exact e2_42
  · exact e2_57
  · exact e2_69
def b2_12 : List Saved := [s2_6, s2_7]
set_option maxRecDepth 100000 in
lemma b2_12_ok (s : Saved) (hs : s ∈ b2_12) : prop2 s := by
  simp only [b2_12, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact e2_6
  · exact e2_7
def b2_13 : List Saved := [s2_29]
set_option maxRecDepth 100000 in
lemma b2_13_ok (s : Saved) (hs : s ∈ b2_13) : prop2 s := by
  simp only [b2_13, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e2_29
def b2_15 : List Saved := [s2_14, s2_33]
set_option maxRecDepth 100000 in
lemma b2_15_ok (s : Saved) (hs : s ∈ b2_15) : prop2 s := by
  simp only [b2_15, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact e2_14
  · exact e2_33
def b2_18 : List Saved := [s2_4, s2_9, s2_13, s2_35, s2_48, s2_51]
set_option maxRecDepth 100000 in
lemma b2_18_ok (s : Saved) (hs : s ∈ b2_18) : prop2 s := by
  simp only [b2_18, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact e2_4
  · exact e2_9
  · exact e2_13
  · exact e2_35
  · exact e2_48
  · exact e2_51
def b2_20 : List Saved := [s2_2, s2_25, s2_46]
set_option maxRecDepth 100000 in
lemma b2_20_ok (s : Saved) (hs : s ∈ b2_20) : prop2 s := by
  simp only [b2_20, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact e2_2
  · exact e2_25
  · exact e2_46
def b2_21 : List Saved := [s2_27]
set_option maxRecDepth 100000 in
lemma b2_21_ok (s : Saved) (hs : s ∈ b2_21) : prop2 s := by
  simp only [b2_21, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e2_27
def b2_22 : List Saved := [s2_3, s2_47]
set_option maxRecDepth 100000 in
lemma b2_22_ok (s : Saved) (hs : s ∈ b2_22) : prop2 s := by
  simp only [b2_22, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact e2_3
  · exact e2_47
def b2_23 : List Saved := [s2_15, s2_17, s2_20, s2_21, s2_36, s2_41, s2_52, s2_53, s2_55, s2_56, s2_65, s2_68, s2_71]
set_option maxRecDepth 100000 in
lemma b2_23_ok (s : Saved) (hs : s ∈ b2_23) : prop2 s := by
  simp only [b2_23, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e2_15
  · exact e2_17
  · exact e2_20
  · exact e2_21
  · exact e2_36
  · exact e2_41
  · exact e2_52
  · exact e2_53
  · exact e2_55
  · exact e2_56
  · exact e2_65
  · exact e2_68
  · exact e2_71
def b2_25 : List Saved := [s2_16]
set_option maxRecDepth 100000 in
lemma b2_25_ok (s : Saved) (hs : s ∈ b2_25) : prop2 s := by
  simp only [b2_25, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e2_16
def b2_26 : List Saved := [s2_28, s2_37, s2_38, s2_40, s2_61, s2_66, s2_67]
set_option maxRecDepth 100000 in
lemma b2_26_ok (s : Saved) (hs : s ∈ b2_26) : prop2 s := by
  simp only [b2_26, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e2_28
  · exact e2_37
  · exact e2_38
  · exact e2_40
  · exact e2_61
  · exact e2_66
  · exact e2_67
def b2_28 : List Saved := [s2_8]
set_option maxRecDepth 100000 in
lemma b2_28_ok (s : Saved) (hs : s ∈ b2_28) : prop2 s := by
  simp only [b2_28, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · exact e2_8
def b2_31 : List Saved := [s2_30, s2_31, s2_32, s2_62, s2_63]
set_option maxRecDepth 100000 in
lemma b2_31_ok (s : Saved) (hs : s ∈ b2_31) : prop2 s := by
  simp only [b2_31, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e2_30
  · exact e2_31
  · exact e2_32
  · exact e2_62
  · exact e2_63
def pick2 (n : ℕ) : {b : List Saved // ∀ s ∈ b, prop2 s} :=
  if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then (⟨[], by simp⟩) else (⟨b2_1, b2_1_ok⟩)) else (if n < 3 then (⟨b2_2, b2_2_ok⟩) else (⟨b2_3, b2_3_ok⟩))) else (if n < 6 then (if n < 5 then (⟨b2_4, b2_4_ok⟩) else (⟨b2_5, b2_5_ok⟩)) else (if n < 7 then (⟨b2_6, b2_6_ok⟩) else (⟨b2_7, b2_7_ok⟩)))) else (if n < 12 then (if n < 10 then (if n < 9 then (⟨[], by simp⟩) else (⟨[], by simp⟩)) else (if n < 11 then (⟨b2_10, b2_10_ok⟩) else (⟨[], by simp⟩))) else (if n < 14 then (if n < 13 then (⟨b2_12, b2_12_ok⟩) else (⟨b2_13, b2_13_ok⟩)) else (if n < 15 then (⟨[], by simp⟩) else (⟨b2_15, b2_15_ok⟩))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (⟨[], by simp⟩) else (⟨[], by simp⟩)) else (if n < 19 then (⟨b2_18, b2_18_ok⟩) else (⟨[], by simp⟩))) else (if n < 22 then (if n < 21 then (⟨b2_20, b2_20_ok⟩) else (⟨b2_21, b2_21_ok⟩)) else (if n < 23 then (⟨b2_22, b2_22_ok⟩) else (⟨b2_23, b2_23_ok⟩)))) else (if n < 28 then (if n < 26 then (if n < 25 then (⟨[], by simp⟩) else (⟨b2_25, b2_25_ok⟩)) else (if n < 27 then (⟨b2_26, b2_26_ok⟩) else (⟨[], by simp⟩))) else (if n < 30 then (if n < 29 then (⟨b2_28, b2_28_ok⟩) else (⟨[], by simp⟩)) else (if n < 31 then (⟨[], by simp⟩) else (⟨b2_31, b2_31_ok⟩)))))
def use2 (l m g f k t z : ℕ) (v : List W) : Bool :=
  if (f == 14 && l == gl && m == gm && g == gg && ((pick2 ((v.foldl (fun a w => a + w.s) z) % 32)).val).any (sameSaved k t z v)) then false
  else oneBelow l m g f k t z v
lemma use2_eq (l m g f : ℕ) : use2 l m g f = look l m g f := by
  funext k t z v
  unfold use2
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
    obtain ⟨⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,s,hs,hh⟩ := h
    have he := sameSaved_eq hh
    subst s
    have all := (pick2 ((v.foldl (fun a w => a + w.s) z) % 32)).property _ hs
    change oneBelow gl gm gg 14 k t z v = false at all
    rw [oneBelow_eq] at all; exact all.symm
  · rw [oneBelow_eq]
def topF (l m g fuel H HN k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (use2 l m g fuel (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub k 2) s)
        v.length z v (pairsQ q q')) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z (Nat.succ q) v v)) true
        (node (use2 l m g fuel (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z v (pairsP q)))) (pos s) l m g (Nat.sub k s) v.length z 0 v (filt HN v))) true
      (node (use2 l m g fuel (Nat.sub k 1) t) (pos t) l m g (Nat.sub k t) v.length z v (pairsC H))) true (Nat.ble v.length 1)
lemma topF_eq : topF = topC := by
  funext l m g f h n k t z v
  simp only [topF, topC, use2_eq]
def startv (l m g B K t H HN : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topF l m g K H HN K t z r) (pos t) l g (Nat.sub (Nat.succ K) t) v.length (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (Nat.beq (cov (pos t) l v) l)
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {v : List W} : ∀ {h : List W → Bool}, anySub v h = false → ∀ r, r.Sublist v → h r = false := by
  induction v with
  | nil => intro h hh r hr; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro h hh r hr
    change (Bool.rec (motive := fun _ => Bool) (anySub v h) true (anySub v fun r => h (w :: r)) : Bool) = false at hh
    rw [bR] at hh
    cases h1 : anySub v (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      cases hr with
      | cons _ hr => exact ih hh r hr
      | cons_cons _ hr => exact ih h1 _ hr
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma filt_mem {H : ℕ} {v : List W} {w : W} (hw : w ∈ v) (hH : hb H w.s = true) : w ∈ filt H v := by
  induction v with
  | nil => simp at hw
  | cons x v ih =>
    have e : filt H (x :: v) = bif hb H x.s then x :: filt H v else filt H v := by
      change Bool.rec (motive := fun _ => List W) (filt H v) (x :: filt H v) (hb H x.s) = _
      cases hb H x.s <;> rfl
    rw [e]
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · rw [hH]; simp
    · cases hb H x.s <;> simp [ih hw]
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
lemma topC_succ {l m g fuel H HN k t z : ℕ} {v : List W} (h : topC l m g fuel H HN k t z v = false) :
    2 ≤ v.length ∧ node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v (pairsC H) = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v (filt HN v) = false := by
  simp only [topC, bR, pos_eq] at h
  cases h0 : Nat.ble v.length 1 with
  | true => rw [h0] at h; simp at h
  | false =>
    rw [h0, Bool.cond_false] at h
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    cases h1 : node (look l m g fuel (Nat.sub k 1) t) (pos' t) l m g (Nat.sub k t) v.length z v (pairsC H) with
    | true => rw [h1] at h; simp at h
    | false =>
      rw [h1, Bool.cond_false] at h
      refine ⟨hlen, rfl, ?_⟩
      rintro s rfl
      exact h
def KP (M : List (ℕ × ℕ)) (x y : ℕ) : Prop := ∃ p ∈ M, hb p.1 (x + y) = true
def KN (M : List (ℕ × ℕ)) (x : ℕ) : Prop := ∃ p ∈ M, hb p.2 x = true
lemma topC_sound {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T) {fuel k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} (hlen : 2 ≤ v.length)
    (h : ∀ p ∈ M, topC l m g fuel p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) :
    ∀ k' ≤ k, Min m T k' t S → ¬ FM m T k' t S (KP M) (KN M) := by
  refine step_sound X (look_sound X fuel) hs hlen (fun x y hxy ⟨p, hpM, hpx⟩ => ⟨pairsC p.1, (topC_succ (h p hpM)).2.1, ?_⟩)
    (fun s hst a ha ⟨p, hpM, hpa⟩ => ⟨_, filt_mem ha hpa, (topC_succ (h p hpM)).2.2 s hst⟩)
  intro h hp a b ha hb' hax hby
  have hpw := pairsC_false hp
  have : Std.Symm (fun a b : L_meta_1674.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
    ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
  refine (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
    (List.mem_map_of_mem ha) (List.mem_map_of_mem hb') ?_ ?_
  · intro e
    have : a.s = b.s := congrArg L_meta_1674.X.s e
    exact hxy (by rw [← hax, ← hby, this])
  · change hb p.1 (a.s + b.s) = true; rw [hax, hby]; exact hpx
def tab : List (ℕ × ℕ) := [(19,8), (25,8), (28,8), (49,8), (67,8), (70,8), (81,8), (82,8), (88,7), (134,8), (140,8), (145,8), (148,8), (152,7), (161,8), (164,8), (176,7), (194,8), (196,8), (208,7), (224,7), (280,7), (322,8), (328,7), (336,7), (352,7), (416,7), (448,7), (7,7), (14,7), (21,7), (26,7), (35,7), (56,6), (74,7), (84,7), (98,7), (112,6), (133,7), (146,7), (162,7), (168,6), (193,7), (200,6), (268,7), (273,7), (289,7), (296,6), (321,7), (324,7), (388,7), (400,6), (22,6), (76,6), (97,6), (131,6), (304,5), (392,5), (11,5), (13,5), (37,5), (38,5), (41,5), (42,5), (44,5), (50,5), (52,5), (69,5), (73,5), (100,5), (104,5), (137,5), (138,5), (259,5), (261,5), (262,5), (265,5), (266,5), (274,5), (276,5), (290,5), (292,5), (385,5), (386,5), (17,11), (24,10), (66,11), (80,10), (132,11), (144,10), (160,10), (192,10), (320,10), (3,9), (6,9), (12,9), (18,9), (20,9), (33,9), (48,8), (65,9), (68,9), (72,9), (96,9), (129,9), (130,9), (136,8), (264,8), (272,8), (288,8), (384,8), (5,8), (9,8), (10,8), (34,8), (36,8), (40,8), (257,8), (258,8), (260,8), (16,12), (64,13), (128,12), (1,12), (2,12), (4,12), (8,11), (32,11), (256,11)]
def pr (Z : ℕ) : List (ℕ × ℕ) := tab.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def WZ (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL, x = w &&& mz Z}
def Imp (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol (mz Z) (tz Z) q (C (mz Z) (WZ Z))
def PZ (Z : ℕ) : List ℕ := (pr Z).map (fun e => mz e.1)
def pOk (Z : ℕ) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && (pr Z).all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
noncomputable def chk (Z K t H HN : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B =>
    frc (avl P m rawL) (fun v => anySub v (fun r => st l fun l => st m fun m => st g fun g => st B fun B => startv l m g B K t H HN r)))
    (pL ((pr Z).map fun e => 16 + (K - e.2)))) (pL ((pr Z).map fun _ => 16))) (PZ Z)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ Z) : Im (mz Z') S ⊆ WZ Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Z K : ℕ) : pL ((pr Z).map fun e => 16 + (K - e.2)) = pk (PZ Z).length (fun j => 16 + (K - ((pr Z).getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
theorem imp_of {Z L : ℕ} (hp : pOk Z = true) (hL : L ≤ 15) (hI : ∀ e ∈ pr Z, Imp e.1 e.2)
    (hb : (∃ e ∈ pr Z, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), M ≠ [] ∧ (∀ p ∈ M, chk Z (L - 1) t p.1 p.2 = false) ∧
      ∀ (k : ℕ) (S : Finset ℕ), (S : Set ℕ) ⊆ WZ Z → Min (mz Z) (tz Z) k t S → 2 ≤ S.card →
        ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ Z ∧ Min (mz Z) (tz Z) k t S' ∧ FM (mz Z) (tz Z) k t S' (KP M) (KN M)) : Imp Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  classical
  have hex : ∃ q, Sol (mz Z) (tz Z) q (C (mz Z) (WZ Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ pr Z, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ Z → ∀ e ∈ pr Z, ∀ q < e.2, ¬ Sol (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro S hSW e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno S hSW e he q' (by omega) hs'
  obtain ⟨M, hM, hchk, hsym⟩ := hb t (by omega)
  have key : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ Z → Min (mz Z) (tz Z) k t S → 2 ≤ S.card ∧ ¬ FM (mz Z) (tz Z) k t S (KP M) (KN M) := by
    clear h0 h1 hbd hl hm hSW hCS hS S
    intro S hSW hm
    have hl := hm.1
    have hbd : ∀ x ∈ S, x &&& mz Z = x := by
      intro x hx
      obtain ⟨w, _, rfl⟩ := hSW hx
      rw [Nat.and_assoc, Nat.and_self]
    obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
    obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Z) (mz Z) rawL
    set v := (avl (PZ Z) (mz Z) rawL).filter (fun w => decide (w.s ∈ S)) with hv
    have hsub : v.Sublist (avl (PZ Z) (mz Z) rawL) := List.filter_sublist
    have hnd : (v.map W.s).Nodup := by
      rw [List.Nodup, List.pairwise_map]
      exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
    have hrep : Rep v S := by
      refine ⟨hnd, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [hv, List.mem_filter] at hw; simpa using hw.2
      · intro hx
        obtain ⟨w, hw, rfl⟩ := hSW hx
        obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
        exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
    have hwok : ∀ w ∈ v, WOk (PZ Z) w := by
      intro w hw
      obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
    have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good hx Z
    have hPlen : (PZ Z).length = (pr Z).length := by simp [PZ]
    have hPget : ∀ j < (PZ Z).length, (PZ Z).getD j 0 = mz ((pr Z).getD j (0, L - 1)).1 ∧ (pr Z).getD j (0, L - 1) ∈ pr Z := by
      intro j hj
      rw [hPlen] at hj
      simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    have X : Ctx (PZ Z) (lz Z) (mz Z) (pL ((pr Z).map fun _ => 16)) (tz Z) := by
      refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
      · obtain ⟨e1, e2⟩ := hPget j hj
        have h3 := hproj _ e2
        rw [e1, tz_sub h3.1]; exact h3
      · rw [pL_pk, List.length_map, hPlen]
        refine pk_congr fun j hj => ?_
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
    have hcl : Cl (PZ Z) (tz Z) (L - 1) (fun j => L - 1 - ((pr Z).getD j (0, L - 1)).2) S := by
      intro j hj q hq
      obtain ⟨e1, e2⟩ := hPget j hj
      have hq' : q + (L - 1 - ((pr Z).getD j (0, L - 1)).2) < L - 1 := hq
      rw [e1]; exact hno S hSW _ e2 q (by omega)
    have hle := cnt_le X hrep hwok hcl hm (by omega)
    have hst : StOk (PZ Z) (tz Z) (lz Z) (L - 1) (pL ((pr Z).map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
      refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
      rw [sumc_eq hwok, pk16, pk_sub]
      intro j hj; have := hle j hj; omega
    have hcov : Nat.beq (cov (pos t) (lz Z) v) (lz Z) = true := by
      rw [Nat.beq_eq]
      apply Nat.eq_of_testBit_eq; intro i
      cases hli : (lz Z).testBit i with
      | false =>
        by_contra hc
        obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
        rw [sp_bit, hli] at hw; simp at hw
      | true =>
        rw [cov_bit]
        obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
        obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
        obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
        exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
    have hsz := hm.size.1
    have hcard := hrep.card
    have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
      change v.length ≤ L - 1 + 1 - t; omega)
    have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL ((pr Z).map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL ((pr Z).map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
      intro p hpM
      have h2 := hchk p hpM
      simp only [chk, frc_eq, st_eq] at h2
      have h3 := anySub_false h2 v hsub
      simp only [startv, topF_eq, bR, hcov, hble, Bool.cond_true] at h3
      exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) (pos_eq t) rfl rfl h3
    obtain ⟨p0, hp0M⟩ := List.exists_mem_of_ne_nil M hM
    have hlen := (topC_succ (all p0 hp0M)).1
    exact ⟨by rw [hcard]; exact hlen, topC_sound X hlen all hst k (by omega) hm⟩
  obtain ⟨S', hS', hm', hfm⟩ := hsym k S hSW hm (key S hSW hm).1
  exact (key S' hS' hm').2 hfm
def PIK : ℕ := 0x22ec5c8b516e2c4598af1562b45089f14a274548a71462644d89712a2444988d11e22c1382304a07c1087f09610c2684707e1042483d08a0cc1883705e0ec1c8350560b42c81b02e0640a84f0f21f4388770da1ec398750de18c308670be1ac348650b61741488910a21c4088303a15c298550a204c0380f01a01401811016024007f6fe9febf97feff9fe3f77f0fd9f3be97ccfa1f2bf07defb5f73eb7d8fa9fa3f27eafcdf8be47c6f85f13e07bef79ee3dd7b4f6debbd87b2f49e8bd47a0f59eabd379cf3de6b736e4dc1b8b6c6deda9b5b676ccda5b2b6e6dada1b1b64776d85afb606bad79dab3d676cf19cb3a75ecdd9b33466aea9d4ba7750e95d33a4744e8dd03a173ec0180afe5febe97c2f45fabd97baf35f2bc97e2fb5eabc178b8c60ec1583303608e19772ec5dabadc0abb574ae15cb7c57eb015eabe6eead95ab74798f2de4bca78ef01dfbc878af19e13be788f0de0bbc77ad89dd3b8772ed9dbb5c6b6d69ac3596a8d39a6b576a2d49a9b50698d59aab4f694d2da4b32660cc59732f686cb195b29654cf9da3b2766ec1d8b3875ceb5d5bac666d21a3347688d1596b42682cfda032864ec999232563ec698cb1e646c818eb1c630c8990b1b62cc5d8ab0f61ac3986310628c4989b11616c2984b08716e25c5387710c09ceb9e736e71cbb91720e69c9b9972ae59c7b98728e49c6b8e5dee15c1b84704ba974ae85ccb9d702dc5b6b8970ae55bcb7d6d2e45c6b756c2d95aeb596a2d55a4b4d68aad556ab154aaa596acd58ab255eac162aa754ca9560b7a6f6de1bcabc700dfdbeb7e56edd9baab4594b2164ac658eab9682ce59eb3166aa8588b0d612a4542a8151aa253ea794a295526a694ca97530a594e29d536a4948a8f520a2944a8c510a3946a8b50ca1d42a84506a0940a8048e9f922a7c4749e91ea3c4ee8e11ba744d29c933a703da9b8f7a6c3d69a939a684e2999302644bc97530a654be98d3125c4268492ca1642a9590820f4a678d289e63ca938f09e04967a0f4a484fe9193ea444869091aa404668f93ca784769ed1ca764ea8d920a3447e8c918a3045e8a51422c4568a91722d44e8991222544688910a1e4348810ea1c43687d0ca1842e9612ba144b696908a554a883906a0c416828ef2083ae759029da3b2808ee2003a8748e99d13a073ce61c939c72ce51cd39071ce31f04da7b9379ec4d67a924a4a3ce941279e44a478926a4c3be824eea013b6811019d840e818ea9ff3fa7f8fe1fb3f47dcfa1f93ec7d4fc1f33e47c4e29c43866f8df9c0382708de9ab3766a4d41b825e6d89692c36642cd890d35e424841ac3786a8dd1b934e680cf9a4346688d09a634a6789419c2466689519824c494ca9042066487f0fd31e418c6901200628af9882c4584c295d2b86086c0d72fe368be8d51a85e85117814a290ba8a72e62804f09f13a2704c89612826c4c097134254498922c661cc3160312578c21832b6554ac9532a4558ad1542b055ca88cd29e33ca68cb296344691481145184688c2862204308710a2104087e0f820c4007f1041f43d87a26623c4813036e4b8da9b42566649499d24e65ccb1243364888d91a23e4788e91c2424808c8f522e3ec7d1141e63c8888f81ee438d810c364428d71ad20e63882994326408c618b1fe644c80fc22c4547c91021e3d88c0f4226448788f01de3b0768ee1d63a8740e91ce398718df1ca388708e01c83786e8dc1b65f86c981300358be17b1a6524a50d029c338a80cc298328620c8184304628c918631c630c00c418c5e8760ea2e83c0b80e61c4390700de1b03486e0d61a8368680ce198328a82e8298bb9761465e4509722e05c4b796e2d459cb69692d05b0b316b2ca59048931264238a294411651c449422805049f93e2744dc9e9392704f09b13b26a4d03c8b90ee2f05d87416e2d45b0b41662c0568b215e2b8588ac1562a85486417c2fc308600be1382604d09612823844092118228480861042104009e1782e05d0b61682b8540b21582a8580a61442905007c0fc1e03d0740ec1c03906c0dc1a0350640cc1803105c0bc1602d0540ac1402904c09c1202504408c1002103c07c0e81b0380680c01902c05c0a01502404c0801101c03c0600d01402c0400900c01c0200500400c00001
def pi0 (i : ℕ) : ℕ := Nat.mod (Nat.shiftRight PIK (Nat.mul 11 i)) 2048
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pi0_ok : ∀ i < NN, pi0 i < NN ∧ pi0 (pi0 i) = i := by decide +kernel
def pi (i : ℕ) : ℕ := if i < NN then pi0 i else if i < NN + NN then NN + pi0 (i - NN) else i
lemma pi_pi (i : ℕ) : pi (pi i) = i := by
  unfold pi
  by_cases h1 : i < NN
  · have := pi0_ok i h1; simp [h1, this]
  · by_cases h2 : i < NN + NN
    · have := pi0_ok (i - NN) (by omega)
      simp [h1, h2, this]; omega
    · simp [h1, h2]
lemma pi_lt {i : ℕ} (h : i < NN + NN) : pi i < NN + NN := by
  unfold pi
  by_cases h1 : i < NN
  · have := pi0_ok i h1; simp [h1]; omega
  · have := pi0_ok (i - NN) (by omega); simp [h1, h]; omega
def rho (w : ℕ) : ℕ := (∑ i ∈ Finset.range (NN + NN), (w.testBit (pi i)).toNat * 2 ^ i) + 2 ^ (NN + NN) * (w >>> (NN + NN))
lemma bits_sum (n : ℕ) (f : ℕ → Bool) : (∑ i ∈ Finset.range n, (f i).toNat * 2 ^ i) < 2 ^ n ∧
    ∀ j, (∑ i ∈ Finset.range n, (f i).toNat * 2 ^ i).testBit j = (decide (j < n) && f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_comm, Nat.mul_comm]
    have hb : (f n).toNat ≤ 1 := by cases f n <;> simp
    constructor
    · have := ih.1
      have h2 : 2 ^ n * (f n).toNat ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ hb
      rw [pow_succ]; omega
    · intro j
      rw [Nat.testBit_two_pow_mul_add _ ih.1, ih.2]
      split_ifs with h
      · simp [h, show j < n + 1 by omega]
      · rcases Nat.eq_or_lt_of_le (not_lt.1 h) with rfl | h2
        · cases f n <;> simp
        · have : (f n).toNat.testBit (j - n) = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hb (Nat.one_lt_two_pow (by omega)))
          rw [this]; simp [show ¬ j < n + 1 by omega]
lemma rho_bit (w i : ℕ) : (rho w).testBit i = w.testBit (pi i) := by
  unfold rho
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ (bits_sum _ _).1]
  split_ifs with h
  · rw [(bits_sum _ _).2]; simp [h]
  · rw [Nat.testBit_shiftRight, show NN + NN + (i - (NN + NN)) = i by omega]
    unfold pi; simp [h, show ¬ i < NN by omega]
lemma rho_ext {w w' : ℕ} (h : ∀ i, w.testBit (pi i) = w'.testBit i) : rho w = w' :=
  Nat.eq_of_testBit_eq fun i => by rw [rho_bit, h]
lemma rho_phi (w : ℕ) : rho (rho w) = w := rho_ext fun i => by rw [rho_bit, pi_pi]
lemma rho_op (d : Bool) (a b : ℕ) : rho (op d a b) = op d (rho a) (rho b) :=
  rho_ext fun i => by simp only [op_bit, rho_bit]
lemma rho_xor (a b : ℕ) : rho (a ^^^ b) = rho a ^^^ rho b := rho_ext fun i => by simp only [Nat.testBit_xor, rho_bit]
lemma rho_and (a b : ℕ) : rho (a &&& b) = rho a &&& rho b := rho_ext fun i => by simp only [Nat.testBit_and, rho_bit]
lemma rho_zero : rho 0 = 0 := rho_ext fun i => by simp
lemma rho_inj {a b : ℕ} (h : rho a = rho b) : a = b := by rw [← rho_phi a, h, rho_phi]
def eqv (w w' : ℕ) : Bool := decide (w < 2 ^ (NN + NN)) && decide (w' < 2 ^ (NN + NN)) && (List.range (NN + NN)).all (fun i => w.testBit (pi i) == w'.testBit i)
lemma eqv_phi {w w' : ℕ} (h : eqv w w' = true) : rho w = w' := by
  simp only [eqv, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine rho_ext fun i => ?_
  by_cases hi : i < NN + NN
  · exact h.2 i hi
  · have : pi i = i := by unfold pi; simp [hi, show ¬ i < NN by omega]
    have hp : 2 ^ (NN + NN) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [this, Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]
lemma Sol.rho {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) : Sol (rho m) (rho T) q (L_meta_1674.rho '' S) := by
  induction h with
  | done h => exact .done ⟨_, h, rfl⟩
  | un h _ ih =>
    refine .un (Set.mem_image_of_mem _ h) ?_
    rw [← rho_xor, ← Set.image_insert_eq]; exact ih
  | @bi _ _ d _ _ h1 h2 _ ih =>
    refine .bi (d := d) (Set.mem_image_of_mem _ h1) (Set.mem_image_of_mem _ h2) ?_
    rw [← rho_op, ← Set.image_insert_eq]; exact ih
lemma Live.rho {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : Live (rho m) (rho T) k t (S.image L_meta_1674.rho) := by
  induction h with
  | stop => rw [Finset.image_singleton]; exact .stop
  | un _ ih =>
    rw [Finset.image_insert, rho_xor] at ih
    rw [Finset.image_insert]; exact .un ih
  | bi hab _ ih =>
    rw [Finset.image_insert, rho_op] at ih
    rw [Finset.image_insert, Finset.image_insert]
    exact .bi (fun e => hab (rho_inj e)) ih
lemma Un.rho {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : Un (rho m) (rho a) (S.image L_meta_1674.rho) (S'.image L_meta_1674.rho) := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨U.image _, by rw [Finset.image_insert], by rw [Finset.image_insert, rho_xor]⟩
lemma Bi.rho {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') : Bi d (rho a) (rho b) (S.image L_meta_1674.rho) (S'.image L_meta_1674.rho) := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  exact ⟨fun e => hab (rho_inj e), U.image _, by rw [Finset.image_insert, Finset.image_insert], by rw [Finset.image_insert, rho_op]⟩
def rawS : List ℕ := (([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ).map (fun i => rawP.getD i 0)) ++ [rawP.getD 0 0 ||| rawP.getD 2 0]
def rawT : List (ℕ × ℕ) := rawL.zip rawS
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_ok : rawT.all (fun p => eqv p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_fst : rawT.map Prod.fst = rawL := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_snd : rawT.all (fun p => rawL.contains p.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_phi : eqv TG TG = true := by decide +kernel
lemma raw_phi {w : ℕ} (hw : w ∈ rawL) : ∃ p ∈ rawT, p.1 = w ∧ rho w = p.2 ∧ p.2 ∈ rawL := by
  rw [← rawT_fst, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  refine ⟨p, hp, rfl, eqv_phi (List.all_eq_true.1 rawT_ok p hp), ?_⟩
  simpa using List.all_eq_true.1 rawT_snd p hp
lemma WZ_phi {Z Z' : ℕ} (h : rho (mz Z') = mz Z) {x : ℕ} (hx : x ∈ WZ Z') : rho x ∈ WZ Z := by
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨p, _, _, e, hp⟩ := raw_phi hw
  exact ⟨p.2, hp, by rw [rho_and, h, e]⟩
lemma tz_phi {Z Z' : ℕ} (h : rho (mz Z') = mz Z) : rho (tz Z') = tz Z := by
  simp only [tz, nl]; rw [rho_and, h, eqv_phi TG_phi]
theorem imp_sym {Z Z' L : ℕ} (h : Imp Z L) (he : eqv (mz Z') (mz Z) = true) : Imp Z' L := by
  intro q hq hs
  have h' := eqv_phi he
  have h2 := hs.rho
  rw [h', tz_phi h'] at h2
  refine h q hq (h2.mono le_rfl ?_)
  rintro _ ⟨x, hx | hx, rfl⟩
  · exact Or.inl (WZ_phi h' hx)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [rho_zero]; exact Or.inr (Set.mem_insert _ _)
    · rw [h']; exact Or.inr (Set.mem_insert_of_mem _ rfl)
def kOk (M : List (ℕ × ℕ)) : Bool := rawT.all (fun p => (M.any (fun x => hb x.2 p.1) || M.any (fun x => hb x.2 p.2)) &&
  rawT.all (fun q => Nat.beq p.1 q.1 || M.any (fun x => hb x.1 (p.1 + q.1)) || M.any (fun x => hb x.1 (p.2 + q.2))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m0_full : rawL.all (fun w => Nat.beq (Nat.land w (mz 0)) w) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m0_phi : eqv (mz 0) (mz 0) = true := by decide +kernel
lemma WZ0 {x : ℕ} (hx : x ∈ WZ 0) : x ∈ rawL := by
  obtain ⟨w, hw, rfl⟩ := hx
  have := List.all_eq_true.1 m0_full w hw
  rw [Nat.beq_eq, nl] at this; rwa [this]
lemma sym0 {M : List (ℕ × ℕ)} (hM : kOk M = true) (k t : ℕ) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ WZ 0) (hm : Min (mz 0) (tz 0) k t S)
    (hc : 2 ≤ S.card) : ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ 0 ∧ Min (mz 0) (tz 0) k t S' ∧ FM (mz 0) (tz 0) k t S' (KP M) (KN M) := by
  have pm := eqv_phi m0_phi
  have pt := tz_phi pm
  have hN : ∀ a ∈ S, KN M a ∨ KN M (rho a) := by
    intro a ha
    obtain ⟨p, hp, e1, e2, _⟩ := raw_phi (WZ0 (hS ha))
    have := List.all_eq_true.1 hM p hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at this
    rw [e2, ← e1]; exact this.1.imp id id
  have hP : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → KP M a b ∨ KP M (rho a) (rho b) := by
    intro a ha b hb hab
    obtain ⟨p, hp, e1, e2, _⟩ := raw_phi (WZ0 (hS ha))
    obtain ⟨q, hq, f1, f2, _⟩ := raw_phi (WZ0 (hS hb))
    have := List.all_eq_true.1 hM p hp
    simp only [Bool.and_eq_true] at this
    have := List.all_eq_true.1 this.2 q hq
    simp only [Bool.or_eq_true, List.any_eq_true] at this
    rw [e2, f2, ← e1, ← f1]
    rcases this with (h | h) | h
    · exact absurd (e1.symm.trans ((Nat.eq_of_beq_eq_true h).trans f1)) hab
    · exact Or.inl h
    · exact Or.inr h
  have hS' : ((S.image L_meta_1674.rho : Finset ℕ) : Set ℕ) ⊆ WZ 0 := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact WZ_phi pm (hS hy)
  have hm' : Min (mz 0) (tz 0) k t (S.image L_meta_1674.rho) := by
    have h1 := hm.1.rho
    rw [pm, pt] at h1
    refine ⟨h1, fun q hq hs => hm.2 q hq ?_⟩
    have h2 := hs.rho
    rw [pm, pt] at h2
    refine h2.mono le_rfl ?_
    rintro _ ⟨x, hx | hx, rfl⟩
    · simp only [Finset.coe_image, Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [rho_phi]; exact Or.inl hy
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx, rho_zero]; exact Or.inr (Set.mem_insert _ _)
      · rw [hx, pm]; exact Or.inr (Set.mem_insert_of_mem _ rfl)
  rcases first_move k t S hm hc with ⟨k0, d, a, b, S1, e, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, e, e', hu, hne, hu', hb, hl⟩
  · rcases hP a hb.sub.1 b hb.sub.2.1 hb.1 with h | h
    · exact ⟨S, hS, hm, Or.inl ⟨k0, d, a, b, S1, e, h, hb, hl⟩⟩
    · refine ⟨_, hS', hm', Or.inl ⟨k0, d, rho a, rho b, _, e, h, hb.rho, ?_⟩⟩
      have := hl.rho; rwa [pm, pt] at this
  · rcases hN a hu.sub.1 with h | h
    · exact ⟨S, hS, hm, Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', h, hu, hb, hl⟩)⟩
    · have h1 := hu.rho; rw [pm] at h1
      have h2 := hb.rho; rw [rho_xor, pm] at h2
      have h3 := hl.rho; rw [pm, pt] at h3
      exact ⟨_, hS', hm', Or.inr (Or.inl ⟨k0, t0, rho a, d, rho c, _, _, e, e', h, h1, h2, h3⟩)⟩
  · rcases hN a hu.sub.1 with h | h
    · exact ⟨S, hS, hm, Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h, hu, hne, hu', hb, hl⟩)⟩
    · have h1 := hu.rho; rw [pm] at h1
      have h1' := hu'.rho; rw [pm] at h1'
      have h2 := hb.rho; rw [rho_xor, rho_xor, pm] at h2
      have h3 := hl.rho; rw [pm, pt] at h3
      refine ⟨_, hS', hm', Or.inr (Or.inr ⟨k0, t0, rho a, rho a', d, _, _, _, e, e', h, h1, fun e => hne ?_, h1', h2, h3⟩)⟩
      apply rho_inj; rw [e, rho_xor, pm]
def FF : ℕ := 2 ^ MM - 1
lemma hbF (x : ℕ) : hb FF x = true := by
  have h : x % MM < MM := Nat.mod_lt _ (by decide)
  have h2 : FF.testBit (x % MM) = true := by rw [FF, Nat.testBit_two_pow_sub_one]; simpa using h
  unfold hb
  rw [Nat.beq_eq]
  change (FF >>> (x % MM)) &&& 1 = 1
  rw [Nat.testBit] at h2
  rw [Nat.and_one_is_mod]
  simp only [Nat.one_and_eq_mod_two, bne_iff_ne, ne_eq] at h2
  omega
lemma FM_mono {m T k t : ℕ} {S : Finset ℕ} {A A' : ℕ → ℕ → Prop} {B B' : ℕ → Prop} (h : FM m T k t S A B) (h1 : ∀ x y, A x y → A' x y)
    (h2 : ∀ x, B x → B' x) : FM m T k t S A' B' := by
  rcases h with ⟨k0, d, a, b, S1, e, q, h⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', q, h⟩ | ⟨k0, t0, a, a', d, S1, S2, S3, e, e', q, h⟩
  · exact Or.inl ⟨k0, d, a, b, S1, e, h1 _ _ q, h⟩
  · exact Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', h2 _ q, h⟩)
  · exact Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h2 _ q, h⟩)
theorem imp_full {Z L : ℕ} (hp : pOk Z = true) (hL : L ≤ 15) (hI : ∀ e ∈ pr Z, Imp e.1 e.2)
    (hb : (∃ e ∈ pr Z, L ≤ e.2) ∨ ∀ t < L, chk Z (L - 1) t FF FF = false) : Imp Z L := by
  refine imp_of hp hL hI (hb.imp id fun h t ht => ⟨[(FF, FF)], by simp, fun p hp => ?_, fun k S hS hm hc => ⟨S, hS, hm, ?_⟩⟩)
  · simp only [List.mem_singleton] at hp; subst hp; exact h t ht
  · exact FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)
noncomputable def okT (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk Z (L - 1) t FF FF)
noncomputable def okE (e : ℕ × ℕ) : Bool := pOk e.1 && Nat.ble e.2 15 && ((pr e.1).any (fun x => Nat.ble e.2 x.2) || okT e.1 e.2 (List.range e.2))
def kFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r) && M.any (fun p => hb p.2 r))
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
lemma sym_full {Z t : ℕ} {M : List (ℕ × ℕ)} (hM : kFull M = true) (k : ℕ) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ WZ Z) (hm : Min (mz Z) (tz Z) k t S)
    (hc : 2 ≤ S.card) : ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ Z ∧ Min (mz Z) (tz Z) k t S' ∧ FM (mz Z) (tz Z) k t S' (KP M) (KN M) := by
  have h : ∀ x, (∃ p ∈ M, hb p.1 x = true) ∧ ∃ p ∈ M, hb p.2 x = true := by
    intro x
    have := List.all_eq_true.1 hM (x % MM) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
    simp only [Bool.and_eq_true, List.any_eq_true, ← hb_mod] at this
    exact this
  exact ⟨S, hS, hm, FM_mono (FM_of hm hc) (fun x y _ => (h (x + y)).1) (fun x _ => (h x).2)⟩
lemma imp_okE {e : ℕ × ℕ} (h : okE e = true) (hI : ∀ e' ∈ pr e.1, Imp e'.1 e'.2) : Imp e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_full h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) id)
def tab3 : List (ℕ × ℕ) := [(19,8), (25,8), (28,8), (49,8), (67,8), (70,8), (81,8), (82,8), (88,7), (134,8), (140,8), (145,8), (148,8), (152,7), (161,8), (164,8), (176,7), (194,8), (196,8), (208,7), (224,7), (280,7), (322,8), (328,7), (336,7), (352,7), (416,7), (448,7), (7,7), (14,7), (21,7), (26,7), (35,7), (56,6), (74,7), (84,7), (98,7), (112,6), (133,7), (146,7), (162,7), (168,6), (193,7), (200,6), (268,7), (273,7), (289,7), (296,6), (321,7), (324,7), (388,7), (400,6), (22,6), (76,6), (97,6), (131,6), (304,5), (392,5), (11,5), (13,5), (37,5), (38,5), (41,5), (42,5), (44,5), (50,5), (52,5), (69,5), (73,5), (100,5), (104,5), (137,5), (138,5), (259,5), (261,5), (262,5), (265,5), (266,5), (274,5), (276,5), (290,5), (292,5), (385,5), (386,5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3all : tab3.all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr3 : tab3.all (fun e => (pr e.1).isEmpty) = true := by decide +kernel
theorem i3 : ∀ e ∈ tab3, Imp e.1 e.2 := fun e he => imp_okE (List.all_eq_true.1 c3all e he) fun x hx => by
  have := List.all_eq_true.1 pr3 e he
  rw [List.isEmpty_iff] at this; rw [this] at hx; simp at hx
def tab2 : List (ℕ × ℕ) := [(17,11), (24,10), (66,11), (80,10), (132,11), (144,10), (160,10), (192,10), (320,10), (3,9), (6,9), (12,9), (18,9), (20,9), (33,9), (48,8), (65,9), (68,9), (72,9), (96,9), (129,9), (130,9), (136,8), (264,8), (272,8), (288,8), (384,8), (5,8), (9,8), (10,8), (34,8), (36,8), (40,8), (257,8), (258,8), (260,8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c17 : okE (17, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c24 : okE (24, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c66 : okE (66, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c80 : okE (80, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c144 : okE (144, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c320 : okE (320, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3 : okE (3, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c12 : okE (12, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c18 : okE (18, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c20 : okE (20, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c48 : okE (48, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c65 : okE (65, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c72 : okE (72, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c264 : okE (264, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c272 : okE (272, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5 : okE (5, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c9 : okE (9, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c10 : okE (10, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c40 : okE (40, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c257 : okE (257, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c258 : okE (258, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr2 : tab2.all (fun e => (pr e.1).all (fun x => tab3.contains x)) = true := by decide +kernel
theorem sub2 (e : ℕ × ℕ) (he : e ∈ tab2) (x : ℕ × ℕ) (hx : x ∈ pr e.1) : Imp x.1 x.2 := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 pr2 e he) x hx
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h
  exact i3 x h
theorem imp17 : Imp 17 11 := imp_okE (e := (17, 11)) c17 (sub2 _ (by decide +kernel))
theorem imp24 : Imp 24 10 := imp_okE (e := (24, 10)) c24 (sub2 _ (by decide +kernel))
theorem imp66 : Imp 66 11 := imp_okE (e := (66, 11)) c66 (sub2 _ (by decide +kernel))
theorem imp80 : Imp 80 10 := imp_okE (e := (80, 10)) c80 (sub2 _ (by decide +kernel))
theorem imp144 : Imp 144 10 := imp_okE (e := (144, 10)) c144 (sub2 _ (by decide +kernel))
theorem imp320 : Imp 320 10 := imp_okE (e := (320, 10)) c320 (sub2 _ (by decide +kernel))
theorem imp3 : Imp 3 9 := imp_okE (e := (3, 9)) c3 (sub2 _ (by decide +kernel))
theorem imp12 : Imp 12 9 := imp_okE (e := (12, 9)) c12 (sub2 _ (by decide +kernel))
theorem imp18 : Imp 18 9 := imp_okE (e := (18, 9)) c18 (sub2 _ (by decide +kernel))
theorem imp20 : Imp 20 9 := imp_okE (e := (20, 9)) c20 (sub2 _ (by decide +kernel))
theorem imp48 : Imp 48 8 := imp_okE (e := (48, 8)) c48 (sub2 _ (by decide +kernel))
theorem imp65 : Imp 65 9 := imp_okE (e := (65, 9)) c65 (sub2 _ (by decide +kernel))
theorem imp72 : Imp 72 9 := imp_okE (e := (72, 9)) c72 (sub2 _ (by decide +kernel))
theorem imp264 : Imp 264 8 := imp_okE (e := (264, 8)) c264 (sub2 _ (by decide +kernel))
theorem imp272 : Imp 272 8 := imp_okE (e := (272, 8)) c272 (sub2 _ (by decide +kernel))
theorem imp5 : Imp 5 8 := imp_okE (e := (5, 8)) c5 (sub2 _ (by decide +kernel))
theorem imp9 : Imp 9 8 := imp_okE (e := (9, 8)) c9 (sub2 _ (by decide +kernel))
theorem imp10 : Imp 10 8 := imp_okE (e := (10, 8)) c10 (sub2 _ (by decide +kernel))
theorem imp40 : Imp 40 8 := imp_okE (e := (40, 8)) c40 (sub2 _ (by decide +kernel))
theorem imp257 : Imp 257 8 := imp_okE (e := (257, 8)) c257 (sub2 _ (by decide +kernel))
theorem imp258 : Imp 258 8 := imp_okE (e := (258, 8)) c258 (sub2 _ (by decide +kernel))
theorem imp132 : Imp 132 11 := imp_sym imp17 (by decide +kernel)
theorem imp160 : Imp 160 10 := imp_sym imp24 (by decide +kernel)
theorem imp192 : Imp 192 10 := imp_sym imp80 (by decide +kernel)
theorem imp6 : Imp 6 9 := imp_sym imp3 (by decide +kernel)
theorem imp33 : Imp 33 9 := imp_sym imp12 (by decide +kernel)
theorem imp68 : Imp 68 9 := imp_sym imp65 (by decide +kernel)
theorem imp96 : Imp 96 9 := imp_sym imp72 (by decide +kernel)
theorem imp129 : Imp 129 9 := imp_sym imp20 (by decide +kernel)
theorem imp130 : Imp 130 9 := imp_sym imp18 (by decide +kernel)
theorem imp136 : Imp 136 8 := imp_sym imp48 (by decide +kernel)
theorem imp288 : Imp 288 8 := imp_sym imp264 (by decide +kernel)
theorem imp384 : Imp 384 8 := imp_sym imp272 (by decide +kernel)
theorem imp34 : Imp 34 8 := imp_sym imp10 (by decide +kernel)
theorem imp36 : Imp 36 8 := imp_sym imp9 (by decide +kernel)
theorem imp260 : Imp 260 8 := imp_sym imp257 (by decide +kernel)
theorem i2 : ∀ e ∈ tab2, Imp e.1 e.2 := by
  intro e he
  simp only [tab2, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact imp17
  · exact imp24
  · exact imp66
  · exact imp80
  · exact imp132
  · exact imp144
  · exact imp160
  · exact imp192
  · exact imp320
  · exact imp3
  · exact imp6
  · exact imp12
  · exact imp18
  · exact imp20
  · exact imp33
  · exact imp48
  · exact imp65
  · exact imp68
  · exact imp72
  · exact imp96
  · exact imp129
  · exact imp130
  · exact imp136
  · exact imp264
  · exact imp272
  · exact imp288
  · exact imp384
  · exact imp5
  · exact imp9
  · exact imp10
  · exact imp34
  · exact imp36
  · exact imp40
  · exact imp257
  · exact imp258
  · exact imp260
def tab1 : List (ℕ × ℕ) := [(16,12), (64,13), (128,12), (1,12), (2,12), (4,12), (8,11), (32,11), (256,11)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16 : okE (16, 12) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1 : okE (1, 12) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2 : okE (2, 12) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c8 : okE (8, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c256 : okE (256, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr1 : tab1.all (fun e => (pr e.1).all (fun x => tab2.contains x || tab3.contains x)) = true := by decide +kernel
theorem sub1 (e : ℕ × ℕ) (he : e ∈ tab1) (x : ℕ × ℕ) (hx : x ∈ pr e.1) : Imp x.1 x.2 := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 pr1 e he) x hx
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h
  exact h.elim (i2 x) (i3 x)
theorem imp16 : Imp 16 12 := imp_okE (e := (16, 12)) c16 (sub1 _ (by decide +kernel))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p64 : pOk 64 = true := by decide +kernel
def G64_0 : List (ℕ × ℕ) := [(0x3ffb7b7fffefffddbdbb6b7dfdb9bffffdfffffdffff6e6ffded3f,0x3bfffffffffffffffffeffffdbdbffffdfffffffffffefffdfffff), (0x40,0x0), (0x80,0x0), (0x200,0x0), (0x1000,0x0), (0x20000,0x0), (0x10000000,0x0), (0x80000000,0x0), (0x100000000,0x0), (0x1000000000,0x0), (0x8000000000,0x0), (0x200000000000000,0x0), (0x200000000000000000000,0x0), (0x40000000000000000000000000,0x0), (0x200000000000000000000000000,0x0), (0x400000000000000000000000000,0x0), (0x4000000000000000000000000000,0x0), (0x20000000000000000000000000000,0x0), (0x2000000000000000000000000000000,0x0), (0x80000000000000000000000000000000,0x0), (0x400000000000000000000000000000000,0x0), (0x1000000000000000000000000000000000,0x0), (0x8000000000000000000000000000000000,0x0), (0x40000000000000000000000000000000000,0x0), (0x400000000000000000000000000000000000,0x0), (0x2000000000000000000000000000000000000,0x0), (0x40000000000000000000000000000000000000,0x0), (0x200000000000000000000000000000000000000,0x0), (0x2000000000000000000000000000000000000000,0x0), (0x10000000000000000000000000000000000000000000,0x0), (0x800000000000000000000000000000000000000000000000,0x0), (0x4000000000000000000000000000000000000000000000000,0x0), (0x80000000000000000000000000000000000000000000000000,0x0), (0x400000000000000000000000000000000000000000000000000,0x0), (0x0,0x200000), (0x0,0x1000000000), (0x0,0x2000000000000000000000), (0x0,0x400000000000000000000000000), (0x0,0x2000000000000000000000000000), (0x0,0x40000000000000000000000000000), (0x0,0x200000000000000000000000000000), (0x0,0x10000000000000000000000000000000000), (0x0,0x40000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g64_0 : kFull G64_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_0 : chk 64 12 0 0x3ffb7b7fffefffddbdbb6b7dfdb9bffffdfffffdffff6e6ffded3f 0x3bfffffffffffffffffeffffdbdbffffdfffffffffffefffdfffff = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_1 : chk 64 12 0 0x40 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_2 : chk 64 12 0 0x80 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_3 : chk 64 12 0 0x200 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_4 : chk 64 12 0 0x1000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_5 : chk 64 12 0 0x20000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_6 : chk 64 12 0 0x10000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_7 : chk 64 12 0 0x80000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_8 : chk 64 12 0 0x100000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_9 : chk 64 12 0 0x1000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_10 : chk 64 12 0 0x8000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_11 : chk 64 12 0 0x200000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_12 : chk 64 12 0 0x200000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_13 : chk 64 12 0 0x40000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_14 : chk 64 12 0 0x200000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_15 : chk 64 12 0 0x400000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_16 : chk 64 12 0 0x4000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_17 : chk 64 12 0 0x20000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_18 : chk 64 12 0 0x2000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_19 : chk 64 12 0 0x80000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_20 : chk 64 12 0 0x400000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_21 : chk 64 12 0 0x1000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_22 : chk 64 12 0 0x8000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_23 : chk 64 12 0 0x40000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_24 : chk 64 12 0 0x400000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_25 : chk 64 12 0 0x2000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_26 : chk 64 12 0 0x40000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_27 : chk 64 12 0 0x200000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_28 : chk 64 12 0 0x2000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_29 : chk 64 12 0 0x10000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_30 : chk 64 12 0 0x800000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_31 : chk 64 12 0 0x4000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_32 : chk 64 12 0 0x80000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_33 : chk 64 12 0 0x400000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_34 : chk 64 12 0 0x0 0x200000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_35 : chk 64 12 0 0x0 0x1000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_36 : chk 64 12 0 0x0 0x2000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_37 : chk 64 12 0 0x0 0x400000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_38 : chk 64 12 0 0x0 0x2000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_39 : chk 64 12 0 0x0 0x40000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_40 : chk 64 12 0 0x0 0x200000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_41 : chk 64 12 0 0x0 0x10000000000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_0_42 : chk 64 12 0 0x0 0x40000000000000000000000000000000000000000000000000000 = false := by decide +kernel
def G64_1 : List (ℕ × ℕ) := [(0x3ffb7b7fffefffddbdbb6b7dfdb9bffffdfffffdffff6e6ffded3f,0x3bfffffffffffffffffeffffdbdbffffdfffffffffffefffdfffff), (0x40,0x0), (0x80,0x0), (0x200,0x0), (0x1000,0x0), (0x20000,0x0), (0x10000000,0x0), (0x80000000,0x0), (0x100000000,0x0), (0x1000000000,0x0), (0x8000000000,0x0), (0x200000000000000,0x0), (0x200000000000000000000,0x0), (0x40000000000000000000000000,0x0), (0x200000000000000000000000000,0x0), (0x400000000000000000000000000,0x0), (0x4000000000000000000000000000,0x0), (0x20000000000000000000000000000,0x0), (0x2000000000000000000000000000000,0x0), (0x80000000000000000000000000000000,0x0), (0x400000000000000000000000000000000,0x0), (0x1000000000000000000000000000000000,0x0), (0x8000000000000000000000000000000000,0x0), (0x40000000000000000000000000000000000,0x0), (0x400000000000000000000000000000000000,0x0), (0x2000000000000000000000000000000000000,0x0), (0x40000000000000000000000000000000000000,0x0), (0x200000000000000000000000000000000000000,0x0), (0x2000000000000000000000000000000000000000,0x0), (0x10000000000000000000000000000000000000000000,0x0), (0x800000000000000000000000000000000000000000000000,0x0), (0x4000000000000000000000000000000000000000000000000,0x0), (0x80000000000000000000000000000000000000000000000000,0x0), (0x400000000000000000000000000000000000000000000000000,0x0), (0x0,0x200000), (0x0,0x1000000000), (0x0,0x2000000000000000000000), (0x0,0x400000000000000000000000000), (0x0,0x2000000000000000000000000000), (0x0,0x40000000000000000000000000000), (0x0,0x200000000000000000000000000000), (0x0,0x10000000000000000000000000000000000), (0x0,0x40000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g64_1 : kFull G64_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_0 : chk 64 12 1 0x3ffb7b7fffefffddbdbb6b7dfdb9bffffdfffffdffff6e6ffded3f 0x3bfffffffffffffffffeffffdbdbffffdfffffffffffefffdfffff = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_1 : chk 64 12 1 0x40 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_2 : chk 64 12 1 0x80 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_3 : chk 64 12 1 0x200 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_4 : chk 64 12 1 0x1000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_5 : chk 64 12 1 0x20000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_6 : chk 64 12 1 0x10000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_7 : chk 64 12 1 0x80000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_8 : chk 64 12 1 0x100000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_9 : chk 64 12 1 0x1000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_10 : chk 64 12 1 0x8000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_11 : chk 64 12 1 0x200000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_12 : chk 64 12 1 0x200000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_13 : chk 64 12 1 0x40000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_14 : chk 64 12 1 0x200000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_15 : chk 64 12 1 0x400000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_16 : chk 64 12 1 0x4000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_17 : chk 64 12 1 0x20000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_18 : chk 64 12 1 0x2000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_19 : chk 64 12 1 0x80000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_20 : chk 64 12 1 0x400000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_21 : chk 64 12 1 0x1000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_22 : chk 64 12 1 0x8000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_23 : chk 64 12 1 0x40000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_24 : chk 64 12 1 0x400000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_25 : chk 64 12 1 0x2000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_26 : chk 64 12 1 0x40000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_27 : chk 64 12 1 0x200000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_28 : chk 64 12 1 0x2000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_29 : chk 64 12 1 0x10000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_30 : chk 64 12 1 0x800000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_31 : chk 64 12 1 0x4000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_32 : chk 64 12 1 0x80000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_33 : chk 64 12 1 0x400000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_34 : chk 64 12 1 0x0 0x200000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_35 : chk 64 12 1 0x0 0x1000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_36 : chk 64 12 1 0x0 0x2000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_37 : chk 64 12 1 0x0 0x400000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_38 : chk 64 12 1 0x0 0x2000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_39 : chk 64 12 1 0x0 0x40000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_40 : chk 64 12 1 0x0 0x200000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_41 : chk 64 12 1 0x0 0x10000000000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64_1_42 : chk 64 12 1 0x0 0x40000000000000000000000000000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v64rest : okT 64 13 [2,3,4,5,6,7,8,9,10,11,12] = true := by decide +kernel
theorem imp64 : Imp 64 13 := by
  refine imp_of p64 (by decide) (sub1 (64, 13) (by decide +kernel)) (Or.inr fun t ht => ?_)
  by_cases h : t < 2
  · interval_cases t
    · refine ⟨G64_0, by simp [G64_0], fun p hp => ?_, fun k S hS hm hc => sym_full g64_0 k S hS hm hc⟩
      simp only [G64_0, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact v64_0_0
      · exact v64_0_1
      · exact v64_0_2
      · exact v64_0_3
      · exact v64_0_4
      · exact v64_0_5
      · exact v64_0_6
      · exact v64_0_7
      · exact v64_0_8
      · exact v64_0_9
      · exact v64_0_10
      · exact v64_0_11
      · exact v64_0_12
      · exact v64_0_13
      · exact v64_0_14
      · exact v64_0_15
      · exact v64_0_16
      · exact v64_0_17
      · exact v64_0_18
      · exact v64_0_19
      · exact v64_0_20
      · exact v64_0_21
      · exact v64_0_22
      · exact v64_0_23
      · exact v64_0_24
      · exact v64_0_25
      · exact v64_0_26
      · exact v64_0_27
      · exact v64_0_28
      · exact v64_0_29
      · exact v64_0_30
      · exact v64_0_31
      · exact v64_0_32
      · exact v64_0_33
      · exact v64_0_34
      · exact v64_0_35
      · exact v64_0_36
      · exact v64_0_37
      · exact v64_0_38
      · exact v64_0_39
      · exact v64_0_40
      · exact v64_0_41
      · exact v64_0_42
    · refine ⟨G64_1, by simp [G64_1], fun p hp => ?_, fun k S hS hm hc => sym_full g64_1 k S hS hm hc⟩
      simp only [G64_1, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact v64_1_0
      · exact v64_1_1
      · exact v64_1_2
      · exact v64_1_3
      · exact v64_1_4
      · exact v64_1_5
      · exact v64_1_6
      · exact v64_1_7
      · exact v64_1_8
      · exact v64_1_9
      · exact v64_1_10
      · exact v64_1_11
      · exact v64_1_12
      · exact v64_1_13
      · exact v64_1_14
      · exact v64_1_15
      · exact v64_1_16
      · exact v64_1_17
      · exact v64_1_18
      · exact v64_1_19
      · exact v64_1_20
      · exact v64_1_21
      · exact v64_1_22
      · exact v64_1_23
      · exact v64_1_24
      · exact v64_1_25
      · exact v64_1_26
      · exact v64_1_27
      · exact v64_1_28
      · exact v64_1_29
      · exact v64_1_30
      · exact v64_1_31
      · exact v64_1_32
      · exact v64_1_33
      · exact v64_1_34
      · exact v64_1_35
      · exact v64_1_36
      · exact v64_1_37
      · exact v64_1_38
      · exact v64_1_39
      · exact v64_1_40
      · exact v64_1_41
      · exact v64_1_42
  · refine ⟨[(FF, FF)], by simp, fun p hp => ?_, fun k S hS hm hc => ⟨S, hS, hm, ?_⟩⟩
    · simp only [List.mem_singleton] at hp; subst hp
      have h := List.all_eq_true.1 v64rest t (by simp; omega)
      rwa [Bool.not_eq_true'] at h
    · exact FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)
theorem imp1 : Imp 1 12 := imp_okE (e := (1, 12)) c1 (sub1 _ (by decide +kernel))
theorem imp2 : Imp 2 12 := imp_okE (e := (2, 12)) c2 (sub1 _ (by decide +kernel))
theorem imp8 : Imp 8 11 := imp_okE (e := (8, 11)) c8 (sub1 _ (by decide +kernel))
theorem imp256 : Imp 256 11 := imp_okE (e := (256, 11)) c256 (sub1 _ (by decide +kernel))
theorem imp128 : Imp 128 12 := imp_sym imp16 (by decide +kernel)
theorem imp4 : Imp 4 12 := imp_sym imp1 (by decide +kernel)
theorem imp32 : Imp 32 11 := imp_sym imp8 (by decide +kernel)
theorem i1 : ∀ e ∈ tab1, Imp e.1 e.2 := by
  intro e he
  simp only [tab1, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact imp16
  · exact imp64
  · exact imp128
  · exact imp1
  · exact imp2
  · exact imp4
  · exact imp8
  · exact imp32
  · exact imp256
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr0 : (pr 0).all (fun x => tab1.contains x || tab2.contains x || tab3.contains x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0 : pOk 0 = true := by decide +kernel
def M0 : List (ℕ × ℕ) := [(0x4, 0x1020000000000000001008080000020000040), (0x8, 0x0), (0x80, 0x0), (0x400, 0x0), (0x1000, 0x0), (0x8000, 0x0), (0x800000000, 0x0), (0x2000000000000000, 0x0), (0x80000000000000000, 0x0), (0x20000000000000000000, 0x0), (0x1000000000000000000000, 0x0), (0x100000000000000000000000, 0x0), (0x1000000000000000000000000, 0x0), (0x20000000000000000000000000, 0x0), (0x400000000000000000000000000, 0x0), (0x20000000000000000000000000000, 0x0), (0x400000000000000000000000000000, 0x0), (0x80000000000000000000000000000000, 0x0), (0x8000000000000000000000000000000000, 0x0), (0x10000000000000000000000000000000000000000, 0x0), (0x400000000000000000000000000000000000000000, 0x0), (0x8000000000000000000000000000000000000000000000000, 0x0), (0x100000000000000000000000000000000000000000000000000, 0x0), (0x20000000000000000000000000000000000000000000000000000, 0x0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k0 : kOk M0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_0 : chk 0 14 0 0x4 0x1020000000000000001008080000020000040 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_1 : chk 0 14 0 0x8 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_2 : chk 0 14 0 0x80 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_3 : chk 0 14 0 0x400 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_4 : chk 0 14 0 0x1000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_5 : chk 0 14 0 0x8000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_6 : chk 0 14 0 0x800000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_7 : chk 0 14 0 0x2000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_8 : chk 0 14 0 0x80000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_9 : chk 0 14 0 0x20000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_10 : chk 0 14 0 0x1000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_11 : chk 0 14 0 0x100000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_12 : chk 0 14 0 0x1000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_13 : chk 0 14 0 0x20000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_14 : chk 0 14 0 0x400000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_15 : chk 0 14 0 0x20000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_16 : chk 0 14 0 0x400000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_17 : chk 0 14 0 0x80000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_18 : chk 0 14 0 0x8000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_19 : chk 0 14 0 0x10000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_20 : chk 0 14 0 0x400000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_21 : chk 0 14 0 0x8000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_22 : chk 0 14 0 0x100000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_23 : chk 0 14 0 0x20000000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
def M1 : List (ℕ × ℕ) := [(0x4, 0x0), (0x8, 0x0), (0x80, 0x0), (0x400, 0x0), (0x1000, 0x0), (0x8000, 0x0), (0x800000000, 0x0), (0x2000000000000000, 0x0), (0x80000000000000000, 0x0), (0x20000000000000000000, 0x0), (0x1000000000000000000000, 0x0), (0x100000000000000000000000, 0x0), (0x1000000000000000000000000, 0x0), (0x20000000000000000000000000, 0x0), (0x400000000000000000000000000, 0x0), (0x20000000000000000000000000000, 0x0), (0x400000000000000000000000000000, 0x0), (0x80000000000000000000000000000000, 0x0), (0x8000000000000000000000000000000000, 0x0), (0x10000000000000000000000000000000000000000, 0x0), (0x400000000000000000000000000000000000000000, 0x0), (0x8000000000000000000000000000000000000000000000000, 0x0), (0x100000000000000000000000000000000000000000000000000, 0x0), (0x20000000000000000000000000000000000000000000000000000, 0x0), (0x0, 0x1020000000000000001008080000020000040)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k1 : kOk M1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_0 : chk 0 14 1 0x4 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_1 : chk 0 14 1 0x8 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_2 : chk 0 14 1 0x80 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_3 : chk 0 14 1 0x400 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_4 : chk 0 14 1 0x1000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_5 : chk 0 14 1 0x8000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_6 : chk 0 14 1 0x800000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_7 : chk 0 14 1 0x2000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_8 : chk 0 14 1 0x80000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_9 : chk 0 14 1 0x20000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_10 : chk 0 14 1 0x1000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_11 : chk 0 14 1 0x100000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_12 : chk 0 14 1 0x1000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_13 : chk 0 14 1 0x20000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_14 : chk 0 14 1 0x400000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_15 : chk 0 14 1 0x20000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_16 : chk 0 14 1 0x400000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_17 : chk 0 14 1 0x80000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_18 : chk 0 14 1 0x8000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_19 : chk 0 14 1 0x10000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_20 : chk 0 14 1 0x400000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_21 : chk 0 14 1 0x8000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_22 : chk 0 14 1 0x100000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_23 : chk 0 14 1 0x20000000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_24 : chk 0 14 1 0x0 0x1020000000000000001008080000020000040 = false := by decide +kernel
def M2 : List (ℕ × ℕ) := [(0x4, 0x0), (0x8, 0x0), (0x80, 0x0), (0x400, 0x0), (0x1000, 0x0), (0x8000, 0x0), (0x800000000, 0x0), (0x2000000000000000, 0x0), (0x80000000000000000, 0x0), (0x20000000000000000000, 0x0), (0x1000000000000000000000, 0x0), (0x100000000000000000000000, 0x0), (0x1000000000000000000000000, 0x0), (0x20000000000000000000000000, 0x0), (0x400000000000000000000000000, 0x0), (0x20000000000000000000000000000, 0x0), (0x400000000000000000000000000000, 0x0), (0x80000000000000000000000000000000, 0x0), (0x8000000000000000000000000000000000, 0x0), (0x10000000000000000000000000000000000000000, 0x0), (0x400000000000000000000000000000000000000000, 0x0), (0x8000000000000000000000000000000000000000000000000, 0x0), (0x100000000000000000000000000000000000000000000000000, 0x0), (0x20000000000000000000000000000000000000000000000000000, 0x0), (0x0, 0x1020000000000000001008080000020000040)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k2 : kOk M2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_0 : chk 0 14 2 0x4 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_1 : chk 0 14 2 0x8 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_2 : chk 0 14 2 0x80 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_3 : chk 0 14 2 0x400 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_4 : chk 0 14 2 0x1000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_5 : chk 0 14 2 0x8000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_6 : chk 0 14 2 0x800000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_7 : chk 0 14 2 0x2000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_8 : chk 0 14 2 0x80000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_9 : chk 0 14 2 0x20000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_10 : chk 0 14 2 0x1000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_11 : chk 0 14 2 0x100000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_12 : chk 0 14 2 0x1000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_13 : chk 0 14 2 0x20000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_14 : chk 0 14 2 0x400000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_15 : chk 0 14 2 0x20000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_16 : chk 0 14 2 0x400000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_17 : chk 0 14 2 0x80000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_18 : chk 0 14 2 0x8000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_19 : chk 0 14 2 0x10000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_20 : chk 0 14 2 0x400000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_21 : chk 0 14 2 0x8000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_22 : chk 0 14 2 0x100000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_23 : chk 0 14 2 0x20000000000000000000000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_24 : chk 0 14 2 0x0 0x1020000000000000001008080000020000040 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r_r : okT 0 15 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem i0 : Imp 0 15 := by
  refine imp_of p0 le_rfl (fun x hx => ?_) (Or.inr fun t ht => ?_)
  · have := List.all_eq_true.1 pr0 x hx
    rw [Bool.or_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem, List.contains_iff_mem] at this
    exact this.elim (fun h => h.elim (i1 x) (i2 x)) (i3 x)
  by_cases h3 : t < 3
  · interval_cases t
    · refine ⟨M0, by simp [M0], fun p hp => ?_, fun k S => sym0 k0 k 0 S⟩
      simp only [M0, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact r0_0
      · exact r0_1
      · exact r0_2
      · exact r0_3
      · exact r0_4
      · exact r0_5
      · exact r0_6
      · exact r0_7
      · exact r0_8
      · exact r0_9
      · exact r0_10
      · exact r0_11
      · exact r0_12
      · exact r0_13
      · exact r0_14
      · exact r0_15
      · exact r0_16
      · exact r0_17
      · exact r0_18
      · exact r0_19
      · exact r0_20
      · exact r0_21
      · exact r0_22
      · exact r0_23
    · refine ⟨M1, by simp [M1], fun p hp => ?_, fun k S => sym0 k1 k 1 S⟩
      simp only [M1, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact r1_0
      · exact r1_1
      · exact r1_2
      · exact r1_3
      · exact r1_4
      · exact r1_5
      · exact r1_6
      · exact r1_7
      · exact r1_8
      · exact r1_9
      · exact r1_10
      · exact r1_11
      · exact r1_12
      · exact r1_13
      · exact r1_14
      · exact r1_15
      · exact r1_16
      · exact r1_17
      · exact r1_18
      · exact r1_19
      · exact r1_20
      · exact r1_21
      · exact r1_22
      · exact r1_23
      · exact r1_24
    · refine ⟨M2, by simp [M2], fun p hp => ?_, fun k S => sym0 k2 k 2 S⟩
      simp only [M2, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact r2_0
      · exact r2_1
      · exact r2_2
      · exact r2_3
      · exact r2_4
      · exact r2_5
      · exact r2_6
      · exact r2_7
      · exact r2_8
      · exact r2_9
      · exact r2_10
      · exact r2_11
      · exact r2_12
      · exact r2_13
      · exact r2_14
      · exact r2_15
      · exact r2_16
      · exact r2_17
      · exact r2_18
      · exact r2_19
      · exact r2_20
      · exact r2_21
      · exact r2_22
      · exact r2_23
      · exact r2_24
  · refine ⟨[(FF, FF)], by simp, fun p hp => ?_, fun k S hS hm hc => ⟨S, hS, hm, ?_⟩⟩
    · simp only [List.mem_singleton] at hp; subst hp
      have h := List.all_eq_true.1 r_r t (by simp; omega)
      rwa [Bool.not_eq_true'] at h
    · exact FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
def EF : ℕ := (([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (ℕ × ℕ)).map
  (fun e => rawP.getD e.1 0 &&& rawP.getD e.2 0)).foldr (· ||| ·) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 9 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 9 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma fold_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma rawL_mem (i : ℕ) (hi : i < 9) : rawP.getD i 0 ∈ rawL := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [rawP_len]; exact hi)]
  exact List.mem_append_left _ (List.getElem_mem _)
lemma or02_mem : rawP.getD 0 0 ||| rawP.getD 2 0 ∈ rawL := List.mem_append_right _ (by simp)
lemma raw_sub {x : ℕ} (hx : x ∈ rawL) : x &&& mz 0 = x := by
  have := List.all_eq_true.1 m0_full x hx
  rwa [Nat.beq_eq, nl] at this
theorem final : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hfan hfirst hfun
  by_contra hsz
  obtain ⟨gates, out⟩ := C
  let row : ℕ → Fin 9 → Bool := fun b v => (rawP.getD v.val 0).testBit b
  have hrow : ∀ b, List.ofFn (row b) = rawP.map (fun x => x.testBit b) := row_list
  have hRP : ∀ x ∈ rawP, x &&& mz 0 = x := fun x hx => raw_sub (List.mem_append_left _ hx)
  match gates, hfan, hfirst, hfun, hsz with
  | [], _, hfirst, _, _ =>
    have := hfirst (fun _ => true)
    simp [PEqualNP.CircuitLowerBounds.Circuit.wires] at this
  | g :: gs, hfan, hfirst, hfun, hsz =>
    have hlen : gs.length ≤ 14 := by
      have : ¬ 16 ≤ gs.length + 1 := hsz
      omega
    have hg : ∀ x ∈ g :: gs, x.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ x.inputs.length ≤ 2 := hfan
    have hy : gv (mz 0) rawP g = rawP.getD 0 0 ||| rawP.getD 2 0 := by
      apply Nat.eq_of_testBit_eq; intro b
      cases hb : (mz 0).testBit b with
      | false =>
        have e1 := congrArg (fun x => x.testBit b) (gv_sub (mz 0) hRP g)
        have e2 := congrArg (fun x => x.testBit b) (raw_sub or02_mem)
        simp only [Nat.testBit_and, hb, Bool.and_false] at e1 e2
        rw [← e1, ← e2]
      | true =>
        have h := hfirst (row b)
        have e : (PEqualNP.CircuitLowerBounds.Circuit.mk (g :: gs) out).wires (List.ofFn (row b)) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (rawP.map (fun x => x.testBit b) ++ [g.op.eval (g.inputs.map fun i => (rawP.map (fun x => x.testBit b)).getD i false)]) := by
          rw [hrow]; rfl
        rw [e, fold_keep _ _ _ (by simp [rawP_len]), ← gv_bit (mz 0) hb rawP g (hg g List.mem_cons_self)] at h
        have h9 : (rawP.map (fun x => x.testBit b) ++ [(gv (mz 0) rawP g).testBit b]).getD 9 false = (gv (mz 0) rawP g).testBit b := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [rawP_len])]; simp [rawP_len]
        rw [h9] at h
        rw [h, Nat.testBit_or]; rfl
    have hsub : ∀ x ∈ rawP ++ [rawP.getD 0 0 ||| rawP.getD 2 0], x ∈ rawL := fun x hx => hx
    have hout : (ex (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 2 0])).getD out 0 = tz 0 := by
      rw [← EF_ok]
      have hs : ∀ x ∈ ex (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 2 0]), x &&& mz 0 = x :=
        ex_sub (mz 0) fun x hx => raw_sub (hsub x hx)
      have hs' := getD_mem (S := {x | x &&& mz 0 = x}) hs (by simp) out
      apply Nat.eq_of_testBit_eq; intro b
      have e1 := congrArg (fun x => x.testBit b) hs'
      simp only [Nat.testBit_and] at e1
      rw [← e1, Nat.testBit_and]
      cases hb : (mz 0).testBit b with
      | false => simp
      | true =>
        simp only [Bool.and_true]
        rw [← getD_map, ex_bit (mz 0) hb gs _ (fun x hx => hg x (List.mem_cons_of_mem _ hx))]
        have h := congrFun hfun (row b)
        have e : PEqualNP.MetaComplexity.circuitFun 9 ⟨g :: gs, out⟩ (row b) =
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (rawP.map (fun x => x.testBit b) ++ [g.op.eval (g.inputs.map fun i => (rawP.map (fun x => x.testBit b)).getD i false)])).getD out false := by
          change ((PEqualNP.CircuitLowerBounds.Circuit.mk (g :: gs) out).wires (List.ofFn (row b))).getD out false = _
          rw [hrow]; rfl
        rw [e, ← gv_bit (mz 0) hb rawP g (hg g List.mem_cons_self), hy] at h
        rw [List.map_append, List.map_singleton, h]
        simp only [EF, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.testBit_or, Nat.testBit_and, Nat.zero_testBit, Bool.or_false]
        simp only [Bool.or_assoc]; rfl
    have hsol := ex_sol (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 2 0]) (C (mz 0) (WZ 0))
      (fun x hx => Or.inl ⟨x, hsub x hx, (raw_sub (hsub x hx)).symm⟩) (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
      (fun x hx => hg x (List.mem_cons_of_mem _ hx)) ⟨out, hout⟩
    exact i0 _ (by omega) hsol
end PEqualNP.Outside.L_meta_1674

theorem PEqualNP.Outside.L_meta_1674 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size :=
  PEqualNP.Outside.L_meta_1674.final
