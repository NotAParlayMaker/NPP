import Mathlib
import PEqualNP.Defs

-- The counting step and the circuit frame are copied from L_meta_9484 (sheganinans, PR 13556).

namespace PEqualNP.Outside.L_meta_9490

variable {α β : Type} [DecidableEq α] [DecidableEq β]

private def Bic (A : α → β → Bool) (R : Finset α) (C : Finset β) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ C, ∀ d ∈ C,
    A a c = true → A b c = true → A a d = true → A b d = true

private def Twins (A : α → β → Bool) (R X : Finset α) (C Y : Finset β) : Prop :=
  (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ C, A a c = A b c) ∧
  (∀ a ∈ Y, ∀ b ∈ Y, ∀ r ∈ R, A r a = A r b)

-- One round can delete a class of equal rows and a class of equal columns.
private def Rank (A : α → β → Bool) : ℕ → Finset α → Finset β → Prop
  | 0, R, C => Bic A R C
  | n + 1, R, C => ∃ X ⊆ R, ∃ Y ⊆ C, Twins A R X C Y ∧ Rank A n (R \ X) (C \ Y)

private theorem rank_pad {A : α → β → Bool} {k : ℕ} {R : Finset α} {C : Finset β}
    (h : Rank A k R C) : Rank A (k + 1) R C := by
  refine ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, ?_, ?_⟩
  · simp [Twins]
  · simpa using h

private theorem rank_extend {A : α → β → Bool} {k : ℕ} {R S : Finset α} {C D : Finset β}
    (hS : S ⊆ R) (hD : D ⊆ C) (h : Rank A k S D)
    (hsub : Bic A (R \ S) (C \ D))
    (h1 : ∀ a ∈ S, ∀ b ∈ C \ D, A a b = false)
    (h2 : ∀ a ∈ R \ S, ∀ b ∈ D, A a b = false) : Rank A k R C := by
  induction k generalizing R S C D with
  | zero =>
    intro a ha b hb c hc d hd hac hbc had
    have key : ∀ x ∈ R, ∀ y ∈ C, A x y = true → (x ∈ S ↔ y ∈ D) := by
      intro x hx y hy hxy
      constructor
      · intro hxS
        by_contra hn
        rw [h1 x hxS y (Finset.mem_sdiff.2 ⟨hy, hn⟩)] at hxy
        contradiction
      · intro hyD
        by_contra hn
        rw [h2 x (Finset.mem_sdiff.2 ⟨hx, hn⟩) y hyD] at hxy
        contradiction
    have e1 := key a ha c hc hac
    have e2 := key b hb c hc hbc
    have e3 := key a ha d hd had
    by_cases hs : a ∈ S
    · exact h a hs b (e2.mpr (e1.mp hs)) c (e1.mp hs) d (e3.mp hs) hac hbc had
    · exact hsub a (Finset.mem_sdiff.2 ⟨ha, hs⟩)
        b (Finset.mem_sdiff.2 ⟨hb, hs ∘ e1.mpr ∘ e2.mp⟩)
        c (Finset.mem_sdiff.2 ⟨hc, hs ∘ e1.mpr⟩)
        d (Finset.mem_sdiff.2 ⟨hd, hs ∘ e3.mpr⟩) hac hbc had
  | succ k ih =>
    obtain ⟨X, hX, Y, hY, hT, h⟩ := h
    refine ⟨X, hX.trans hS, Y, hY.trans hD, ⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb c hc
      by_cases hd : c ∈ D
      · exact hT.1 a ha b hb c hd
      · rw [h1 a (hX ha) c (Finset.mem_sdiff.2 ⟨hc, hd⟩), h1 b (hX hb) c (Finset.mem_sdiff.2 ⟨hc, hd⟩)]
    · intro a ha b hb r hr
      by_cases hs : r ∈ S
      · exact hT.2 a ha b hb r hs
      · rw [h2 r (Finset.mem_sdiff.2 ⟨hr, hs⟩) a (hY ha), h2 r (Finset.mem_sdiff.2 ⟨hr, hs⟩) b (hY hb)]
    · have eR : (R \ X) \ (S \ X) = R \ S := by
        ext a
        simp only [Finset.mem_sdiff]
        have := @hX a
        tauto
      have eC : (C \ Y) \ (D \ Y) = C \ D := by
        ext a
        simp only [Finset.mem_sdiff]
        have := @hY a
        tauto
      have Incl {T U V : Finset α} (h : T ⊆ U) : T \ V ⊆ U \ V :=
        fun _ hmem => Finset.mem_sdiff.2 ⟨h (Finset.mem_sdiff.1 hmem).1, (Finset.mem_sdiff.1 hmem).2⟩
      have Incl' {T U V : Finset β} (h : T ⊆ U) : T \ V ⊆ U \ V :=
        fun _ hmem => Finset.mem_sdiff.2 ⟨h (Finset.mem_sdiff.1 hmem).1, (Finset.mem_sdiff.1 hmem).2⟩
      apply ih (Incl hS) (Incl' hD) h
      · simpa only [eR, eC] using hsub
      · intro a ha b hb
        exact h1 a (Finset.mem_sdiff.1 ha).1 b (eC ▸ hb)
      · intro a ha b hb
        exact h2 a (eR ▸ ha) b (Finset.mem_sdiff.1 hb).1

private def Pairing (F : Finset ℕ → Bool) (A : α → β → Bool) (l : α → ℕ) (r : β → ℕ)
    (N : Finset ℕ) (R : Finset α) (C : Finset β) : Prop :=
  (∀ a ∈ R, l a ∈ N ∧ F {l a} = false) ∧
  (∀ b ∈ C, r b ∈ N ∧ F {r b} = false) ∧
  (∀ a ∈ R, ∀ b ∈ C, A a b = F {l a, r b})

private def Depends (F : Finset ℕ → Bool) (N : Finset ℕ) : Prop :=
  ∀ P Q : Finset ℕ, (∀ i ∈ N, i ∈ P ↔ i ∈ Q) → F P = F Q

private def Budgets (F : Finset ℕ → Bool) (N : Finset ℕ) (k : ℕ) : Prop :=
  ∀ {α β : Type} [DecidableEq α] [DecidableEq β] (A : α → β → Bool)
    (l : α → ℕ) (r : β → ℕ) (R : Finset α) (C : Finset β),
    Pairing F A l r N R C → Rank A k R C

private def avoid {γ : Type} (S : Finset γ) (w : γ → ℕ) (J : Finset ℕ) : Finset γ :=
  S.filter fun a => w a ∉ J

private theorem charge {F : Finset ℕ → Bool} {A : α → β → Bool} {l : α → ℕ} {r : β → ℕ}
    {N R C} (h : Pairing F A l r N R C) (J : Finset ℕ) {k : ℕ}
    (hk : Rank A k (avoid R l J) (avoid C r J)) : Rank A (k + J.card) R C := by
  induction J using Finset.induction_on generalizing R C with
  | empty => simpa [avoid] using hk
  | @insert j J hj ih =>
    let X := R.filter fun a => l a = j
    let Y := C.filter fun b => r b = j
    rw [Finset.card_insert_of_notMem hj, ← Nat.add_assoc]
    refine ⟨X, Finset.filter_subset _ _, Y, Finset.filter_subset _ _, ⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb c hc
      obtain ⟨ha, e₁⟩ := Finset.mem_filter.1 ha
      obtain ⟨hb, e₂⟩ := Finset.mem_filter.1 hb
      rw [h.2.2 a ha c hc, h.2.2 b hb c hc, e₁, e₂]
    · intro a ha b hb c hc
      obtain ⟨ha, e₁⟩ := Finset.mem_filter.1 ha
      obtain ⟨hb, e₂⟩ := Finset.mem_filter.1 hb
      rw [h.2.2 c hc a ha, h.2.2 c hc b hb, e₁, e₂]
    · apply ih
      · exact ⟨fun a ha => h.1 a (Finset.mem_sdiff.1 ha).1,
          fun b hb => h.2.1 b (Finset.mem_sdiff.1 hb).1,
          fun a ha b hb => h.2.2 a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1⟩
      · have eR : avoid (R \ X) l J = avoid R l (insert j J) := by
          ext a
          simp only [avoid, X, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert]
          tauto
        have eC : avoid (C \ Y) r J = avoid C r (insert j J) := by
          ext a
          simp only [avoid, Y, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert]
          tauto
        rw [eR, eC]
        exact hk

private def put (t : ℕ) (b : Bool) (P : Finset ℕ) : Finset ℕ :=
  if b then insert t P else P.erase t

private def trigger (S : Finset ℕ) (isAnd : Bool) (P : Finset ℕ) : Bool :=
  if isAnd then decide (S ⊆ P) else decide (∃ i ∈ S, i ∈ P)

private theorem trigger_congr (S : Finset ℕ) (a : Bool) (P Q : Finset ℕ)
    (h : ∀ i ∈ S, i ∈ P ↔ i ∈ Q) : trigger S a P = trigger S a Q := by
  cases a
  · simp only [trigger, Bool.false_eq_true, ite_false, decide_eq_decide]
    exact exists_congr fun i => and_congr_right (h i)
  · simp only [trigger, ite_true, decide_eq_decide]
    exact forall_congr' fun i => imp_congr_right (h i)

private theorem trigger_zero (S : Finset ℕ) (a : Bool)
    (ha : a = true → S.card = 2) : trigger S a ∅ = false := by
  cases a
  · simp [trigger]
  · have h : S ≠ ∅ := fun e => by simpa [e] using ha rfl
    simp [trigger, h]

private theorem put_mem_self (t : ℕ) (b : Bool) (P : Finset ℕ) :
    t ∈ put t b P ↔ b = true := by cases b <;> simp [put]

private theorem put_mem_other {i t : ℕ} (h : i ≠ t) (b : Bool) (P : Finset ℕ) :
    i ∈ put t b P ↔ i ∈ P := by cases b <;> simp [put, h]

private theorem replace_depends {F : Finset ℕ → Bool} {N S : Finset ℕ} {t : ℕ} {a : Bool}
    (hd : Depends F N) : Depends (fun P => F (put t (trigger S a P) P)) (N.erase t ∪ S) := by
  intro P Q hPQ
  apply hd
  intro i hi
  by_cases h : i = t
  · subst i
    rw [put_mem_self, put_mem_self, trigger_congr S a P Q (fun i hi => hPQ i (Finset.mem_union_right _ hi))]
  · rw [put_mem_other h, put_mem_other h]
    exact hPQ i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨h, hi⟩))

private theorem ignored_update {F : Finset ℕ → Bool} {N : Finset ℕ} {t : ℕ}
    (hd : Depends F N) (ht : t ∉ N) (P : Finset ℕ) (b : Bool) : F (put t b P) = F P := by
  apply hd
  intro i hi
  have hn : i ≠ t := fun e => ht (e ▸ hi)
  exact put_mem_other hn b P

private theorem or_pair {F : Finset ℕ → Bool} {N S : Finset ℕ} {t u v : ℕ}
    (hd : Depends F N) (ht : t ∈ N)
    (hu : u ∈ N.erase t ∪ S) (hv : v ∈ N.erase t ∪ S)
    (hu' : u ∉ N.erase t ∩ S) (hv' : v ∉ N.erase t ∩ S) :
    let m (w : ℕ) := if w ∈ S then t else w
    m u ∈ N ∧ m v ∈ N ∧ F (put t (trigger S false {u,v}) {u,v}) = F {m u,m v} := by
  dsimp
  have hm : ∀ w ∈ N.erase t ∪ S, (if w ∈ S then t else w) ∈ N := by
    intro w hw
    split_ifs with hh
    · exact ht
    · exact (Finset.mem_erase.1 ((Finset.mem_union.1 hw).resolve_right hh)).2
  refine ⟨hm u hu, hm v hv, ?_⟩
  apply hd
  intro i hi
  have mt : ∀ w ∈ N.erase t ∪ S, (if w ∈ S then t else w) = t ↔ w ∈ S := by
    intro w hw
    by_cases hh : w ∈ S
    · simp [hh]
    · have hne := (Finset.mem_erase.1 ((Finset.mem_union.1 hw).resolve_right hh)).1
      simp [hh, hne]
  have mo : ∀ w, w ∉ N.erase t ∩ S → i ≠ t →
      (i = (if w ∈ S then t else w) ↔ i = w) := by
    intro w hw hn
    by_cases hS : w ∈ S
    · have hw' : i ≠ w := fun e => hw (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨e ▸ hn, e ▸ hi⟩, hS⟩)
      simp [hS, hn, hw']
    · simp [hS]
  by_cases he : i = t
  · subst i
    rw [put_mem_self]
    simp only [trigger, Bool.false_eq_true, ite_false, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    rw [eq_comm (a := t) (b := if u ∈ S then t else u),
      eq_comm (a := t) (b := if v ∈ S then t else v), mt u hu, mt v hv]
    constructor
    · rintro ⟨j, hj, (rfl | rfl)⟩
      · exact Or.inl hj
      · exact Or.inr hj
    · rintro (h | h)
      · exact ⟨u, h, Or.inl rfl⟩
      · exact ⟨v, h, Or.inr rfl⟩
  · rw [put_mem_other he]
    simp only [Finset.mem_insert, Finset.mem_singleton, mo u hu' he, mo v hv' he]

private theorem and_pair {F : Finset ℕ → Bool} {N S : Finset ℕ} {t u v : ℕ}
    (hd : Depends F N) (hS : S.card = 2) (htS : t ∉ S)
    (hu : u ∈ N.erase t ∪ S) (hv : v ∈ N.erase t ∪ S)
    (hu' : u ∉ N.erase t ∩ S) (hv' : v ∉ N.erase t ∩ S) :
    F (put t (trigger S true {u,v}) {u,v}) =
      if u ∈ S then
        if v ∈ S then (if S ⊆ {u,v} then F {t} else F ∅) else F {v}
      else if v ∈ S then F {u} else F {u,v} := by
  have ht : t ≠ u ∧ t ≠ v := by
    constructor
    · rintro rfl
      exact (Finset.mem_union.1 hu).elim (by simp) htS
    · rintro rfl
      exact (Finset.mem_union.1 hv).elim (by simp) htS
  have hnot : ∀ w : ℕ, ¬ S ⊆ {w} := by
    intro w hn
    have := Finset.card_le_card hn
    simp [hS] at this
  have htno : ∀ i ∈ N, i ≠ t → i ≠ u ∨ u ∉ S := by
    intro i hi hit
    by_cases d : i = u
    · subst i
      exact Or.inr (fun h => hu' (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hit, hi⟩, h⟩))
    · exact Or.inl d
  have htno' : ∀ i ∈ N, i ≠ t → i ≠ v ∨ v ∉ S := by
    intro i hi hit
    by_cases d : i = v
    · subst i
      exact Or.inr (fun h => hv' (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hit, hi⟩, h⟩))
    · exact Or.inl d
  have off : u ∉ S ∨ v ∉ S → ¬ S ⊆ ({u,v} : Finset ℕ) := by
    rintro (h | h) hs
    · apply hnot v
      intro x hx
      have := hs hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      exact this.resolve_left (fun e => h (e ▸ hx))
    · apply hnot u
      intro x hx
      have := hs hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      exact this.resolve_right (fun e => h (e ▸ hx))
  by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
  · simp only [huS, hvS, ite_true]
    split_ifs with e
    · apply hd
      intro i hi
      by_cases ht' : i = t
      · subst i
        simp [put_mem_self, trigger, e]
      · rw [put_mem_other ht']
        have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
        have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
        simp [h₁, h₂, ht']
    · apply hd
      intro i hi
      by_cases ht' : i = t
      · subst i
        simp [put_mem_self, trigger, e]
      · rw [put_mem_other ht']
        have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
        have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
        simp [h₁, h₂]
  · simp only [huS, hvS, ite_true, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inr hvS), ht.2]
    · rw [put_mem_other ht']
      have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
      simp [h₁]
  · simp only [huS, hvS, ite_true, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inl huS), ht.1]
    · rw [put_mem_other ht']
      have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
      simp [h₂]
  · simp only [huS, hvS, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inl huS), ht.1, ht.2]
    · exact put_mem_other ht' _ _

-- Shared operands spend deletion rounds. Fresh OR operands merge into the old
-- label, and the fresh AND operands contribute only isolated rectangles.
private theorem replace_budget {F : Finset ℕ → Bool} {N S : Finset ℕ} {t k : ℕ} {a : Bool}
    (hd : Depends F N) (h0 : F ∅ = false) (hB : Budgets F N k)
    (ht : t ∈ N) (htS : t ∉ S) (ha : a = true → S.card = 2) :
    Budgets (fun P => F (put t (trigger S a P) P)) (N.erase t ∪ S) (k + (N.erase t ∩ S).card) := by
  intro α β _ _ A l r R C h
  let J := N.erase t ∩ S
  apply charge h J
  let R' := avoid R l J
  let C' := avoid C r J
  have hL : ∀ i ∈ R', l i ∈ N.erase t ∪ S ∧ l i ∉ J := fun i hi =>
    ⟨(h.1 i (Finset.mem_filter.1 hi).1).1, (Finset.mem_filter.1 hi).2⟩
  have hR : ∀ j ∈ C', r j ∈ N.erase t ∪ S ∧ r j ∉ J := fun j hj =>
    ⟨(h.2.1 j (Finset.mem_filter.1 hj).1).1, (Finset.mem_filter.1 hj).2⟩
  have hLS : ∀ i ∈ R', F (put t (trigger S a {l i}) {l i}) = false := fun i hi =>
    (h.1 i (Finset.mem_filter.1 hi).1).2
  have hRS : ∀ j ∈ C', F (put t (trigger S a {r j}) {r j}) = false := fun j hj =>
    (h.2.1 j (Finset.mem_filter.1 hj).1).2
  have hP : ∀ i ∈ R', ∀ j ∈ C', A i j = F (put t (trigger S a {l i,r j}) {l i,r j}) := fun i hi j hj =>
    h.2.2 i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1
  cases a
  · let m (w : ℕ) := if w ∈ S then t else w
    apply hB A (m ∘ l) (m ∘ r) R' C'
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have e := or_pair hd ht (hL i hi).1 (hL i hi).1 (hL i hi).2 (hL i hi).2
      have q : F (put t (trigger S false {l i}) {l i}) = F {m (l i)} := by
        simpa [m] using e.2.2
      exact ⟨e.1, q.symm.trans (hLS i hi)⟩
    · intro j hj
      have e := or_pair hd ht (hR j hj).1 (hR j hj).1 (hR j hj).2 (hR j hj).2
      have q : F (put t (trigger S false {r j}) {r j}) = F {m (r j)} := by
        simpa [m] using e.2.2
      exact ⟨e.1, q.symm.trans (hRS j hj)⟩
    · intro i hi j hj
      exact (hP i hi j hj).trans (or_pair hd ht (hL i hi).1 (hR j hj).1 (hL i hi).2 (hR j hj).2).2.2
  · have hS := ha rfl
    let X := avoid R' l S
    let Y := avoid C' r S
    let e u v hu hv hu' hv' := and_pair (u := u) (v := v) hd hS htS hu hv hu' hv'
    have lzero : ∀ i ∈ X, F {l i} = false := by
      intro i hi
      obtain ⟨hr, hs⟩ := Finset.mem_filter.1 hi
      have q := e (l i) (l i) (hL i hr).1 (hL i hr).1 (hL i hr).2 (hL i hr).2
      have q' : F (put t (trigger S true {l i}) {l i}) = F {l i} := by simpa [hs] using q
      exact q'.symm.trans (hLS i hr)
    have rzero : ∀ j ∈ Y, F {r j} = false := by
      intro j hj
      obtain ⟨hr, hs⟩ := Finset.mem_filter.1 hj
      have q := e (r j) (r j) (hR j hr).1 (hR j hr).1 (hR j hr).2 (hR j hr).2
      have q' : F (put t (trigger S true {r j}) {r j}) = F {r j} := by simpa [hs] using q
      exact q'.symm.trans (hRS j hr)
    have hX : X ⊆ R' := Finset.filter_subset _ _
    have hY : Y ⊆ C' := Finset.filter_subset _ _
    have hx : ∀ i ∈ R' \ X, l i ∈ S := by
      intro i hi
      by_contra hn
      exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hi).1, hn⟩)
    have hy : ∀ j ∈ C' \ Y, r j ∈ S := by
      intro j hj
      by_contra hn
      exact (Finset.mem_sdiff.1 hj).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hj).1, hn⟩)
    have evalP : ∀ i ∈ R', ∀ j ∈ C', A i j =
        if l i ∈ S then if r j ∈ S then (if S ⊆ {l i,r j} then F {t} else F ∅) else F {r j}
        else if r j ∈ S then F {l i} else F {l i,r j} := by
      intro i hi j hj
      exact (hP i hi j hj).trans (e _ _ (hL i hi).1 (hR j hj).1 (hL i hi).2 (hR j hj).2)
    apply rank_extend hX hY (hB A l r X Y ?_)
    · intro a ha b hb c hc d hd' hac hbc had
      have E : ∀ i ∈ R' \ X, ∀ j ∈ C' \ Y, A i j = (if S ⊆ {l i,r j} then F {t} else false) := by
        intro i hi j hj
        simpa [hx i hi, hy j hj, h0] using evalP i (Finset.mem_sdiff.1 hi).1 j (Finset.mem_sdiff.1 hj).1
      rw [E a ha c hc] at hac
      rw [E a ha d hd'] at had
      rw [E b hb c hc] at hbc
      rw [E b hb d hd']
      have h₁ : S ⊆ ({l a,r c} : Finset ℕ) := by
        by_contra e
        simp [e] at hac
      have h₂ : S ⊆ ({l a,r d} : Finset ℕ) := by
        by_contra e
        simp [e] at had
      have same : ({l a,r c} : Finset ℕ) = {l a,r d} := by
        have eq : ∀ x y : ℕ, S ⊆ {x,y} → S = {x,y} := by
          intro x y hxy
          apply Finset.eq_of_subset_of_card_le hxy
          rw [hS]
          exact le_trans (Finset.card_insert_le _ _) (by simp)
        exact (eq _ _ h₁).symm.trans (eq _ _ h₂)
      have neq : r d ≠ l a := by
        intro he
        have := Finset.card_le_card h₂
        simp [he, hS] at this
      have hr' : r d = r c := by
        have hm : r d ∈ ({l a,r c} : Finset ℕ) := by rw [same]; simp
        exact (Finset.mem_insert.1 hm).resolve_left neq |> Finset.mem_singleton.1
      simpa only [hr'] using hbc
    · intro i hi j hj
      simpa [(Finset.mem_filter.1 hi).2, hy j hj, lzero i hi] using
        evalP i (hX hi) j (Finset.mem_sdiff.1 hj).1
    · intro i hi j hj
      simpa [hx i hi, (Finset.mem_filter.1 hj).2, rzero j hj] using
        evalP i (Finset.mem_sdiff.1 hi).1 j (hY hj)
    · refine ⟨?_, ?_, ?_⟩
      · intro i hi
        have nue := (Finset.mem_filter.1 hi).2
        exact ⟨(Finset.mem_erase.1 ((Finset.mem_union.1 (hL i (hX hi)).1).resolve_right nue)).2, lzero i hi⟩
      · intro j hj
        have nue := (Finset.mem_filter.1 hj).2
        exact ⟨(Finset.mem_erase.1 ((Finset.mem_union.1 (hR j (hY hj)).1).resolve_right nue)).2, rzero j hj⟩
      · intro i hi j hj
        simpa [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hj).2] using evalP i (hX hi) j (hY hj)

-- The literal graph is a ring of fourteen squares, one satellite per square end.
private def A : Fin 21 → Fin 21 → Bool := fun a b => decide (∃ i : Fin 7,
  ((a.val = i.val ∨ a.val = 7 + i.val) ∧ (b.val = (i.val + 1) % 7 ∨ b.val = 14 + i.val)) ∨
  ((b.val = i.val ∨ b.val = 7 + i.val) ∧ (a.val = (i.val + 1) % 7 ∨ a.val = 14 + i.val)))

private theorem A_sym : ∀ a b, A a b = A b a := by decide +kernel

private abbrev V := Fin 21 ⊕ Fin 21

private def G : V → V → Bool
  | .inl a, .inr b => A a b
  | .inr b, .inl a => A a b
  | _, _ => false

private def token (i : Fin 14) (kind : Fin 3) : V :=
  let v := Fin.ofNat 21 (if kind = 0 then i.val % 7 else
    if kind = 1 then 7 + i.val % 7 else 14 + (i.val + 6) % 7)
  if i.val % 2 = 0 then .inl v else .inr v

private theorem localDiamond : ∀ (i : Fin 14) (p q : Bool),
    let a := if p then token (i + 13) 0 else token (i + 13) 1
    let b := if q then token (i + 1) 0 else token (i + 1) 2
    G (token i 0) a = true ∧ G (token i 0) b = true ∧
      G (token i 2) a = true ∧ G (token i 2) b = false ∧
      G (token i 1) b = true ∧ G (token i 1) a = false := by decide +kernel

-- A rectangle-closed remainder resolves every ring position.
private theorem resolved (D : Finset V)
    (h : ∀ a b c d : V, a ∉ D → b ∉ D → c ∉ D → d ∉ D →
      G a c = true → G b c = true → G a d = true → G b d = true) (i : Fin 14) :
    token i 0 ∈ D ∨ (token (i + 13) 0 ∈ D ∧ token (i + 13) 1 ∈ D) ∨
      (token (i + 1) 0 ∈ D ∧ token (i + 1) 2 ∈ D) ∨ (token i 1 ∈ D ∧ token i 2 ∈ D) := by
  by_contra hn
  push_neg at hn
  obtain ⟨h0, hp, hq, hab⟩ := hn
  let p := decide (token (i + 13) 0 ∉ D)
  let q := decide (token (i + 1) 0 ∉ D)
  let a := if p then token (i + 13) 0 else token (i + 13) 1
  let b := if q then token (i + 1) 0 else token (i + 1) 2
  have ha : a ∉ D := by
    by_cases e : token (i + 13) 0 ∈ D
    · have h' : token (i + 13) 1 ∉ D := hp e
      simpa [a, p, e] using h'
    · simp [a, p, e]
  have hb : b ∉ D := by
    by_cases e : token (i + 1) 0 ∈ D
    · have h' : token (i + 1) 2 ∉ D := hq e
      simpa [b, q, e] using h'
    · simp [b, q, e]
  obtain ⟨hia, hib, hca, hcb, hfb, hfa⟩ := localDiamond i p q
  by_cases h1 : token i 1 ∈ D
  · have h2 : token i 2 ∉ D := hab h1
    exact Bool.false_ne_true (hcb.symm.trans (h _ _ _ _ h0 h2 ha hb hia hca hib))
  · exact Bool.false_ne_true (hfa.symm.trans (h _ _ _ _ h0 h1 hb ha hib hfb hia))

-- The potential: resolved positions plus a local credit for half-deleted positions.
private def selfB (s : Fin 3 → Bool) : Bool := s 0 || (s 1 && s 2)

private def resF (s : Fin 14 → Fin 3 → Bool) (j : Fin 14) : Bool :=
  (selfB (s j) || (s (j + 13) 0 && s (j + 13) 1)) || (s (j + 1) 0 && s (j + 1) 2)

private def piF (m a b r0 r1 r2 : Bool) : ℕ :=
  if m then 0 else if a then (if b then (!r0 && !r2).toNat else (!r1 && !r2).toNat)
  else if b then (!r0 && !r1).toNat else 0

private def termR (s : Fin 14 → Fin 3 → Bool) (j : Fin 14) : ℕ := (resF s j).toNat

private def termP (s : Fin 14 → Fin 3 → Bool) (j : Fin 14) : ℕ :=
  piF (s j 0) (s j 1) (s j 2) (resF s (j + 13)) (resF s j) (resF s (j + 1))

private def Psi (s : Fin 14 → Fin 3 → Bool) : ℕ := (∑ j, termR s j) + ∑ j, termP s j

private def locF (y1 e1 g1 g2 y2 e2 m1 a1 b1 m0 a0 b0 m2 a2 b2 : Bool) : ℕ :=
  let r12 := (y1 || e1) || (m1 && b1)
  let r13 := ((m1 || (a1 && b1)) || g1) || (m0 && b0)
  let r0 := ((m0 || (a0 && b0)) || (m1 && a1)) || (m2 && b2)
  let r1 := ((m2 || (a2 && b2)) || (m0 && a0)) || g2
  let r2 := (y2 || (m2 && a2)) || e2
  (r12.toNat + (r13.toNat + (r0.toNat + (r1.toNat + r2.toNat)))) +
    (piF m1 a1 b1 r12 r13 r0 + (piF m0 a0 b0 r13 r0 r1 + piF m2 a2 b2 r0 r1 r2))

-- One twin set around a column raises the window part of the potential by at most one.
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
private theorem local_twin : ∀ m1 m1' : Bool, (m1 = true → m1' = true) →
    ∀ a1 a1' : Bool, (a1 = true → a1' = true) →
    ∀ m2 m2' : Bool, (m2 = true → m2' = true) →
    ∀ b2 b2' : Bool, (b2 = true → b2' = true) →
    ∀ m0 a0 b0 g1 g2 : Bool,
    (m1' = true → m1 = false → a1' = true → a1 = false → g1 = true) →
    (m2' = true → m2 = false → b2' = true → b2 = false → g2 = true) →
    (a1' = true → a1 = false → b2' = true → b2 = false → a0 = true ∧ b0 = true) →
    (m1' = true → m1 = false → b2' = true → b2 = false → g1 = true ∧ a0 = true ∧ b0 = true) →
    (a1' = true → a1 = false → m2' = true → m2 = false → a0 = true ∧ b0 = true ∧ g2 = true) →
    (m1' = true → m1 = false → m2' = true → m2 = false →
      g1 = true ∧ a0 = true ∧ b0 = true ∧ g2 = true) →
    ∀ y1 : Bool, (g1 = true → y1 = true) → ∀ y2 : Bool, (g2 = true → y2 = true) →
    ∀ e1 e2 b1 a2 : Bool,
    locF y1 e1 g1 g2 y2 e2 m1' a1' b1 m0 a0 b0 m2' a2 b2' ≤
      locF y1 e1 g1 g2 y2 e2 m1 a1 b1 m0 a0 b0 m2 a2 b2 + 1 := by decide +kernel

-- Deleting isolated vertices never raises it.
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
private theorem local_iso : ∀ m1 m1' : Bool, (m1 = true → m1' = true) →
    ∀ a1 a1' : Bool, (a1 = true → a1' = true) →
    ∀ m2 m2' : Bool, (m2 = true → m2' = true) →
    ∀ b2 b2' : Bool, (b2 = true → b2' = true) →
    ∀ m0 a0 b0 g1 g2 : Bool,
    (m1' = true → m1 = false → g1 = true ∧ m0 = true ∧ b0 = true) →
    (a1' = true → a1 = false → m0 = true ∧ b0 = true) →
    (m2' = true → m2 = false → m0 = true ∧ a0 = true ∧ g2 = true) →
    (b2' = true → b2 = false → m0 = true ∧ a0 = true) →
    ∀ y1 : Bool, (g1 = true → y1 = true) → ∀ y2 : Bool, (g2 = true → y2 = true) →
    ∀ e1 e2 b1 a2 : Bool,
    locF y1 e1 g1 g2 y2 e2 m1' a1' b1 m0 a0 b0 m2' a2 b2' ≤
      locF y1 e1 g1 g2 y2 e2 m1 a1 b1 m0 a0 b0 m2 a2 b2 := by decide +kernel

private def W5 : Finset (Fin 14) := {12, 13, 0, 1, 2}

private def W3 : Finset (Fin 14) := {13, 0, 1}

private theorem far_R : ∀ j : Fin 14, j ∉ W5 →
    (j ≠ 13 ∧ j ≠ 1) ∧ (j + 13 ≠ 13 ∧ j + 13 ≠ 1) ∧ (j + 1 ≠ 13 ∧ j + 1 ≠ 1) := by decide

private theorem far_P : ∀ j : Fin 14, j ∉ W3 → j ≠ 13 ∧ j ≠ 1 := by decide

private theorem resF_mono {s s' : Fin 14 → Fin 3 → Bool} (h : ∀ j c, s j c = true → s' j c = true)
    (j : Fin 14) (hr : resF s j = true) : resF s' j = true := by
  simp only [resF, selfB, Bool.or_eq_true, Bool.and_eq_true] at hr ⊢
  rcases hr with ((h1 | ⟨h2, h3⟩) | ⟨h4, h5⟩) | ⟨h6, h7⟩
  · exact Or.inl (Or.inl (Or.inl (h _ _ h1)))
  · exact Or.inl (Or.inl (Or.inr ⟨h _ _ h2, h _ _ h3⟩))
  · exact Or.inl (Or.inr ⟨h _ _ h4, h _ _ h5⟩)
  · exact Or.inr ⟨h _ _ h6, h _ _ h7⟩

private theorem piF_anti : ∀ m a b r0 r1 r2 r0' r1' r2' : Bool,
    (r0 = true → r0' = true) → (r1 = true → r1' = true) → (r2 = true → r2' = true) →
    piF m a b r0' r1' r2' ≤ piF m a b r0 r1 r2 := by decide +kernel

private theorem window (t t' : Fin 14 → Fin 3 → Bool) (b : ℕ)
    (hle : ∀ j c, t j c = true → t' j c = true)
    (hoff : ∀ j, j ≠ 13 → j ≠ 1 → t' j = t j)
    (hloc : (∑ j ∈ W5, termR t' j) + (∑ j ∈ W3, termP t' j) ≤
      (∑ j ∈ W5, termR t j) + (∑ j ∈ W3, termP t j) + b) :
    Psi t' ≤ Psi t + b := by
  have eR : ∑ j ∈ W5ᶜ, termR t' j = ∑ j ∈ W5ᶜ, termR t j := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ := far_R j (Finset.mem_compl.1 hj)
    simp only [termR, resF, hoff j h1 h2, hoff _ h3 h4, hoff _ h5 h6]
  have eP : ∑ j ∈ W3ᶜ, termP t' j ≤ ∑ j ∈ W3ᶜ, termP t j := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨h1, h2⟩ := far_P j (Finset.mem_compl.1 hj)
    unfold termP
    rw [hoff j h1 h2]
    exact piF_anti _ _ _ _ _ _ _ _ _ (resF_mono hle _) (resF_mono hle _) (resF_mono hle _)
  have s1 := Finset.sum_add_sum_compl W5 (termR t')
  have s2 := Finset.sum_add_sum_compl W5 (termR t)
  have s3 := Finset.sum_add_sum_compl W3 (termP t')
  have s4 := Finset.sum_add_sum_compl W3 (termP t)
  unfold Psi
  omega

private theorem win_eq (t : Fin 14 → Fin 3 → Bool) :
    (∑ j ∈ W5, termR t j) + (∑ j ∈ W3, termP t j) =
      locF (selfB (t 12)) (t 11 0 && t 11 1) (t 12 0 && t 12 1) (t 2 0 && t 2 2) (selfB (t 2))
        (t 3 0 && t 3 2) (t 13 0) (t 13 1) (t 13 2) (t 0 0) (t 0 1) (t 0 2) (t 1 0) (t 1 1) (t 1 2) := by
  rw [W5, W3,
    Finset.sum_insert (show (12 : Fin 14) ∉ ({13, 0, 1, 2} : Finset (Fin 14)) by decide),
    Finset.sum_insert (show (13 : Fin 14) ∉ ({0, 1, 2} : Finset (Fin 14)) by decide),
    Finset.sum_insert (show (0 : Fin 14) ∉ ({1, 2} : Finset (Fin 14)) by decide),
    Finset.sum_insert (show (1 : Fin 14) ∉ ({2} : Finset (Fin 14)) by decide),
    Finset.sum_singleton,
    Finset.sum_insert (show (13 : Fin 14) ∉ ({0, 1} : Finset (Fin 14)) by decide),
    Finset.sum_insert (show (0 : Fin 14) ∉ ({1} : Finset (Fin 14)) by decide),
    Finset.sum_singleton]
  rfl

private theorem anchor0 (t t' : Fin 14 → Fin 3 → Bool) (b : ℕ)
    (hle : ∀ j c, t j c = true → t' j c = true)
    (hoff : ∀ j, j ≠ 13 → j ≠ 1 → t' j = t j)
    (h13 : t' 13 2 = t 13 2) (h1 : t' 1 1 = t 1 1)
    (hloc : locF (selfB (t 12)) (t 11 0 && t 11 1) (t 12 0 && t 12 1) (t 2 0 && t 2 2) (selfB (t 2))
        (t 3 0 && t 3 2) (t' 13 0) (t' 13 1) (t 13 2) (t 0 0) (t 0 1) (t 0 2) (t' 1 0) (t 1 1) (t' 1 2) ≤
      locF (selfB (t 12)) (t 11 0 && t 11 1) (t 12 0 && t 12 1) (t 2 0 && t 2 2) (selfB (t 2))
        (t 3 0 && t 3 2) (t 13 0) (t 13 1) (t 13 2) (t 0 0) (t 0 1) (t 0 2) (t 1 0) (t 1 1) (t 1 2) + b) :
    Psi t' ≤ Psi t + b := by
  apply window t t' b hle hoff
  rw [win_eq, win_eq, hoff 12 (by decide) (by decide), hoff 11 (by decide) (by decide),
    hoff 0 (by decide) (by decide), hoff 2 (by decide) (by decide), hoff 3 (by decide) (by decide),
    h13, h1]
  exact hloc

private def cfg (D : Finset V) : Fin 14 → Fin 3 → Bool := fun j c => decide (token j c ∈ D)

private theorem psi_rot (s : Fin 14 → Fin 3 → Bool) (k : Fin 14) :
    Psi (fun i => s (k + i)) = Psi s := by
  have hr : ∀ i, resF (fun i => s (k + i)) i = resF s (k + i) := by
    intro i
    simp only [resF, add_assoc]
  have e1 : ∑ i, termR (fun i => s (k + i)) i = ∑ j, termR s j :=
    Fintype.sum_equiv (Equiv.addLeft k) _ _ (fun i => by simp only [termR, hr, Equiv.coe_addLeft])
  have e2 : ∑ i, termP (fun i => s (k + i)) i = ∑ j, termP s j :=
    Fintype.sum_equiv (Equiv.addLeft k) _ _
      (fun i => by simp only [termP, hr, Equiv.coe_addLeft, add_assoc])
  unfold Psi
  rw [e1, e2]

private def N4 (k : Fin 14) : Finset V :=
  {token (k + 13) 0, token (k + 13) 1, token (k + 1) 0, token (k + 1) 2}

private theorem tok_N4 : ∀ (k i : Fin 14) (c : Fin 3), token (k + i) c ∈ N4 k →
    (i = 13 ∧ c ≠ 2) ∨ (i = 1 ∧ c ≠ 1) := by decide +kernel

private theorem gfacts : ∀ k : Fin 14,
    (G (token (k + 13) 0) (token (k + 12) 0) = true ∧ G (token (k + 13) 0) (token (k + 12) 1) = true ∧
    G (token (k + 13) 0) (token (k + 0) 0) = true ∧ G (token (k + 13) 0) (token (k + 0) 2) = true ∧
    G (token (k + 13) 1) (token (k + 0) 0) = true ∧ G (token (k + 13) 1) (token (k + 0) 2) = true ∧
    G (token (k + 1) 0) (token (k + 0) 0) = true ∧ G (token (k + 1) 0) (token (k + 0) 1) = true ∧
    G (token (k + 1) 0) (token (k + 2) 0) = true ∧ G (token (k + 1) 0) (token (k + 2) 2) = true ∧
    G (token (k + 1) 2) (token (k + 0) 0) = true ∧ G (token (k + 1) 2) (token (k + 0) 1) = true) ∧
    (G (token (k + 13) 1) (token (k + 12) 0) = false ∧ G (token (k + 13) 1) (token (k + 12) 1) = false ∧
    G (token (k + 1) 2) (token (k + 2) 0) = false ∧ G (token (k + 1) 2) (token (k + 2) 2) = false ∧
    G (token (k + 13) 1) (token (k + 0) 1) = false ∧ G (token (k + 1) 2) (token (k + 0) 2) = false ∧
    G (token (k + 13) 0) (token (k + 0) 1) = false ∧ G (token (k + 1) 0) (token (k + 0) 2) = false ∧
    G (token (k + 13) 1) (token (k + 2) 0) = false ∧ G (token (k + 13) 1) (token (k + 2) 2) = false ∧
    G (token (k + 13) 0) (token (k + 2) 0) = false ∧ G (token (k + 13) 0) (token (k + 2) 2) = false ∧
    G (token (k + 1) 0) (token (k + 12) 0) = false ∧ G (token (k + 1) 0) (token (k + 12) 1) = false ∧
    G (token (k + 1) 2) (token (k + 12) 0) = false ∧ G (token (k + 1) 2) (token (k + 12) 1) = false) := by
  decide +kernel

private theorem anchorD (D N : Finset V) (k : Fin 14) (b : ℕ) (hN : ∀ v ∈ N, v ∈ N4 k)
    (hloc : locF (selfB (cfg D (k + 12))) (cfg D (k + 11) 0 && cfg D (k + 11) 1)
        (cfg D (k + 12) 0 && cfg D (k + 12) 1) (cfg D (k + 2) 0 && cfg D (k + 2) 2)
        (selfB (cfg D (k + 2))) (cfg D (k + 3) 0 && cfg D (k + 3) 2)
        (cfg (D ∪ N) (k + 13) 0) (cfg (D ∪ N) (k + 13) 1) (cfg D (k + 13) 2)
        (cfg D (k + 0) 0) (cfg D (k + 0) 1) (cfg D (k + 0) 2)
        (cfg (D ∪ N) (k + 1) 0) (cfg D (k + 1) 1) (cfg (D ∪ N) (k + 1) 2) ≤
      locF (selfB (cfg D (k + 12))) (cfg D (k + 11) 0 && cfg D (k + 11) 1)
        (cfg D (k + 12) 0 && cfg D (k + 12) 1) (cfg D (k + 2) 0 && cfg D (k + 2) 2)
        (selfB (cfg D (k + 2))) (cfg D (k + 3) 0 && cfg D (k + 3) 2)
        (cfg D (k + 13) 0) (cfg D (k + 13) 1) (cfg D (k + 13) 2)
        (cfg D (k + 0) 0) (cfg D (k + 0) 1) (cfg D (k + 0) 2)
        (cfg D (k + 1) 0) (cfg D (k + 1) 1) (cfg D (k + 1) 2) + b) :
    Psi (cfg (D ∪ N)) ≤ Psi (cfg D) + b := by
  rw [← psi_rot (cfg (D ∪ N)) k, ← psi_rot (cfg D) k]
  apply anchor0 _ _ b
  · intro j c h
    simp only [cfg, decide_eq_true_eq] at h ⊢
    exact Finset.mem_union_left _ h
  · intro j h1 h2
    funext c
    have hn : token (k + j) c ∉ N := fun h => by
      rcases tok_N4 k j c (hN _ h) with ⟨e, _⟩ | ⟨e, _⟩
      · exact h1 e
      · exact h2 e
    simp [cfg, hn]
  · have hn : token (k + 13) 2 ∉ N := fun h => by
      rcases tok_N4 k 13 2 (hN _ h) with ⟨_, e⟩ | ⟨e, _⟩
      · exact e rfl
      · exact absurd e (by decide)
    simp [cfg, hn]
  · have hn : token (k + 1) 1 ∉ N := fun h => by
      rcases tok_N4 k 1 1 (hN _ h) with ⟨e, _⟩ | ⟨_, e⟩
      · exact absurd e (by decide)
      · exact e rfl
    simp [cfg, hn]
  · exact hloc

private theorem new_mem {D N : Finset V} {x : V}
    (h1 : decide (x ∈ D ∪ N) = true) (h2 : decide (x ∈ D) = false) : x ∈ N := by
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_union] at h1 h2
  tauto

private theorem mono_bit {D N : Finset V} {x : V} :
    decide (x ∈ D) = true → decide (x ∈ D ∪ N) = true := by
  simp only [decide_eq_true_eq, Finset.mem_union]
  exact Or.inl

private theorem self_of {s : Fin 3 → Bool} : (s 0 && s 1) = true → selfB s = true := by
  simp only [selfB, Bool.and_eq_true, Bool.or_eq_true]
  tauto

private theorem self_of' {s : Fin 3 → Bool} : (s 0 && s 2) = true → selfB s = true := by
  simp only [selfB, Bool.and_eq_true, Bool.or_eq_true]
  tauto

private theorem anchor_twin (D N : Finset V) (k : Fin 14) (hN : ∀ v ∈ N, v ∈ N4 k)
    (htw : ∀ u ∈ N, ∀ v ∈ N, ∀ w, w ∉ D → G u w = G v w) :
    Psi (cfg (D ∪ N)) ≤ Psi (cfg D) + 1 := by
  have del : ∀ {u v w : V}, u ∈ N → v ∈ N → G u w = true → G v w = false → decide (w ∈ D) = true := by
    intro u v w hu hv h1 h2
    by_contra hw
    have hw' : w ∉ D := by simpa using hw
    have := htw u hu v hv w hw'
    rw [h1, h2] at this
    exact Bool.noConfusion this
  have del' : ∀ {u v w : V}, u ∈ N → v ∈ N → G u w = false → G v w = true → decide (w ∈ D) = true :=
    fun hu hv h1 h2 => del hv hu h2 h1
  obtain ⟨⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩,
    ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16⟩⟩ := gfacts k
  apply anchorD D N k 1 hN
  apply local_twin
  · exact mono_bit
  · exact mono_bit
  · exact mono_bit
  · exact mono_bit
  · intro h1 h2 h3 h4
    have u := new_mem h1 h2
    have v := new_mem h3 h4
    simp only [Bool.and_eq_true]
    exact ⟨del u v p1 q1, del u v p2 q2⟩
  · intro h1 h2 h3 h4
    have u := new_mem h1 h2
    have v := new_mem h3 h4
    simp only [Bool.and_eq_true]
    exact ⟨del u v p9 q3, del u v p10 q4⟩
  · intro h1 h2 h3 h4
    have u := new_mem h1 h2
    have v := new_mem h3 h4
    exact ⟨del' u v q5 p12, del u v p6 q6⟩
  · intro h1 h2 h3 h4
    have u := new_mem h1 h2
    have v := new_mem h3 h4
    simp only [Bool.and_eq_true]
    exact ⟨⟨del u v p1 q15, del u v p2 q16⟩, del' u v q7 p12, del u v p4 q6⟩
  · intro h1 h2 h3 h4
    have u := new_mem h1 h2
    have v := new_mem h3 h4
    simp only [Bool.and_eq_true]
    exact ⟨del' u v q5 p8, del u v p6 q8, del' u v q9 p9, del' u v q10 p10⟩
  · intro h1 h2 h3 h4
    have u := new_mem h1 h2
    have v := new_mem h3 h4
    simp only [Bool.and_eq_true]
    exact ⟨⟨del u v p1 q13, del u v p2 q14⟩, del' u v q7 p8, del u v p4 q8,
      ⟨del' u v q11 p9, del' u v q12 p10⟩⟩
  · exact self_of
  · exact self_of'

private theorem anchor_iso (D N : Finset V) (k : Fin 14) (hN : ∀ v ∈ N, v ∈ N4 k)
    (hiso : ∀ u ∈ N, ∀ w, w ∉ D → G u w = false) :
    Psi (cfg (D ∪ N)) ≤ Psi (cfg D) := by
  have adj : ∀ {u w : V}, u ∈ N → G u w = true → decide (w ∈ D) = true := by
    intro u w hu h
    by_contra hw
    have hw' : w ∉ D := by simpa using hw
    rw [hiso u hu w hw'] at h
    exact Bool.noConfusion h
  obtain ⟨⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩, -⟩ := gfacts k
  have h := anchorD D N k 0 hN (by
    apply local_iso
    · exact mono_bit
    · exact mono_bit
    · exact mono_bit
    · exact mono_bit
    · intro h1 h2
      have u := new_mem h1 h2
      simp only [Bool.and_eq_true]
      exact ⟨⟨adj u p1, adj u p2⟩, adj u p3, adj u p4⟩
    · intro h1 h2
      have u := new_mem h1 h2
      exact ⟨adj u p5, adj u p6⟩
    · intro h1 h2
      have u := new_mem h1 h2
      simp only [Bool.and_eq_true]
      exact ⟨adj u p7, adj u p8, adj u p9, adj u p10⟩
    · intro h1 h2
      have u := new_mem h1 h2
      exact ⟨adj u p11, adj u p12⟩
    · exact self_of
    · exact self_of')
  simpa using h

private theorem token_surj : ∀ w : V, ∃ k c, token k c = w := by decide +kernel

private theorem nbr_N4 : ∀ (k : Fin 14) (c : Fin 3) (v : V), G v (token k c) = true → v ∈ N4 k := by
  decide +kernel

private theorem in_N4 : ∀ v : V, ∃ k, v ∈ N4 k := by decide +kernel

private theorem iso_all (D N : Finset V) (hiso : ∀ u ∈ N, ∀ w, w ∉ D → G u w = false) :
    Psi (cfg (D ∪ N)) ≤ Psi (cfg D) := by
  induction N using Finset.induction_on with
  | empty => simp
  | @insert u N hu ih =>
    have h1 := ih (fun v hv => hiso v (Finset.mem_insert_of_mem hv))
    obtain ⟨k, hk⟩ := in_N4 u
    have h2 := anchor_iso (D ∪ N) {u} k (by simpa using hk) (by
      intro v hv w hw
      rw [Finset.mem_singleton] at hv
      subst hv
      exact hiso _ (Finset.mem_insert_self _ _) w (fun h => hw (Finset.mem_union_left _ h)))
    have e : D ∪ insert u N = (D ∪ N) ∪ {u} := by
      rw [Finset.union_insert, Finset.insert_eq, Finset.union_comm {u} (D ∪ N)]
    rw [e]
    omega

-- Each twin set raises the potential by at most one.
private theorem key (D N : Finset V) (htw : ∀ u ∈ N, ∀ v ∈ N, ∀ w, w ∉ D → G u w = G v w) :
    Psi (cfg (D ∪ N)) ≤ Psi (cfg D) + 1 := by
  by_cases hc : ∃ u ∈ N, ∃ w, w ∉ D ∧ G u w = true
  · obtain ⟨u, hu, w, hw, huw⟩ := hc
    obtain ⟨k, c, rfl⟩ := token_surj w
    exact anchor_twin D N k (fun v hv => nbr_N4 k c v ((htw v hv u hu _ hw).trans huw)) htw
  · push_neg at hc
    have h := iso_all D N (fun u hu w hw => by simpa using hc u hu w hw)
    omega

private def absent (R C : Finset (Fin 21)) : Finset V :=
  ((Finset.univ \ R).image Sum.inl) ∪ ((Finset.univ \ C).image Sum.inr)

private theorem absent_left {R C : Finset (Fin 21)} (a : Fin 21) :
    Sum.inl a ∉ absent R C ↔ a ∈ R := by simp [absent]

private theorem absent_right {R C : Finset (Fin 21)} (a : Fin 21) :
    Sum.inr a ∉ absent R C ↔ a ∈ C := by simp [absent]

private theorem psi_bic (R C : Finset (Fin 21)) (h : Bic A R C) : 14 ≤ Psi (cfg (absent R C)) := by
  let D := absent R C
  have hG : ∀ a b c d : V, a ∉ D → b ∉ D → c ∉ D → d ∉ D →
      G a c = true → G b c = true → G a d = true → G b d = true := by
    intro a b c d ha hb hc hd hac hbc had
    cases a <;> cases b <;> cases c <;> cases d <;> simp only [G] at *
    all_goals try contradiction
    · exact h _ ((absent_left _).1 ha) _ ((absent_left _).1 hb)
        _ ((absent_right _).1 hc) _ ((absent_right _).1 hd) hac hbc had
    · exact h _ ((absent_left _).1 hc) _ ((absent_left _).1 hd)
        _ ((absent_right _).1 ha) _ ((absent_right _).1 hb) hac had hbc
  have hres : ∀ j, termR (cfg D) j = 1 := by
    intro j
    rcases resolved D hG j with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [termR, resF, selfB, cfg, h0]
    · simp [termR, resF, selfB, cfg, h1, h2]
    · simp [termR, resF, selfB, cfg, h1, h2]
    · simp [termR, resF, selfB, cfg, h1, h2]
  have hs : ∑ j, termR (cfg D) j = 14 := by simp [hres]
  have hs' : ∑ j, termR (cfg (absent R C)) j = 14 := hs
  unfold Psi
  omega

private theorem rank_psi : ∀ (k : ℕ) (R C : Finset (Fin 21)), Rank A k R C →
    14 ≤ Psi (cfg (absent R C)) + 2 * k := by
  intro k
  induction k with
  | zero =>
    intro R C h
    have := psi_bic R C h
    omega
  | succ k ih =>
    intro R C h
    obtain ⟨X, _, Y, _, hT, h⟩ := h
    have h1 := ih _ _ h
    have e1 : absent (R \ X) C = absent R C ∪ X.image Sum.inl := by
      ext v
      rcases v with a | a <;> simp [absent] <;> tauto
    have e2 : absent (R \ X) (C \ Y) = absent (R \ X) C ∪ Y.image Sum.inr := by
      ext v
      rcases v with a | a <;> simp [absent] <;> tauto
    have s1 : Psi (cfg (absent (R \ X) C)) ≤ Psi (cfg (absent R C)) + 1 := by
      rw [e1]
      apply key
      intro u hu v hv w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
      rcases w with r | c
      · rfl
      · exact hT.1 a ha b hb c ((absent_right c).1 hw)
    have s2 : Psi (cfg (absent (R \ X) (C \ Y))) ≤ Psi (cfg (absent (R \ X) C)) + 1 := by
      rw [e2]
      apply key
      intro u hu v hv w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
      rcases w with r | c
      · exact hT.2 a ha b hb r (Finset.mem_sdiff.1 ((absent_left r).1 hw)).1
      · rfl
    omega

private theorem literal_obstruction : ¬ Rank A 5 Finset.univ Finset.univ := by
  intro h
  have h1 := rank_psi 5 _ _ h
  have e : absent Finset.univ Finset.univ = ∅ := by simp [absent]
  have z : Psi (cfg ∅) = 0 := by
    simp [Psi, termR, termP, resF, selfB, piF, cfg]
  rw [e, z] at h1
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def wiresFrom (gs : List Gate) (x : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires x

private theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst i; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private def run : List Gate → ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, x => x
  | g :: gs, t, x => run gs (t + 1) (Function.update x t (g.op.eval (g.inputs.map x)))

private theorem run_eq (gs : List Gate) : ∀ w : List Bool, ∀ i,
    (wiresFrom gs w).getD i false = run gs w.length (fun j => w.getD j false) i := by
  induction gs with
  | nil => intro w i; rfl
  | cons g gs ih =>
    intro w i
    have e : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [e, ih, List.length_append, List.length_singleton, run]
    congr 2
    funext j
    rw [getD_snoc, Function.update_apply]

private theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

private theorem run_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ t (x y : ℕ → Bool), (∀ i, x i = true → y i = true) →
      ∀ o, run gs t x o = true → run gs t y o = true := by
  induction gs with
  | nil => exact fun _ x y h o => h o
  | cons g gs ih =>
    intro t x y h o
    simp only [run]
    apply ih (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) _ _ _ _ o
    intro i
    by_cases hi : i = t
    · subst i
      simpa using op_mono g (hg g (by simp)) x y h
    · simpa only [Function.update_of_ne hi] using h i

-- The cut records changes from the all-zero evaluation of the earlier gates.
private def readCut (b : List Bool) (P : Finset ℕ) (i : ℕ) : Bool :=
  b.getD i false || decide (i < b.length ∧ i ∈ P)

private def cut (gs : List Gate) (b : List Bool) (o : ℕ) (P : Finset ℕ) : Bool :=
  run gs b.length (readCut b P) o

private theorem cut_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (b : List Bool) (o : ℕ) {P Q : Finset ℕ} (h : P ⊆ Q) : cut gs b o P = true → cut gs b o Q = true := by
  apply run_mono gs hg
  intro i
  simp only [readCut, Bool.or_eq_true, decide_eq_true_eq]
  rintro (hi | ⟨hlt, hp⟩)
  · exact Or.inl hi
  · exact Or.inr ⟨hlt, h hp⟩

private theorem readCut_snoc (b : List Bool) (v : Bool) (P : Finset ℕ) (e : Bool) :
    readCut (b ++ [v]) (put b.length e P) = Function.update (readCut b P) b.length (v || e) := by
  funext i
  unfold readCut
  rw [getD_snoc, Function.update_apply]
  split_ifs with hi
  · subst i
    simp [put_mem_self]
  · have hh : i < b.length + 1 ↔ i < b.length := by omega
    simp [hh, put_mem_other hi]

private abbrev Atom := ℕ ⊕ Bool

private def readAtom (b : List Bool) (i : ℕ) : Atom :=
  if b.getD i false then .inr true else if i < b.length then .inl i else .inr false

private def val (P : Finset ℕ) : Atom → Bool
  | .inl i => decide (i ∈ P)
  | .inr b => b

private theorem val_atom (b : List Bool) (i : ℕ) (P : Finset ℕ) :
    val P (readAtom b i) = readCut b P i := by
  unfold readAtom readCut
  by_cases h : b.getD i false = true
  · simp only [h, ite_true, val, Bool.true_or]
  · have h' : b.getD i false = false := by
      cases e : b.getD i false
      · rfl
      · exact (h e).elim
    rw [h']
    by_cases e : i < b.length
    · simp only [Bool.false_eq_true, ite_false, e, ite_true, val, Bool.false_or, true_and]
    · simp only [Bool.false_eq_true, ite_false, e, val, Bool.false_or, false_and, decide_false]

private theorem atom_lt (b : List Bool) (i x : ℕ) (h : readAtom b i = .inl x) : x < b.length := by
  unfold readAtom at h
  split_ifs at h with h₁ h₂; simp_all

private def Normal (t : ℕ) (f : Finset ℕ → Bool) : Prop :=
  ∃ v : Bool, ∃ S : Finset ℕ, ∃ a : Bool,
    (∀ i ∈ S, i < t) ∧ S.card ≤ 2 ∧ (a = true → S.card = 2) ∧
    ∀ P, f P = (v || trigger S a P)

private theorem norm_const (t : ℕ) (v : Bool) : Normal t (fun _ => v) := by
  refine ⟨v, ∅, false, ?_, by simp, by simp, ?_⟩
  · simp
  · intro P; simp [trigger]

private theorem norm_atom (t : ℕ) (x : Atom) (hx : ∀ i, x = .inl i → i < t) :
    Normal t (fun P => val P x) := by
  cases x with
  | inr b => exact norm_const t b
  | inl i =>
    refine ⟨false, {i}, false, ?_, by simp, by simp, ?_⟩
    · intro j hj
      have e := Finset.mem_singleton.1 hj
      exact hx j (congrArg Sum.inl e.symm)
    · intro P; simp [trigger, val]

private def combine (a : Bool) (p q : Bool) : Bool := if a then p && q else p || q

private theorem norm_two (t : ℕ) (a : Bool) (x y : Atom)
    (hx : ∀ i, x = .inl i → i < t) (hy : ∀ i, y = .inl i → i < t) :
    Normal t (fun P => combine a (val P x) (val P y)) := by
  cases x with
  | inr b =>
    cases a <;> cases b
    · simpa [combine, val] using norm_atom t y hy
    · simpa [combine, val] using norm_const t true
    · simpa [combine, val] using norm_const t false
    · simpa [combine, val] using norm_atom t y hy
  | inl p =>
    cases y with
    | inr b =>
      cases a <;> cases b
      · simpa [combine, val] using norm_atom t (.inl p) hx
      · simpa [combine, val] using norm_const t true
      · simpa [combine, val] using norm_const t false
      · simpa [combine, val] using norm_atom t (.inl p) hx
    | inl q =>
      by_cases e : p = q
      · subst q
        cases a <;> simpa [combine] using norm_atom t (.inl p) hx
      · refine ⟨false, {p,q}, a, ?_, by simp [e], fun _ => by simp [e], ?_⟩
        · intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hx _ rfl
          · exact hy _ rfl
        · intro P
          cases a <;> simp [combine, val, trigger, Finset.insert_subset_iff, Finset.singleton_subset_iff]

private theorem norm_gate (b : List Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Normal b.length (fun P => g.op.eval (g.inputs.map (readCut b P))) := by
  rcases g with ⟨op, l⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with ⟨hop, hl⟩
  rcases l with _ | ⟨p, _ | ⟨q, l⟩⟩
  · rcases hop with rfl | rfl
    · exact norm_const _ true
    · exact norm_const _ false
  · rcases hop with rfl | rfl <;>
      simpa [GateOp.eval, val_atom] using norm_atom b.length (readAtom b p) (atom_lt b p)
  · have e : l = [] := by
      cases l with
      | nil => rfl
      | cons u l =>
        simp only [List.length_cons] at hl
        omega
    subst l
    rcases hop with rfl | rfl
    · simpa [GateOp.eval, combine, val_atom] using
        norm_two b.length true (readAtom b p) (readAtom b q) (atom_lt b p) (atom_lt b q)
    · simpa [GateOp.eval, combine, val_atom] using
        norm_two b.length false (readAtom b p) (readAtom b q) (atom_lt b p) (atom_lt b q)

private theorem cut_normal (gs : List Gate) (b : List Bool) (o : ℕ) (g : Gate)
    (v : Bool) (S : Finset ℕ) (a : Bool)
    (he : ∀ P, g.op.eval (g.inputs.map (readCut b P)) = (v || trigger S a P)) :
    cut (g :: gs) b o = fun P => cut gs (b ++ [v]) o (put b.length (trigger S a P) P) := by
  funext P
  simp only [cut, run, List.length_append, List.length_singleton, readCut_snoc, he]

-- Each gate increases the dependency count plus deletion budget by at most one.
private theorem cut_budget (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ b o, cut gs b o ∅ = false → ∃ N : Finset ℕ, ∃ k : ℕ,
    Depends (cut gs b o) N ∧ Budgets (cut gs b o) N k ∧ N.card + k ≤ gs.length + 1 := by
  induction gs with
  | nil =>
    intro b o h0
    refine ⟨{o}, 0, ?_, ?_, by simp⟩
    · intro P Q he
      have e := he o (Finset.mem_singleton_self _)
      unfold cut run readCut
      have hh : (o < b.length ∧ o ∈ P) ↔ (o < b.length ∧ o ∈ Q) := by rw [e]
      rw [decide_eq_decide.2 hh]
    · intro α β _ _ A l r R C h i hi j hj c hc d hd e₁ e₂ e₃
      have ho := (h.2.2 i hi c hc).symm.trans e₁
      have hli : l i = o := Finset.mem_singleton.1 (h.1 i hi).1
      have hrc : r c = o := Finset.mem_singleton.1 (h.2.1 c hc).1
      have hf := (h.1 i hi).2
      rw [hli] at hf
      have ht : cut [] b o {o} = true := by simpa [hli, hrc] using ho
      exact Bool.false_ne_true (hf.symm.trans ht) |>.elim
  | cons g gs ih =>
    intro b o h0
    obtain ⟨v, S, a, hS, hS2, ha, he⟩ := norm_gate b g (hg g (by simp))
    have eq := cut_normal gs b o g v S a he
    rw [eq] at h0 ⊢
    have h0' : cut gs (b ++ [v]) o ∅ = false := by
      simpa [trigger_zero S a ha, put] using h0
    obtain ⟨N, k, hd, hb, hsz⟩ := ih (fun h hh => hg h (List.mem_cons_of_mem _ hh)) _ _ h0'
    by_cases ht : b.length ∈ N
    · have htS : b.length ∉ S := fun h => (Nat.lt_irrefl _ (hS _ h))
      refine ⟨N.erase b.length ∪ S, k + (N.erase b.length ∩ S).card,
        replace_depends hd, replace_budget hd h0' hb ht htS ha, ?_⟩
      have h₁ := Finset.card_union_add_card_inter (N.erase b.length) S
      have h₂ := Finset.card_erase_of_mem ht
      have h₃ : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
      simp only [List.length_cons]
      omega
    · have e : (fun P => cut gs (b ++ [v]) o (put b.length (trigger S a P) P)) = cut gs (b ++ [v]) o := by
        funext P
        exact ignored_update hd ht P _
      rw [e]
      exact ⟨N, k, hd, hb, by simp only [List.length_cons]; omega⟩

private def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

private theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

private theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega

private theorem see_pair (C : Circuit) (i j : Fin 21) : C.eval (oneEach i j) =
    cut C.gates (List.replicate 42 false) C.output {i.val, 21 + j.val} := by
  rw [oneEach_eq]
  change (wiresFrom C.gates (inp 42 _)).getD C.output false = _
  rw [run_eq]
  unfold cut
  have hlen : (inp 42 {i.val,21 + j.val}).length = 42 := by simp [inp]
  rw [hlen, List.length_replicate]
  congr 2
  funext k
  rw [inp_getD]
  have hoff : ∀ n w, (List.replicate n false).getD w false = false := by
    intro n
    induction n with
    | zero => intro w; simp [List.getD_eq_getElem?_getD]
    | succ n ih =>
      intro w
      cases w with
      | zero => simp [List.replicate_succ, List.getD_eq_getElem?_getD]
      | succ w => simpa [List.replicate_succ, List.getD_eq_getElem?_getD] using ih w
  simp only [readCut, hoff, List.length_replicate, Bool.false_or]

private theorem rows_vary : ∀ i : Fin 21, (∃ j : Fin 21, A i j = true) ∧ (∃ j : Fin 21, A i j = false) := by decide +kernel

private theorem forced_bound : ¬ RepSizeAtMost A 46 := by
  rintro ⟨C, hg, hs, hrep⟩
  let F := cut C.gates (List.replicate 42 false) C.output
  have hm : ∀ {P Q}, P ⊆ Q → F P = true → F Q = true :=
    fun h => cut_mono C.gates (fun g hg' => (hg g hg').1) _ _ h
  have hv : ∀ a b : Fin 21, F {a.val, 21 + b.val} = A a b := by
    intro a b
    change cut C.gates (List.replicate 42 false) C.output {a.val, 21 + b.val} = A a b
    rw [← see_pair]
    exact hrep a b
  have hS₁ : ∀ a : Fin 21, F {a.val} = false := by
    intro a
    obtain ⟨b, hb⟩ := (rows_vary a).2
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {a.val, 21 + b.val}) (by simp) h
    rw [hv, hb] at h'
    contradiction
  have hS₂ : ∀ b : Fin 21, F {21 + b.val} = false := by
    intro b
    obtain ⟨a, ha⟩ := (rows_vary b).2
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {a.val, 21 + b.val}) (by simp) h
    rw [hv, A_sym, ha] at h'
    contradiction
  have h0 : F ∅ = false := by
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {0}) (by simp) h
    have e := hS₁ 0
    exact Bool.false_ne_true (e.symm.trans h')
  obtain ⟨N, k, hd, hb, hsN⟩ := cut_budget C.gates hg _ _ h0
  have hN₁ : ∀ a : Fin 21, a.val ∈ N := by
    intro a
    obtain ⟨b, hb⟩ := (rows_vary a).1
    by_contra h
    have e : F {a.val, 21 + b.val} = F {21 + b.val} := by
      apply hd
      intro i hi
      have hne : i ≠ a.val := fun e => h (e ▸ hi)
      simp [hne]
    rw [hv, hb, hS₂] at e
    contradiction
  have hN₂ : ∀ b : Fin 21, 21 + b.val ∈ N := by
    intro b
    obtain ⟨a, ha⟩ := (rows_vary b).1
    by_contra h
    have e : F {a.val, 21 + b.val} = F {a.val} := by
      apply hd
      intro i hi
      have hne : i ≠ 21 + b.val := fun e => h (e ▸ hi)
      simp [hne]
    rw [hv, A_sym, ha, hS₁] at e
    contradiction
  have hN : Finset.range 42 ⊆ N := by
    intro i hi
    have hh := Finset.mem_range.1 hi
    by_cases h : i < 21
    · exact hN₁ ⟨i, h⟩
    · have hey := hN₂ ⟨i - 21, by omega⟩
      simpa [Nat.add_sub_of_le (by omega : 21 ≤ i)] using hey
  have hc := Finset.card_le_card hN
  rw [Finset.card_range] at hc
  have hsz : C.gates.length ≤ 46 := hs
  have hR := hb A Fin.val (fun b => 21 + b.val) Finset.univ Finset.univ
    ⟨fun a _ => ⟨hN₁ a, hS₁ a⟩, fun b _ => ⟨hN₂ b, hS₂ b⟩, fun a _ b _ => (hv a b).symm⟩
  have hk : k ≤ 5 := by omega
  apply literal_obstruction
  interval_cases k
  · exact rank_pad (rank_pad (rank_pad (rank_pad (rank_pad hR))))
  · exact rank_pad (rank_pad (rank_pad (rank_pad hR)))
  · exact rank_pad (rank_pad (rank_pad hR))
  · exact rank_pad (rank_pad hR)
  · exact rank_pad hR
  · exact hR

end PEqualNP.Outside.L_meta_9490

theorem PEqualNP.Outside.L_meta_9490 : ¬ PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 21 => decide (∃ i : Fin 7, ((a.val = i.val ∨ a.val = 7 + i.val) ∧ (b.val = (i.val + 1) % 7 ∨ b.val = 14 + i.val)) ∨ ((b.val = i.val ∨ b.val = 7 + i.val) ∧ (a.val = (i.val + 1) % 7 ∨ a.val = 14 + i.val)))) 46 := by
  exact PEqualNP.Outside.L_meta_9490.forced_bound
