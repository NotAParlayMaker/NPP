import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Image
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Intervals
import PEqualNP.Defs


-- The finite search specializes the Petersen graph search by Trey Kind in L_meta_1673.
-- Each checkpoint records the remaining signals and their budgets on restricted inputs.
namespace PEqualNP.Outside.L_meta_2766

def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]

inductive Sol (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : False → Sol m T q (insert (a ^^^ m) S) → Sol m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S →
      Sol m T q (insert (op d a b) S) → Sol m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un bad => exact False.elim bad
  | bi h1 h2 _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) (ih (by omega) (Set.insert_subset_insert hs))

inductive Live (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : False → Live m T k t (insert (a ^^^ m) U) →
      Live m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Live m T k t (insert (op d a b) U) →
      Live m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : Sol m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | un bad => exact False.elim bad
  | @bi k t d a b U _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | un bad => exact False.elim bad
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

def Un (_m _a : ℕ) (_S _S' : Finset ℕ) : Prop := False
def Bi (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S') :
    Live m T (k + 1) (t + 1) S := False.elim h
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S') :
    Live m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl⟩ := h; exact .bi hab hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') : Bi d b a S S' := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm]⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := False.elim h
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]

def Min (m T k t : ℕ) (S : Finset ℕ) : Prop := Live m T k t S ∧ ∀ q < k, ¬ Sol m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol m T q (C m S')) :
    Sol m T (q + 1) (C m S) := False.elim h
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
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : Min m T k t S' := False.elim h
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : Min m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : a ^^^ m ∉ C m S := False.elim h
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
  | un bad => exact False.elim bad
  | @bi k t d a b U hab hl ih =>
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega

def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
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
  | un bad => exact False.elim bad
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
    Sol n (T &&& n) (q + 1) (C n (Im n S)) := False.elim h
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) q (C n (Im n S)) := False.elim h
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
  | un bad => exact False.elim bad
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
  | un bad => exact False.elim bad
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
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live m T k 0 S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un bad => exact False.elim bad
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
  | un bad => exact False.elim bad
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
  | un bad => exact False.elim bad
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
def nots (f : Nat → Nat → List W → Bool) (d : Bool) (l m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) d l g e (Nat.succ n) (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) d l g e n (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
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
  | un bad => exact False.elim bad
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
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := False.elim hb
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {d : Bool} {l m g e n z q : ℕ} {v r : List W} (h : nots f d l m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f d l m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
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
          else nots f d l m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f d l m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {d : Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Un m a.s S S') (hl : Live m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f d l m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hsz := hmin.size
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
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
    {go : (L_meta_2766.X → L_meta_2766.X → Bool) → List L_meta_2766.X → Bool}
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
    (hA : ∀ x y : ℕ, x ≠ y → KP x y → ∃ go : (L_meta_2766.X → L_meta_2766.X → Bool) → List L_meta_2766.X → Bool,
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
    have : Std.Symm (fun a c : L_meta_2766.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
    refine (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_
    intro e
    have : a.s = c.s := congrArg L_meta_2766.X.s e
    exact hxy (by rw [← hax, ← hcy, this])
end sound
def rawP : List ℕ := [0x1ffff8000000007fffe000f8000007fffc07c000000003e003c00000000000000001f03ffff03c00000000000000000000000f83e00e000020c00800086060800008c0ca44000080948800085032910410204200288610001004a8402001108ca8408000010822020b0844a880000000821511012a20042a221951014a880a888000000000000000010290417e052000852085ad14800be0008a51e2901f002100252f802f0005482002a4108217c089ea40f00800690800690410442120be0f80b80a40830020016181860000230300000002020000006b40c00010c0810801a218400040100000802c4630000601080c6188186c2110000000a8161afffe04000035fffc60000d00007fff2cb20284c2023205, 0x7fffc07c00000000003e00000003e0000000000000000f81ffff80078000000000000000000000000000000ffffc0ffffc001f003c3e00000e000040202208843010100010002102183080620460842018408c0a000000100100230c0310431810841210431000808010000400101043860888410a08c0c41182141184208c21046904700000000000000001f04301f02086001086f80012182f8200110c02430410be046e86081e1000a1840050c210420420030c2121127c30127c30027c04f0f82008b8810d0080882210c04060004000800000c20180000230806000016c000000c02c058c300c000060421068000060460610c0043002d57fff1862210c2000030000184000100000d7fff7fff605989290008a0c3, 0x1ffff8007fffef80000000000000000000000000000003fffe0000007c0f80003ffff7803e0000000000007c0078000003ee00000000000001000024208c00d806141800b00c282098140185050401000800024080008061400020000461482140405808160120506281012010260c502018a04c18a008c510462906280000000000000000020860820410c16b90c101ad433e100002218048608210420050c1044228bc30002819f03e00848be19e00f8088600088609f081e201042fb90021800000002c0005b08230036000006002c0000083605000001610040060281b020002000000058150b7fff08503016020580d814000040682c0d80000800001b000016fffe17fff00004840d0f006c20810, 0x7fffdf000001ffffbef0000000003ffff000001f78000000000000000ffffdf00000003efb8000000002800000001240002000a000068800a0000d2000000901a60002c02400ab00000d6000c90a40055800c9004009b000240024b000d102400a58001a405034a000348501a6300d200d200000000000000000421410408428202428208060a042042140513e147c000844ee28fbc000110a0899e50400847de104504002041141165d47c4000844fbee110008500a00002800db0000800280000000028000000a80056dfffc000b00b002ac0000358000006b00156000000b0036c002b000dac000005b002d6000000b5fffc0000016fffec00000000000004525d9ab670, 0x7fffdf00000001ffffbef00000000003ffff000000000fbc00000000003fffef80000000fbc00000000003effffde00000000007bd8000000000005800280ab500000280d600014911b600029242ad2800524800580009b400000b600015121096a00015120295a00000894d00001522149aa00002a4828549469549402a4801524152400000000000000001f0187c01003006b830fbc080c0000808f860081810403ef0083020804089cc3e01060003ef10800860020f925d8780118100001ef62084200100616000a02ad600000a035800000006d80000000ab6b0000000016000b6d800002d800000006b5ac00000000b56800002b5b6000000005b6a800000000b5fffdb5fffc000000000000004c32000238851dce, 0x3fffefbffff7de00000000000003effffdeffffdf7df70000000000000000000000000000002aa000000019892a1200370000000006c00485080000000092429001b80000000001b02d5ada53400000000003316daab534806e0000d80000d80006c00036003600000000000000000852020820a4040c2404103090084104284805120208210813040410884add03eade81f780020025080040f9b5e079b5e07df7dc0000100400214800000aa800000000aa80000000006daadafffe00000000000016b56000000002db5ad7fff0000000000000b56b6d6d80000000000005b6aad6dafffe00000000000000000000000000940c0523a2600210, 0x3ffff7fffdf7de00000000000003fffefbffff7defbdf7bffff7bd8000000000000000000000000000000000a84800000000002aa42a4840de00000001b800000000370005ad5ada6aa6d400000019c00000000019c02d52d35a6ad69b6a541bc00000000003700006e00006e000370001b801b800000000000000001084041041080830080820c020108208cf9019e407df7a0024080001000c9e03ec9f01f7bef7dec9f01ef60206000206000001000804000002021016ab600000000000aab5ab6b7fff000000000000000000000016b56b6daadb580000000000000000000000b56b6d6dab5b6dad57fff000000000000000000000000000000000000000a180bb188920c1a4, 0x7fffdf7dffffbc000000000000000003ffff7fffdf7defbdffffbef7bd8000000000000000000000000000000000000000000000000000000000005aadaaaaa5b6d498000000018e000000031c0000000063800012852d36ab4962494259e01ad4b55a99e018000000000000000019c0000000000338000670000670003380019c019c000000000000000001f1807df7e300f4030000100c02000008fe011f807df7bef47f00fbdef60e00100e000821000000e0008004038002038002082090000000820006016ab6aaaad6db5b6000000000000000000000000000000000016b56b6daadb5adb5ad7fff6b5ad56b7fff6000000000000000000000000000000000000000000000000000000000000130220c900310c00, 0x7fffdf7dffffbdffffbef7fffefbefb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000050292aaab5a496d800940929f001240a4be002adad527c005b0000000000000000001e00000000001e000000000000000000001e000000000003c0000780000780003c0001e001e0000000000000000001fe007df7fc00f7fc00fbdff003efbeef0001e000410400078000820000f00020f000104208410f000108483c00043c0004104100008208000038016ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000092683e00754c0101]
def rawL : List ℕ := rawP ++ [rawP.getD 0 0 ||| rawP.getD 3 0]
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7ffffc7abffbffeabfd5
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
noncomputable section packed0
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end packed0
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
noncomputable section packed1
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
def startv (l m g B K t H HN : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H HN K t z r) (pos t) l g (Nat.sub (Nat.succ K) t) v.length (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (Nat.beq (cov (pos t) l v) l)
end packed1
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
  have : Std.Symm (fun a b : L_meta_2766.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
    ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
  refine (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
    (List.mem_map_of_mem ha) (List.mem_map_of_mem hb') ?_ ?_
  · intro e
    have : a.s = b.s := congrArg L_meta_2766.X.s e
    exact hxy (by rw [← hax, ← hby, this])
  · change hb p.1 (a.s + b.s) = true; rw [hax, hby]; exact hpx
def tab : List (ℕ × ℕ) := [(19, 8), (25, 8), (28, 8), (49, 8), (67, 8), (70, 7), (81, 8), (82, 8), (88, 8), (134, 7), (140, 8), (145, 8), (148, 8), (152, 8), (161, 8), (164, 7), (176, 8), (194, 7), (196, 7), (208, 8), (224, 7), (280, 8), (322, 7), (328, 8), (336, 8), (352, 7), (416, 7), (448, 7), (7, 7), (14, 7), (21, 7), (26, 7), (35, 7), (56, 7), (74, 7), (84, 7), (98, 6), (112, 7), (133, 7), (146, 7), (162, 6), (168, 7), (193, 7), (200, 7), (268, 7), (273, 7), (289, 7), (296, 7), (321, 7), (324, 6), (388, 6), (400, 7), (22, 6), (76, 6), (97, 6), (131, 6), (304, 6), (392, 6), (11, 5), (13, 5), (37, 5), (38, 4), (41, 5), (42, 5), (44, 5), (50, 5), (52, 5), (69, 5), (73, 5), (100, 5), (104, 5), (137, 5), (138, 5), (259, 5), (261, 5), (262, 4), (265, 5), (266, 5), (274, 5), (276, 5), (290, 4), (292, 4), (385, 5), (386, 5), (17, 11), (24, 11), (66, 10), (80, 11), (132, 10), (144, 11), (160, 10), (192, 10), (320, 10), (3, 9), (6, 8), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 8), (384, 9), (5, 8), (9, 8), (10, 8), (34, 7), (36, 7), (40, 8), (257, 8), (258, 7), (260, 7), (16, 13), (64, 13), (128, 13), (1, 12), (2, 11), (4, 11), (8, 12), (32, 11), (256, 11)]
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
    (hb : (∃ e ∈ pr Z, L ≤ e.2) ∨ ∀ t < L, t=0 → ∃ M : List (ℕ × ℕ), M ≠ [] ∧ (∀ p ∈ M, chk Z (L - 1) t p.1 p.2 = false) ∧
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
  have tz0 : t=0 := by
    have hh := hm.1
    clear * - hh
    induction hh with
    | stop => rfl
    | un bad => exact bad.elim
    | bi _ _ ih => exact ih
  obtain ⟨M, hM, hchk, hsym⟩ := hb t (by omega) tz0
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
      simp only [startv, bR, hcov, hble, Bool.cond_true] at h3
      exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) (pos_eq t) rfl rfl h3
    obtain ⟨p0, hp0M⟩ := List.exists_mem_of_ne_nil M hM
    have hlen := (topC_succ (all p0 hp0M)).1
    exact ⟨by rw [hcard]; exact hlen, topC_sound X hlen all hst k (by omega) hm⟩
  obtain ⟨S', hS', hm', hfm⟩ := hsym k S hSW hm (key S hSW hm).1
  exact (key S' hS' hm').2 hfm

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

theorem splitImp {Z L : ℕ} {M : List (ℕ × ℕ)} (hp : pOk Z = true) (hL : L ≤ 15)
    (hI : ∀ e∈pr Z, Imp e.1 e.2) (ne : M≠[]) (full : kFull M=true)
    (checks : ∀ p∈M, chk Z (L-1) 0 p.1 p.2=false) : Imp Z L := by
  apply imp_of hp hL hI (Or.inr ?_)
  intro t _ ht
  subst t
  exact ⟨M, ne, checks, sym_full full⟩
theorem monotoneImp {Z L : ℕ} (hp : pOk Z=true) (hL : L ≤ 15) (hI : ∀ e∈pr Z,Imp e.1 e.2)
    (hz : chk Z (L-1) 0 FF FF = false) : Imp Z L := by
  apply imp_of hp hL hI (Or.inr ?_)
  intro t _ ht
  subst t
  refine ⟨[(FF,FF)],by simp,by simpa using hz,?_⟩
  intro k S hS hm hc
  exact ⟨S,hS,hm,FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF,FF),by simp,hbF _⟩) (fun x _ => ⟨(FF,FF),by simp,hbF _⟩)⟩

def BoundStep (e : ℕ × ℕ) := (∀ u∈pr e.1, Imp u.1 u.2) → Imp e.1 e.2
def tab3 : List (ℕ × ℕ) := [(19, 8), (25, 8), (28, 8), (49, 8), (67, 8), (70, 7), (81, 8), (82, 8), (88, 8), (134, 7), (140, 8), (145, 8), (148, 8), (152, 8), (161, 8), (164, 7), (176, 8), (194, 7), (196, 7), (208, 8), (224, 7), (280, 8), (322, 7), (328, 8), (336, 8), (352, 7), (416, 7), (448, 7), (7, 7), (14, 7), (21, 7), (26, 7), (35, 7), (56, 7), (74, 7), (84, 7), (98, 6), (112, 7), (133, 7), (146, 7), (162, 6), (168, 7), (193, 7), (200, 7), (268, 7), (273, 7), (289, 7), (296, 7), (321, 7), (324, 6), (388, 6), (400, 7), (22, 6), (76, 6), (97, 6), (131, 6), (304, 6), (392, 6), (11, 5), (13, 5), (37, 5), (38, 4), (41, 5), (42, 5), (44, 5), (50, 5), (52, 5), (69, 5), (73, 5), (100, 5), (104, 5), (137, 5), (138, 5), (259, 5), (261, 5), (262, 4), (265, 5), (266, 5), (274, 5), (276, 5), (290, 4), (292, 4), (385, 5), (386, 5)]
def tab2 : List (ℕ × ℕ) := [(17, 11), (24, 11), (66, 10), (80, 11), (132, 10), (144, 11), (160, 10), (192, 10), (320, 10), (3, 9), (6, 8), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 8), (384, 9), (5, 8), (9, 8), (10, 8), (34, 7), (36, 7), (40, 8), (257, 8), (258, 7), (260, 7)]
def tab1 : List (ℕ × ℕ) := [(16, 13), (64, 13), (128, 13), (1, 12), (2, 11), (4, 11), (8, 12), (32, 11), (256, 11)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr3 : tab3.all (fun e => (pr e.1).isEmpty) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr2 : tab2.all (fun e => (pr e.1).all (fun x => tab3.contains x)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr1 : tab1.all (fun e => (pr e.1).all (fun x => tab2.contains x || tab3.contains x)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr0 : (pr 0).all (fun x => tab1.contains x || tab2.contains x || tab3.contains x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk19 : chk 19 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full19 : BoundStep (19,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk25 : chk 25 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full25 : BoundStep (25,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk25
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk28 : chk 28 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full28 : BoundStep (28,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk28
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk49 : chk 49 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full49 : BoundStep (49,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk49
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk67 : chk 67 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full67 : BoundStep (67,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk67
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk70 : chk 70 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full70 : BoundStep (70,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk81 : chk 81 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full81 : BoundStep (81,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk81
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk82 : chk 82 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full82 : BoundStep (82,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk82
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk88 : chk 88 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full88 : BoundStep (88,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk88
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk134 : chk 134 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full134 : BoundStep (134,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk134
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk140 : chk 140 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full140 : BoundStep (140,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk140
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk145 : chk 145 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full145 : BoundStep (145,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk145
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk148 : chk 148 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full148 : BoundStep (148,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk148
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk152 : chk 152 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full152 : BoundStep (152,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk152
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk161 : chk 161 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full161 : BoundStep (161,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk161
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk164 : chk 164 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full164 : BoundStep (164,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk164
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk176 : chk 176 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full176 : BoundStep (176,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk176
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk194 : chk 194 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full194 : BoundStep (194,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk194
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk196 : chk 196 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full196 : BoundStep (196,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk196
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk208 : chk 208 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full208 : BoundStep (208,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk208
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk224 : chk 224 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full224 : BoundStep (224,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk224
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk280 : chk 280 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full280 : BoundStep (280,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk280
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk322 : chk 322 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full322 : BoundStep (322,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk322
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk328 : chk 328 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full328 : BoundStep (328,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk328
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk336 : chk 336 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full336 : BoundStep (336,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk336
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk352 : chk 352 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full352 : BoundStep (352,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk352
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk416 : chk 416 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full416 : BoundStep (416,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk416
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk448 : chk 448 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full448 : BoundStep (448,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk448
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk7 : chk 7 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full7 : BoundStep (7,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk14 : chk 14 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full14 : BoundStep (14,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk14
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk21 : chk 21 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full21 : BoundStep (21,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk21
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk26 : chk 26 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full26 : BoundStep (26,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk26
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk35 : chk 35 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full35 : BoundStep (35,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk35
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk56 : chk 56 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full56 : BoundStep (56,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk74 : chk 74 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full74 : BoundStep (74,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk74
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk84 : chk 84 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full84 : BoundStep (84,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk84
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk98 : chk 98 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full98 : BoundStep (98,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk98
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk112 : chk 112 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full112 : BoundStep (112,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk112
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk133 : chk 133 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full133 : BoundStep (133,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk133
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk146 : chk 146 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full146 : BoundStep (146,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk146
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk162 : chk 162 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full162 : BoundStep (162,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk162
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk168 : chk 168 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full168 : BoundStep (168,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk168
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk193 : chk 193 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full193 : BoundStep (193,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk193
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk200 : chk 200 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full200 : BoundStep (200,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk200
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk268 : chk 268 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full268 : BoundStep (268,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk268
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk273 : chk 273 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full273 : BoundStep (273,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk273
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk289 : chk 289 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full289 : BoundStep (289,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk289
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk296 : chk 296 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full296 : BoundStep (296,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk296
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk321 : chk 321 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full321 : BoundStep (321,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk321
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk324 : chk 324 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full324 : BoundStep (324,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk324
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk388 : chk 388 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full388 : BoundStep (388,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk388
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk400 : chk 400 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full400 : BoundStep (400,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk400
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk22 : chk 22 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full22 : BoundStep (22,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk22
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk76 : chk 76 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full76 : BoundStep (76,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk76
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk97 : chk 97 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full97 : BoundStep (97,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk97
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk131 : chk 131 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full131 : BoundStep (131,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk131
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk304 : chk 304 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full304 : BoundStep (304,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk304
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk392 : chk 392 5 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full392 : BoundStep (392,6) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk392
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk11 : chk 11 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full11 : BoundStep (11,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk13 : chk 13 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full13 : BoundStep (13,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk13
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk37 : chk 37 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full37 : BoundStep (37,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk37
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk38 : chk 38 3 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full38 : BoundStep (38,4) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk38
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk41 : chk 41 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full41 : BoundStep (41,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk41
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk42 : chk 42 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full42 : BoundStep (42,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk42
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk44 : chk 44 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full44 : BoundStep (44,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk44
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk50 : chk 50 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full50 : BoundStep (50,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk50
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk52 : chk 52 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full52 : BoundStep (52,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk52
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk69 : chk 69 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full69 : BoundStep (69,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk69
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk73 : chk 73 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full73 : BoundStep (73,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk73
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk100 : chk 100 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full100 : BoundStep (100,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk100
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk104 : chk 104 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full104 : BoundStep (104,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk104
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk137 : chk 137 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full137 : BoundStep (137,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk137
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk138 : chk 138 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full138 : BoundStep (138,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk138
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk259 : chk 259 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full259 : BoundStep (259,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk259
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk261 : chk 261 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full261 : BoundStep (261,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk261
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk262 : chk 262 3 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full262 : BoundStep (262,4) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk262
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk265 : chk 265 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full265 : BoundStep (265,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk265
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk266 : chk 266 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full266 : BoundStep (266,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk266
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk274 : chk 274 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full274 : BoundStep (274,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk274
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk276 : chk 276 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full276 : BoundStep (276,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk276
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk290 : chk 290 3 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full290 : BoundStep (290,4) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk290
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk292 : chk 292 3 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full292 : BoundStep (292,4) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk292
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk385 : chk 385 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full385 : BoundStep (385,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk385
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk386 : chk 386 4 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full386 : BoundStep (386,5) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk386
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk17 : chk 17 10 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full17 : BoundStep (17,11) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk17
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk24 : chk 24 10 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full24 : BoundStep (24,11) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk66 : chk 66 9 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full66 : BoundStep (66,10) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk66
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk80 : chk 80 10 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full80 : BoundStep (80,11) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk132 : chk 132 9 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full132 : BoundStep (132,10) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk132
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk144 : chk 144 10 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full144 : BoundStep (144,11) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk144
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk160 : chk 160 9 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full160 : BoundStep (160,10) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk160
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk192 : chk 192 9 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full192 : BoundStep (192,10) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk320 : chk 320 9 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full320 : BoundStep (320,10) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk320
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk3 : chk 3 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full3 : BoundStep (3,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk6 : chk 6 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full6 : BoundStep (6,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk12 : chk 12 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full12 : BoundStep (12,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk18 : chk 18 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full18 : BoundStep (18,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk20 : chk 20 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full20 : BoundStep (20,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk33 : chk 33 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full33 : BoundStep (33,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk33
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk48 : chk 48 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full48 : BoundStep (48,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk65 : chk 65 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full65 : BoundStep (65,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk65
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk68 : chk 68 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full68 : BoundStep (68,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk68
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk72 : chk 72 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full72 : BoundStep (72,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk96 : chk 96 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full96 : BoundStep (96,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk129 : chk 129 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full129 : BoundStep (129,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk129
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk130 : chk 130 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full130 : BoundStep (130,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk130
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk136 : chk 136 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full136 : BoundStep (136,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk136
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk264 : chk 264 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full264 : BoundStep (264,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk264
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk272 : chk 272 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full272 : BoundStep (272,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk272
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk288 : chk 288 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full288 : BoundStep (288,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk288
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk384 : chk 384 8 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full384 : BoundStep (384,9) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk384
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk5 : chk 5 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full5 : BoundStep (5,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk9 : chk 9 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full9 : BoundStep (9,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk10 : chk 10 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full10 : BoundStep (10,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk34 : chk 34 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full34 : BoundStep (34,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk34
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk36 : chk 36 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full36 : BoundStep (36,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk36
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk40 : chk 40 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full40 : BoundStep (40,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk40
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk257 : chk 257 7 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full257 : BoundStep (257,8) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk257
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk258 : chk 258 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full258 : BoundStep (258,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk258
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk260 : chk 260 6 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full260 : BoundStep (260,7) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk260
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk1 : chk 1 11 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full1 : BoundStep (1,12) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk2 : chk 2 10 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full2 : BoundStep (2,11) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk4 : chk 4 10 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full4 : BoundStep (4,11) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk8 : chk 8 11 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full8 : BoundStep (8,12) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk32 : chk 32 10 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full32 : BoundStep (32,11) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk256 : chk 256 10 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full256 : BoundStep (256,11) := fun hI => monotoneImp (by decide +kernel) (by decide) hI chk256

def groups16 : List (ℕ × ℕ) := [(0x3ffffed7ffffffdfffffffefffffff6fffffffffffbffefdfff7bf, FF), (0x10000000000000000000000000000040, FF), (0x80000002000000000000000000000000000000002000000, FF), (0x200000000000000000000000100000000000400000000000, FF), (0x800000000000000100000800, FF), (0x1000000000000000000000000000000000000000000000000, FF)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part16_0 : chk 16 12 0 0x3ffffed7ffffffdfffffffefffffff6fffffffffffbffefdfff7bf FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part16_1 : chk 16 12 0 0x10000000000000000000000000000040 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part16_2 : chk 16 12 0 0x80000002000000000000000000000000000000002000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part16_3 : chk 16 12 0 0x200000000000000000000000100000000000400000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part16_4 : chk 16 12 0 0x800000000000000100000800 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part16_5 : chk 16 12 0 0x1000000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full16 : BoundStep (16, 13) := by
  intro hI
  apply splitImp (M := groups16) (by decide +kernel) (by decide) hI (by decide) (by decide +kernel)
  simp only [groups16, List.forall_mem_cons]
  exact ⟨part16_0, part16_1, part16_2, part16_3, part16_4, part16_5, by simp⟩
def groups64 : List (ℕ × ℕ) := [(0x40000000000000000000000000000000, FF), (0x80000000000000000000000000000000000, FF), (0x100000000000000000000000000000000000000000000000, FF), (0x3adffd4fffefff7fff57ff96ffffffffffcbfff3fff7ffffffef7f, FF), (0x800000000000000000000000000000000000, FF), (0x2000000000000000000000000000000000000000000000000000, FF), (0x8000000000000000000000000000000000000080, FF), (0x10000000000000000000000000000000000000000080000000000, FF), (0x4000000000000001000, FF), (0x40000800000000000000000000000000000000000000000000000, FF), (0x200000000000000000000000000000000000, FF), (0x2000000000000000000000000000000000000000000000000, FF), (0x20000400000000000000, FF), (0x8000000000010000000000000000000, FF), (0x200000000000000000000000000000000800000000000000, FF), (0x10000000000001000000000000000000000000000000, FF), (0x20000000000000000000000000000000, FF)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_0 : chk 64 12 0 0x40000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_1 : chk 64 12 0 0x80000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_2 : chk 64 12 0 0x100000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_3 : chk 64 12 0 0x3adffd4fffefff7fff57ff96ffffffffffcbfff3fff7ffffffef7f FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_4 : chk 64 12 0 0x800000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_5 : chk 64 12 0 0x2000000000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_6 : chk 64 12 0 0x8000000000000000000000000000000000000080 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_7 : chk 64 12 0 0x10000000000000000000000000000000000000000080000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_8 : chk 64 12 0 0x4000000000000001000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_9 : chk 64 12 0 0x40000800000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_10 : chk 64 12 0 0x200000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_11 : chk 64 12 0 0x2000000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_12 : chk 64 12 0 0x20000400000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_13 : chk 64 12 0 0x8000000000010000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_14 : chk 64 12 0 0x200000000000000000000000000000000800000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_15 : chk 64 12 0 0x10000000000001000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part64_16 : chk 64 12 0 0x20000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full64 : BoundStep (64, 13) := by
  intro hI
  apply splitImp (M := groups64) (by decide +kernel) (by decide) hI (by decide) (by decide +kernel)
  simp only [groups64, List.forall_mem_cons]
  exact ⟨part64_0, part64_1, part64_2, part64_3, part64_4, part64_5, part64_6, part64_7, part64_8, part64_9, part64_10, part64_11, part64_12, part64_13, part64_14, part64_15, part64_16, by simp⟩
def groups128 : List (ℕ × ℕ) := [(0x4000000000000000000000000000, FF), (0x20000000000000000000000000000000000000000000000, FF), (0x4000000000000000000000000000000000000000000000, FF), (0x3dffffbdbfcfffeffffcfffffd9fffeff7e7edffffff7e5fffffd7, FF), (0x20000000000000000000000000000000000000000000, FF), (0x120000000000000000, FF), (0x8000000000000000000, FF), (0x8000000020, FF), (0x810000000000000000000, FF), (0x1000000000000000000000000000000000000000, FF), (0x400000000000000000000000000000000000000000000000, FF), (0x20000000000000000000100000000, FF), (0x10000000020000000000000000000000000000000000, FF), (0x100000000000000080000000, FF), (0x10000002000000000000000000000000000, FF), (0x20000008, FF), (0x20000000000000000000000000000000000000000000000000000, FF)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_0 : chk 128 12 0 0x4000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_1 : chk 128 12 0 0x20000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_2 : chk 128 12 0 0x4000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_3 : chk 128 12 0 0x3dffffbdbfcfffeffffcfffffd9fffeff7e7edffffff7e5fffffd7 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_4 : chk 128 12 0 0x20000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_5 : chk 128 12 0 0x120000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_6 : chk 128 12 0 0x8000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_7 : chk 128 12 0 0x8000000020 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_8 : chk 128 12 0 0x810000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_9 : chk 128 12 0 0x1000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_10 : chk 128 12 0 0x400000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_11 : chk 128 12 0 0x20000000000000000000100000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_12 : chk 128 12 0 0x10000000020000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_13 : chk 128 12 0 0x100000000000000080000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_14 : chk 128 12 0 0x10000002000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_15 : chk 128 12 0 0x20000008 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma part128_16 : chk 128 12 0 0x20000000000000000000000000000000000000000000000000000 FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full128 : BoundStep (128, 13) := by
  intro hI
  apply splitImp (M := groups128) (by decide +kernel) (by decide) hI (by decide) (by decide +kernel)
  simp only [groups128, List.forall_mem_cons]
  exact ⟨part128_0, part128_1, part128_2, part128_3, part128_4, part128_5, part128_6, part128_7, part128_8, part128_9, part128_10, part128_11, part128_12, part128_13, part128_14, part128_15, part128_16, by simp⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma all3 : ∀ e ∈ tab3, BoundStep e := by
  simp only [tab3,List.forall_mem_cons]
  exact ⟨full19, full25, full28, full49, full67, full70, full81, full82, full88, full134, full140, full145, full148, full152, full161, full164, full176, full194, full196, full208, full224, full280, full322, full328, full336, full352, full416, full448, full7, full14, full21, full26, full35, full56, full74, full84, full98, full112, full133, full146, full162, full168, full193, full200, full268, full273, full289, full296, full321, full324, full388, full400, full22, full76, full97, full131, full304, full392, full11, full13, full37, full38, full41, full42, full44, full50, full52, full69, full73, full100, full104, full137, full138, full259, full261, full262, full265, full266, full274, full276, full290, full292, full385, full386, by simp⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma all2 : ∀ e ∈ tab2, BoundStep e := by
  simp only [tab2,List.forall_mem_cons]
  exact ⟨full17, full24, full66, full80, full132, full144, full160, full192, full320, full3, full6, full12, full18, full20, full33, full48, full65, full68, full72, full96, full129, full130, full136, full264, full272, full288, full384, full5, full9, full10, full34, full36, full40, full257, full258, full260, by simp⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma all1 : ∀ e ∈ tab1, BoundStep e := by
  simp only [tab1,List.forall_mem_cons]
  exact ⟨full16, full64, full128, full1, full2, full4, full8, full32, full256, by simp⟩
theorem i3 : ∀ e ∈ tab3, Imp e.1 e.2 := fun e he => (all3 e he) fun x hx => by
  have := List.all_eq_true.1 pr3 e he
  rw [List.isEmpty_iff] at this; rw [this] at hx; simp at hx
lemma up2 {e : ℕ × ℕ} (he : e ∈ tab2) : ∀ x ∈ pr e.1, Imp x.1 x.2 := fun x hx =>
  i3 x (by simpa using List.all_eq_true.1 (List.all_eq_true.1 pr2 e he) x hx)
theorem i2 : ∀ e∈tab2, Imp e.1 e.2 := fun e he => all2 e he (up2 he)
lemma up1 {e : ℕ × ℕ} (he : e ∈ tab1) : ∀ x ∈ pr e.1, Imp x.1 x.2 := fun x hx => by
  have := List.all_eq_true.1 (List.all_eq_true.1 pr1 e he) x hx
  rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem] at this
  exact this.elim (i2 x) (i3 x)
theorem i1 : ∀ e∈tab1, Imp e.1 e.2 := fun e he => all1 e he (up1 he)

abbrev Snap := ℕ × List W
def sameW (a b : W) : Bool :=
  Nat.beq a.s b.s && Nat.beq a.a b.a && Nat.beq a.b b.b && Nat.beq a.c b.c
lemma sameW_sound {a b : W} (h : sameW a b = true) : a = b := by
  cases a; cases b
  simp only [sameW, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩ := h
  rfl
def sameV : List W → List W → Bool
  | [], [] => true
  | a :: x, b :: y => sameW a b && sameV x y
  | _, _ => false
lemma sameV_sound {v r : List W} (h : sameV v r=true) : v=r := by
  induction v generalizing r with
  | nil => cases r <;> simp_all [sameV]
  | cons a v ih =>
    cases r with
    | nil => simp [sameV] at h
    | cons b r =>
      obtain ⟨hw,hr⟩ := Bool.and_eq_true_iff.mp h
      rw [sameW_sound hw,ih hr]
def listed (L : List Snap) (z : Nat) (v : List W) : Bool :=
  L.any (fun s => Nat.beq z s.1 && sameV v s.2)
lemma listed_mem {L : List Snap} {z v} (h : listed L z v=true) : (z,v)∈L := by
  obtain ⟨⟨z',v'⟩,hL, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨rfl,h⟩ := h
  rw [sameV_sound h]
  exact hL

noncomputable def runCut (l m g k : Nat) (cuts : List Snap) (s : Snap) : Bool :=
  frc s.2 fun v => st s.1 fun z => st l fun l => st m fun m => st g fun g =>
    bif Nat.ble v.length 1 then true else
      node (fun z r => bif listed cuts z r then false else look l m g k (k-1) 0 z r)
        false l m g k v.length z v pairs

def BoundAt (P : List ℕ) (T l m k : ℕ) (s : Snap) : Prop :=
  ∀ S, StOk P T l k s.1 s.2 S → ∀ k'≤k, ¬ Min m T k' 0 S
lemma cut_sound {P : List ℕ} {T l m g : ℕ} (ctx : Ctx P l m g T) {k : ℕ}
    {s : Snap} {cs : List Snap}
    (rec : ∀ c∈cs,BoundAt P T l m (k-1) c) (check : runCut l m g k cs s=false) :
    BoundAt P T l m k s := by
  intro S hs k' hk hm
  simp only [runCut,frc_eq,st_eq] at check
  cases hlen : Nat.ble s.2.length 1 with
  | true => simp [hlen] at check
  | false =>
    simp only [hlen,Bool.cond_false] at check
    have hc : 2≤S.card := by
      rw [hs.rep.card]
      have h : ¬s.2.length≤1 := by intro h; simp [Nat.ble_eq_true_of_le h] at hlen
      omega
    rcases first_move k' 0 S hm hc with ⟨j,d,a,b,S',rfl,hb,hl⟩ | ⟨_,_,_,_,_,_,_,_,bad,_⟩ | ⟨_,_,_,_,_,_,_,_,_,bad,_⟩
    · obtain ⟨n,rfl⟩ : ∃ n, k=n+1 := ⟨k-1, by omega⟩
      obtain ⟨z,r,hf,st'⟩ := node_bi ctx hs hm (by omega) (by rfl) rfl (by omega) hb hl
        (fun h xs hp a c ha hc hax hcy hxs => by
          subst xs
          have hpw := pairs_false hp
          have : Std.Symm (fun a c : X => h a c=false ∨ h c a=false) := ⟨fun a b h => h.symm⟩
          refine (hpw.imp (S := fun a c => h a c=false ∨ h c a=false) fun h => Or.inl h).forall
            (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_
          intro e
          have : a.s=c.s := congrArg X.s e
          exact hb.1 (by rw [← hax,← hcy,this])) check
      have hm' := hb.min hl hm.2
      change (bif listed cs z r then false else look l m g (n+1) n 0 z r) = false at hf
      cases h : listed cs z r with
      | true => exact rec (z,r) (listed_mem h) S' st' j (by omega) hm'
      | false =>
        simp only [h,Bool.cond_false] at hf
        exact look_sound ctx _ _ _ _ _ _ hf st' j (by omega) hm'
    · omega
    · omega

def shiftW (s : Snap) (i j opn keepI keepJ : ℕ) : Snap :=
  let w0 : W := ⟨0,0,0,0⟩
  let a := s.2.getD i w0
  let b := s.2.getD j w0
  let x := if opn=0 then a.a ||| b.a else a.a &&& b.a
  let y := if opn=0 then a.b &&& b.b else a.b ||| b.b
  let o : W := ⟨if opn=0 then a.s &&& b.s else a.s ||| b.s, x, y, x ||| y⟩
  let r := s.2.filter fun w => (keepI≠0 || w.s≠a.s) && (keepJ≠0 || w.s≠b.s)
  (s.1 + (a.c &&& b.c) - o.c - keepI*a.c - keepJ*b.c,
    r.takeWhile (fun w => o.s < w.s) ++ [o] ++ r.dropWhile (fun w => o.s < w.s))


noncomputable def initialCheck (Z K : ℕ) (answer : ℕ → List W → Bool) : Bool :=
  let l := lz Z
  let m := mz Z
  let g := pL ((pr Z).map fun _ => 16)
  let B := pL ((pr Z).map fun e => 16+(K-e.2))
  frc (avl (PZ Z) m rawL) fun all => anySub all fun v =>
    bif Nat.beq (cov false l v) l then
      bif Nat.ble v.length (K+1) then
        child answer false l g (K+1) v.length (fun f => f v) (Nat.sub B (sumc v)) else false
    else false
theorem initial_sound {Z L : ℕ} (hp : pOk Z=true) (hL : L≤15) (hI : ∀ e∈pr Z,Imp e.1 e.2)
    {answer : ℕ → List W → Bool} (hans : initialCheck Z (L-1) answer=false)
    (hbound : ∀ z v, answer z v=false → Ctx (PZ Z) (lz Z) (mz Z) (pL ((pr Z).map fun _ => 16)) (tz Z) →
      BoundAt (PZ Z) (tz Z) (lz Z) (mz Z) (L-1) (z,v)) : Imp Z L := by
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
  have tz0 : t=0 := by
    have hh := hm.1
    clear * - hh
    induction hh with
    | stop => rfl
    | un bad => exact bad.elim
    | bi _ _ ih => exact ih
  subst t
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
  have hcov : Nat.beq (cov (pos 0) (lz Z) v) (lz Z) = true := by
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
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) 0) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - 0; omega)

  have h2 := hans
  simp only [initialCheck,frc_eq] at h2
  have h3 := anySub_false h2 v hsub
  change Nat.beq (cov false (lz Z) v) (lz Z)=true at hcov
  have hsize : Nat.ble v.length (L-1+1) = true := by simpa using hble
  simp only [hcov,hsize,Bool.cond_true] at h3
  have h4 := child_sound X (f:=answer) (fun _ => rfl) hst hm (by omega) rfl rfl (by simp) h3
  exact hbound _ _ h4 X S hst k (by omega) hm

def rootL : ℕ := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7fff0000000000000000
def rootM : ℕ := 0x7fffdf7dffffbdffffbef7fffefbefbbffff7fffdf7defbdffffbef7bdbfffefbffff7defbdf7bffff7bdbeffffdeffffdf7df77bdbefbbeeeefff5aadaaaab5b6d6daaad6adadfffdb6ab6bfffaadad5b7fff5b5ad5adb6ab6d6b6d6b5fffdad6b55adfffdad5adb5b6ad6db6b55fffd6daab5b6bfffad7fff6d7fff5bfffb5fffdfffc0000000000000001ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7fffffffffffffffffff
def rootG : ℕ := 0x108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootCtxEq : rootL=lz 0 ∧ rootM=mz 0 ∧ rootG=pL ((pr 0).map fun _ => 16) := by decide +kernel
def mergeW (n : ℕ) (a b : W) : W :=
  let x := if n=0 then a.a ||| b.a else a.a &&& b.a
  let y := if n=0 then a.b &&& b.b else a.b ||| b.b
  ⟨if n=0 then a.s &&& b.s else a.s ||| b.s, x, y, x ||| y⟩
def w0 : W := ⟨0x7fffdf7dffffbdffffbef7fffefbefb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000050292aaab5a496d800940929f001240a4be002adad527c005b0000000000000000001e00000000001e000000000000000000001e000000000003c0000780000780003c0001e001e0000000000000000001fe007df7fc00f7fc00fbdff003efbeef0001e000410400078000820000f00020f000104208410f000108483c00043c0004104100008208000038016ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000092683e00754c0101, 0x10000000000084200000000421080000000000000000010000000000084210842108420000000000000000000210000008421084210000000000000000000008421084200000000000000000000000000, 0x0, 0x10000000000084200000000421080000000000000000010000000000084210842108420000000000000000000210000008421084210000000000000000000008421084200000000000000000000000000⟩
def w1 : W := ⟨0x7fffdf7dffffbc000000000000000003ffff7fffdf7defbdffffbef7bd8000000000000000000000000000000000000000000000000000000000005aadaaaaa5b6d498000000018e000000031c0000000063800012852d36ab4962494259e01ad4b55a99e018000000000000000019c0000000000338000670000670003380019c019c000000000000000001f1807df7e300f4030000100c02000008fe011f807df7bef47f00fbdef60e00100e000821000000e0008004038002038002082090000000820006016ab6aaaad6db5b6000000000000000000000000000000000016b56b6daadb5adb5ad7fff6b5ad56b7fff6000000000000000000000000000000000000000000000000000000000000130220c900310c00, 0x400000000000000400004210000000000000000842100000084000000000001080000000000000000200800008400000000842108400000000000008400000010842108421084200000000000, 0x0, 0x400000000000000400004210000000000000000842100000084000000000001080000000000000000200800008400000000842108400000000000008400000010842108421084200000000000⟩
def w2 : W := ⟨0x7fffdf00000001ffffbef00000000003ffff000000000fbc00000000003fffef80000000fbc00000000003effffde00000000007bd8000000000005800280ab500000280d600014911b600029242ad2800524800580009b400000b600015121096a00015120295a00000894d00001522149aa00002a4828549469549402a4801524152400000000000000001f0187c01003006b830fbc080c0000808f860081810403ef0083020804089cc3e01060003ef10800860020f925d8780118100001ef62084200100616000a02ad600000a035800000006d80000000ab6b0000000016000b6d800002d800000006b5ac00000000b56800002b5b6000000005b6a800000000b5fffdb5fffc000000000000004c32000238851dce, 0x1000000000000001000000000008021000000002008021000000840000000000000042000000000010000108000000200000008020080200840000001000200800100021080010840008421, 0x0, 0x1000000000000001000000000008021000000002008021000000840000000000000042000000000010000108000000200000008020080200840000001000200800100021080010840008421⟩
def w3 : W := ⟨0x7fffc07c00000000003e00000003e0000000000000000f81ffff80078000000000000000000000000000000ffffc0ffffc001f003c3e00000e000040202208843010100010002102183080620460842018408c0a000000100100230c0310431810841210431000808010000400101043860888410a08c0c41182141184208c21046904700000000000000001f04301f02086001086f80012182f8200110c02430410be046e86081e1000a1840050c210420420030c2121127c30127c30027c04f0f82008b8810d0080882210c04060004000800000c20180000230806000016c000000c02c058c300c000060421068000060460610c0043002d57fff1862210c2000030000184000100000d7fff7fff605989290008a0c3, 0x100000004000042000000000200000000001004200000000400080010042008021000000002008020004000800100000000000000108001004010802100000004000002000000000200802100001, 0x0, 0x100000004000042000000000200000000001004200000000400080010042008021000000002008020004000800100000000000000108001004010802100000004000002000000000200802100001⟩
def w4 : W := ⟨0x1ffff8000000007fffe000f8000007fffdf7c0001ffffbef03c0000003ffff000001f7bffff03c00000000ffffdf00000003efbbe00e000028c0080009646082000ac0ca6c800a8094da000850b29b64102c42402ab61000d604acd0a401558cacd084009b0822420b4b44ad902400a58215b5052b6a042b6a595b634ada0ada80000000000000000523d1457e47a202c7a28daf1e842be2148f53e3d7df00a54ee7afbc2f0115e8a99ef4508a57de99ef44f028417d1965fd7c5044a56fbeef90b88f40a30022816db18608002b030000002a020000a86b56dfffd0c0b10b01aad8400358100006b02d56300006b10b6c61ab186dad100005b0aad61afffeb5fffc35fffd6fffed00007fff2cb206d6df9ab675, 0x100000000000000000000000000000000000000000000100000080010000000400084000000000000000000000000000000000000000000000000000000000000000000000020, 0x0, 0x100000000000000000000000000000000000000000000100000080010000000400084000000000000000000000000000000000000000000000000000000000000000000000020⟩
def w5 : W := ⟨0x1ffff8000000007fffe000f8000007fffc07c000000003e003c00000000000000001f03ffff03c00000000000000000000000f83e00e000020c00800086060800008c0ca44000080948800085032910410204200288610001004a8402001108ca8408000010822020b0844a880000000821511012a20042a221951014a880a888000000000000000010290417e052000852085ad14800be0008a51e2901f002100252f802f0005482002a4108217c089ea40f00800690800690410442120be0f80b80a40830020016181860000230300000002020000006b40c00010c0810801a218400040100000802c4630000601080c6188186c2110000000a8161afffe04000035fffc60000d00007fff2cb20284c2023205, 0x8000000200000108000000010000100400000200000000001004000000100420080010800000401084000840000001004200040000400000010040100000000000000000400080000040108021, 0x0, 0x8000000200000108000000010000100400000200000000001004000000100420080010800000401084000840000001004200040000400000010040100000000000000000400080000040108021⟩
def w6 : W := ⟨0x1ffff8007fffef80000000000000000000000000000003fffe0000007c0f80003ffff7803e0000000000007c0078000003ee00000000000001000024208c00d806141800b00c282098140185050401000800024080008061400020000461482140405808160120506281012010260c502018a04c18a008c510462906280000000000000000020860820410c16b90c101ad433e100002218048608210420050c1044228bc30002819f03e00848be19e00f8088600088609f081e201042fb90021800000002c0005b08230036000006002c0000083605000001610040060281b020002000000058150b7fff08503016020580d814000040682c0d80000800001b000016fffe17fff00004840d0f006c20810, 0x2000000080000800008000000000002000020084000000100000000200800008400000200840100021080000002100420000010000000400080000042100000000000040008001004200002000400, 0x0, 0x2000000080000800008000000000002000020084000000100000000200800008400000200840100021080000002100420000010000000400080000042100000000000040008001004200002000400⟩
def w7 : W := ⟨0x3ffff7fffdf7de00000000000003fffefbffff7defbdf7bffff7bd8000000000000000000000000000000000a84800000000002aa42a4840de00000001b800000000370005ad5ada6aa6d400000019c00000000019c02d52d35a6ad69b6a541bc00000000003700006e00006e000370001b801b800000000000000001084041041080830080820c020108208cf9019e407df7a0024080001000c9e03ec9f01f7bef7dec9f01ef60206000206000001000804000002021016ab600000000000aab5ab6b7fff000000000000000000000016b56b6daadb580000000000000000000000b56b6d6dab5b6dad57fff000000000000000000000000000000000000000a180bb188920c1a4, 0x20000000000000000000000842100000000010800008400000000000000000004210800000000000000042000021000000840000021084000000008021084010842000000000010842100000, 0x0, 0x20000000000000000000000842100000000010800008400000000000000000004210800000000000000042000021000000840000021084000000008021084010842000000000010842100000⟩
def w8 : W := ⟨0x7fffdf000001ffffbef0000000003ffff000001f78000000000000000ffffdf00000003efb8000000002800000001240002000a000068800a0000d2000000901a60002c02400ab00000d6000c90a40055800c9004009b000240024b000d102400a58001a405034a000348501a6300d200d200000000000000000421410408428202428208060a042042140513e147c000844ee28fbc000110a0899e50400847de104504002041141165d47c4000844fbee110008500a00002800db0000800280000000028000000a80056dfffc000b00b002ac0000358000006b00156000000b0036c002b000dac000005b002d6000000b5fffc0000016fffec00000000000004525d9ab670, 0x40000000000010002100000084000040000000080000000000020000000002100001084010000108400084200002000000080010802000000004200802000000080200000000020004010000000420, 0x0, 0x40000000000010002100000084000040000000080000000000020000000002100001084010000108400084200002000000080010802000000004200802000000080200000000020004010000000420⟩
def w9 : W := ⟨0x3fffefbffff7de00000000000003effffdeffffdf7df70000000000000000000000000000002aa000000019892a1200370000000006c00485080000000092429001b80000000001b02d5ada53400000000003316daab534806e0000d80000d80006c00036003600000000000000000852020820a4040c2404103090084104284805120208210813040410884add03eade81f780020025080040f9b5e079b5e07df7dc0000100400214800000aa800000000aa80000000006daadafffe00000000000016b56000000002db5ad7fff0000000000000b56b6d6d80000000000005b6aad6dafffe00000000000000000000000000940c0523a2600210, 0x800000000000010840000020000000800008400000000040000000000210000000000004200042108421000010040000000084000002100021000210000000420000010000108400000000000008000, 0x0, 0x800000000000010840000020000000800008400000000040000000000210000000000004200042108421000010040000000084000002100021000210000000420000010000108400000000000008000⟩
def b0 : ℕ := 0x12946528c210ad694ad694a4e939ce739ce739ce739d27294a328ca31b5af7b5ad6bdad6b5ad6b5ad6b5af6b5ab5ad6b5a56b4a5294a5295a5295a5294a5294a52939d2749d293a4e739ce939ce939ce73
def w10 := mergeW 1 w5 w0
def b1 : ℕ := 0x119465284210a5254ad6939ca7294e729ce729ca739d25194a328ca30ad2d6ad6b4b5296adad5adad6b56f5ad694a52b59d2929ca53a4e95a4e95a5293a4e939ce7294e549d293a4a7394e939ca9294e52
def w11 := mergeW 0 w9 w10
def b2 : ℕ := 0x118465284210a52329ce939ca3294e728ce728c2739d251942328ca30ace94ad6b3b4e76ad295ad294a4eb3ad692a4ab59d2918c633a4e53a4e53a5251a4e939c63294e529d2919427394e939ca9284e52
def w12 := mergeW 1 w3 w0
def b3 : ℕ := 0x119465184210a4e54ad2739ca7294e529ce729ca729ce3194a328c630a52d5ad294ad275adad5adab6ad6d5ad2949d2b49d2929ca53a4e949ce94a4e929ce729ce7294a549d273a4a7394e7394a7194e51
def b4 : ℕ := 0x119425284210a5253ad6729ca728ca729ca729ca739525194a328ca10ad2d6ad693b5295a56d4adad5ad2f5a5274a52959d29294a529ce75a4e95a4e739ce739ce728ce349d293a4a5394a929ca9294a32
def w13 := mergeW 1 w9 w8
def b5 : ℕ := 0x118c25284210a5252a52729ca528ca7294a729467395251946328ca10ad2b5ad693b5295a52b4ad6b4a4ed4a5273a4e959d2928c6529ce54a4e74a4e529ce739ca528ce339d2929c65394a929ca928ca32
def w14 := mergeW 1 w9 w3
def b6 : ℕ := 0x118c65184210a4e53a4e739ca5294e5294e72946729ce31946328c630a52b4ad294ad275ad6b5ad695a52b4ad2939ceb49d29294653a4e739ce73a4e719ce729ca5294a539d2729c67394e7394a718ce51
def w15 := mergeW 1 w9 w6
def b7 : ℕ := 0x118c632842109d2539d29394a5294e7294e529465394e51946318ca30ad295a56b4ace96ad695a52b4ad2b3a5693a4e949ce7294652a4e74a4a749d272a4a729ca5294e539ce929467294a739ca728ca52
def w16 := mergeW 1 w6 w10
def b8 : ℕ := 0x1194632842109d254a569394a7294e729ce529ca5394e5194a318ca30ad2b6a56b4ace96adab5a56d5b56d4a5694a52949ce729ca52a4e95a4a959d293a4a729ce7294e549ce939ca7294a739ca7294a52
def w17 := mergeW 1 w8 w3
def b9 : ℕ := 0x119425184210a4e53ad2529ca728ca529ca729ca7294e3194a328c610a52d5ad273ad274a56d4adab5a52d5a4e749d2949d29294a529ce749ce94a4a7294e529ce728ca349d273a4a5394a7294a7194a31
def b10 : ℕ := 0x118465284210a52129ce939ca3294e728ce728c2739d251942328ca30aca94ad6b2b4a56ad295ad294a4eb3ad692a4ab59d2908c213a4e53a4e53a5251a4e939c63294e529d2919427394e939ca9284e52
def w18 := mergeW 0 w6 w3
def b11 : ℕ := 0x11946108421094a549ce538ca7294e329ce329ca318ca1194a308c2309d2949ce74a4a54ada959d294a56b39ce94952739ca529ca51a4e939469394a91946519ce72946549ca5394a71946538ca5094650
def w19 := mergeW 1 w9 w0
def b12 : ℕ := 0x118c65284210a5253a52939ca5294e7294e72946739d251946328ca30ad2b5ad6b4b5296ad6b5ad6b5ad2d4ad693a4eb59d29294653a4e74a4e74a5272a4e939ca5294e539d2929c67394e939ca928ce52
def w20 := mergeW 1 w9 w5
def w21 := mergeW 1 w6 w0
def b13 : ℕ := 0x10946328421094e34a5693946518ce729ce529ca5394e5094a318ca30a4e959d293a4a76adab5a56d5b56d4a5673a529494a5194631a4e95a4a959d293a4a7294a518ca349ce939ca7294a739ca7294a52
def b14 : ℕ := 0x1094651842109ca34ad2739c6518ce529ce729ca729ce3094a328c6309ceb4a4e73a4e55adad5adab6ad6d5ad2739d2b494e7194632a4e949ce94a4e929ce7294a518c6349d273a4a7394e7394a7194e51
def w22 := mergeW 1 w8 w10
def w23 := mergeW 0 w3 w10
def b15 : ℕ := 0x119465084210a4a34ace539ca7294e329ce729ca719ca1194a328c2309ced4ace73a4e74adad5ada96a56b5ace94952b39d2919c633a4e9394e93a4a9194e519ce72946549d253a4a7394e538ca5094e50
def w24 := mergeW 1 w3 w10
def w25 := mergeW 1 w8 w6
def b16 : ℕ := 0x1194232842109d253a567294a728ca729ca529ca538ce5194a318ca10ad2b6a5693ace95a56b4a56d4ad2d49d274a52749ce7294a519ce75a4a959ce739ca529ce728ce349ce939ca52946729ca7294632
def w26 := mergeW 1 w6 w5
def b17 : ℕ := 0x129463284210a5674a569394e939ce729ce529ca5394e5294a318ca30b56d7adad5b52b6adab5a56d5b56d4a56b5a5294a5293a4e73a4e95a4a959d293a4a72a52939d2749ce939ca7294a739ca7294a52
def w27 := mergeW 0 w26 w3
def b18 : ℕ := 0x129463084210a4e74a4e538ce939ce329ce529ca519461294a318c230a56d5ad295a4e74adab59d695a56939ceb595292a5293a4e73a4e93946939ca9194631a52939ca749ce539ca7294a338ca3094a50
def b19 : ℕ := 0x128c63284210a56739d29394e739ce7294e529465394e52946318ca30b56b6adad5b52b6ad695a52b4ad2b3a56b4a4e94a52939ca73a4e74a4a749d272a4a72a4e739d2739ce929467294a739ca728ca52
def b20 : ℕ := 0x129423284210a5673a567294e9394a729ca529ca538ce5294a318ca10b56d7adab4b52b5a56b4a56d4ad2d49d295a5274a52939ce729ce75a4a959ce739ca52a5293952549ce939ca52946729ca7294632
def b21 : ℕ := 0x129423184210a5273a525294e9394a529ca529ca528ca3294a318c610ad6d6ad694ad294a56b4a56b4a52b49ce959d273a52939ce729ce749ca949ca7294a31a529394e549ce739ca529465294a5194631
def b22 : ℕ := 0x128c63184210a52739ce7394e739ce5294e529465294a32946318c630ad6b5ad6b5ad295ad695a5294a5293a52b49ce93a52939ca73a4e739ca739ce719ca51a4e739ce739ce729467294a5394a518ca51
def b23 : ℕ := 0x1194631842109ce54a527394a7294e529ce529ca5294a3194a318c630a52b5a5294a4e75adab5a56b5ad6b4a52949d2939ce729ca52a4e949ca949ce929ca519ce7294a549ce739ca7294a5394a5194a51
def b24 : ℕ := 0x128c23284210a56729d27294e7394a7294a52946538ce52946318ca10b56b6adab4b52b5a5294a52b3a4eb39d294a4e74a529394a729ce54a4a749ce529ca52a4e73952539ce9294652946729ca728c632
def b25 : ℕ := 0x129463084210a4e74a4e5384e939ce329ce529ca519461294a318c230a56d5ad295a4a74adab595695a569294eb595292a5293a4e73a4e93942939ca9194230a52939ca749ce539ca7294a338ca3094a50
def w28 := mergeW 0 w9 w0
def b26 : ℕ := 0x10846328421094e3294e93946518ce728ce528c25394e50942318ca30a4e959d293a4a76ad275a4e93a4e92a5673a4a9494a5194631a4e53a4a539d251a4a7294a518ca329ce918c27294a739ca7284a52
def w29 := mergeW 1 w6 w3
def b27 : ℕ := 0x129463184210a5274a527394e939ce529ce529ca5294a3294a318c630ad6d6ad6b5ad295adab5a56b5ad6b4a52b59d293a5293a4e73a4e949ca949ce929ca51a52939ce749ce739ca7294a5394a5194a51
def w30 := mergeW 1 w5 w3
def b28 : ℕ := 0x119461284210952549d6938ca7294e729ce329ca338ca5194a308ca30ad2969d6b4a4a96ada959d2d4b56b39d694a52739ca529ca51a4e95a469595293a46519ce7294e549ca9394a71946539ca5294652
def b29 : ℕ := 0x128c612842109d673952938ce739ce7294e32946338ca52946308ca30b5696a5ad5aceb6ad6759ceb3ad2929d6b4a4e73a4e739ca72a4e74a467495272a4651a4e739d2739ca928c671946539ca528c652
def w31 := mergeW 1 w8 w26
def w32 := mergeW 0 w9 w26
def b30 : ℕ := 0x128463284210a567294e938ce539ce728ce528c25394e52942318ca30b5695adad5b4eb6ad2759ce93a4e939d6b3a4a94a529394673a4e53a46539d251a4671a4a539d2729ce918c27294a739ca7284a52
def w33 := mergeW 1 w9 w26
def w34 := mergeW 1 w8 w0
def b31 : ℕ := 0x12942518c210ad293ad253a4e9394a539ca739ce7294e5294a328c611adaf6b5695b5ab4ad6d5b5ab5a56d6ad295a5694a56b49d2939d2749d294a4a7395253a529394e549d273a4e539ca7294e729ca52
def w35 := mergeW 0 w6 w17
def b32 : ℕ := 0x12942118c2109d2939d23394e9394a539ca339ce328465294a308c611adab6a5675a52b3ad695a52b39d6949ce95a5652a4e749d2919d2749ca94946738ca31a529394e549ca7394e519c23294e329c252
def b33 : ℕ := 0x11942518c210a4e73ad253a4a728ca539ca739ce7294e5194a328c611a56d5ad274ad694ad6d5b5ab5a56d6ad274a56949d29394e729d2749d294a4a73952539ce728ca349d273a4e539ca7294e729ca52
def b34 : ℕ := 0x129425184210ad273ad2529ce9394a529ca729ca7294e3294a328c610ad6f6b5694b5694a56d4adab5a52d5a4e959d294a56b39ce739ce749ce94a4a7294e52a529394e549d273a4a5394a7294a7194a31
def b35 : ℕ := 0x11942318c2109ce73a52539ca728ca539ca539ce528ca5194a318c611a56b5a5274a5294ad6b5ad6b4a56b5a5274a56739ce7394e719d2749ce949ca7394e329ce728ca349ce739ce529c65294e529c652
def b36 : ℕ := 0x128c2318c210a52929ce539ce7394a5394a5394a528ca52946318c611adab5ad695ad6b4ad295ad2939d294a5294a5273a529494e929d2539ce739ca5294e32a4e7394e539ce7294a529c65294e5294652
def w36 := mergeW 1 w9 w17
def b37 : ℕ := 0x128c2518c210ad292a4e53a4e7394a5394a7394a7294e52946328c611adad5b5695b5ab4ad2b5b56949d2b5ad294a5294a56b494e939d2539d273a4a5295253a4e7394e539d2729ca539ca7294e7294a52
def b38 : ℕ := 0x12942118c2109d2939d21394e9394a539ca339ce328465294a308c611adab6a5655a52b2ad695a52b3956949ca95a5652a4e749d2919d2749ca949427384a11a529394e549ca7394e519c23294e329c252
def b39 : ℕ := 0x10842518c2109ca519ca53a465184a538ca738c67294e50942328c6119d2b4a4e53a5274ace95b527394e94ad253a4e9494e728ca519d2329d252a4a319525394a51846129d271946539ca7294e728ca52
def b40 : ℕ := 0x12942318c210a5293a52539ce9394a539ca539ce528ca5294a318c611adad6ad695ad6b4ad6b5ad6b4a56b5a5295a5673a52949d2929d2749ce949ca7394e32a529394e549ce739ce529c65294e529c652
def b41 : ℕ := 0x128c2508c210ace92a4a33a4e7394a3394a7394a7194a32946328c211a5ad4b5275ada93ad2b5b567495295ace949d293a56b494e939d25295272a46518d232a4e7394a539d2529ca539ca528ce5194a51
def b42 : ℕ := 0x11942508c210a4a73ace33a4a728ca339ca739ce7194a3194a328c2119d6d4ace54a5673ad6d5b5a959d6b6ace749d6939d29394e729d27395293a46728d2329ce728c6349d253a4e539ca528ce519ca51
def w37 := mergeW 1 w5 w17
def w38 := mergeW 0 w17 w0
def b43 : ℕ := 0x10942518c2109ca53ad233a465184a539ca739ce7294e5094a328c6119d2b4a4e73a5273ad6d5b5ab59d6d6ace53a569494e728ca519d2749d294a46738d23394a51846149d273a4e539ca7294e729ca52
def w39 := mergeW 1 w17 w0
def b44 : ℕ := 0x128c25184210ad272a4e529ce7394a5294a729467294e32946328c610ad6d5b5694b5694a52b4ad6949ceb4a4e949ce94a56b394a739ce539ce73a4a5194e52a4e7394e539d2729c65394a7294a718ca31
def b45 : ℕ := 0x128c2528c210ad692a5273a4e7394a7394a7394a7395272946328ca11b5ad6b5ab5bdad5ad2b5b56b4a52d5ad694ad295a56b494e939d254a5274a4e539d274a4e73952539d2929ca539ca929ce9394a53
def w40 := mergeW 0 w13 w0
def b46 : ℕ := 0x108c2528c2109ce51a5273a463184a7394a7394a7395270946328ca11a5294a5273ad295aceb5b56b39ced5ad652ad29594e728c6519d234a5274a4e339d2749463184a139d2929ca539ca929ce9394a53
def b47 : ℕ := 0x128c2328c210a56929d2739ce7394a7394a5394a538ce72946318ca11b5ab6adab5b56d5ad295ad2b3a52b4a5694ad274a529494e929d254a4e749ce539ce53a4e73952539ce9294a529c6729ce7394653
def b48 : ℕ := 0x128c25284210ad672a52729ce7394a7294a729467395252946328ca10b56d6b5ab4bd6b5a52b4ad6b4a4ed4a5294a4e95a56b394a739ce54a4e74a4e529ce73a4e73952539d2929c65394a929ca928ca32
def b49 : ℕ := 0x118c2328c2109d2729d2739ca528ca7394a5394a538ce71946318ca11ad695a5694ad2b5ad295ad2b3a52b4a5673ad2749ce738ca719d254a4e749ce539ce539ca528ce339ce9294a529c6729ce7394653
def b50 : ℕ := 0x118c2518c210a4e72a4e53a4a528ca5394a7394a7294e51946328c611a56b4ad274ad694ad2b5b56949d2b5ad273a52949d2938ca729d2539d273a4a52952539ca528ca339d2729ca539ca7294e7294a52
def b51 : ℕ := 0x108c2528c2109ce50a5273a463184a7394a7394a7395270946328ca11a5294a5273ad295acab5b56b294ad5ad652ad29594e72846519d214a5274a4e139d2749463184a139d2929ca539ca929ce9394a53
def b52 : ℕ := 0x128c2108c2109ce9294a3394e7394a3394a3394a3184a32946308c211a5a94a5275ad293ad275a4e72952939ce949d253a4e7494e919d25294a72946518ca32a4e7394a539ca528ca519c2528ce5194251
def b53 : ℕ := 0x118c2528c210a5272a5273a4a528ca7394a7394a7395271946328ca11ad6b5ad694b56b5ad2b5b56b4a52d5ad673ad2959d2938ca729d254a5274a4e539d2749ca528ce339d2929ca539ca929ce9394a53
def b54 : ℕ := 0x12842518c210ad2919ca53a4e5394a538ca738c67294e52942328c611adab4b5695b5ab4ace95b527394e94ad293a4e94a56b48ca939d2329d252a4a3195253a4a5394e529d271946539ca7294e728ca52
def b55 : ℕ := 0x12842328c210a569194e739ce5394a738ca538c6538ce72942318ca11b5a95adab5b56d5ace75ace929ce93a5693ace74a52948ca929d233a4e539ce329ce53a4a53952529ce918c6529c6729ce738c653
def w41 := mergeW 1 w13 w5
def w42 := mergeW 0 w13 w6
def b56 : ℕ := 0x128c2128c2109d6919527394e7394a7394a3394a3384a72946308ca11b5a96a5ab5ad2d5ace75a4eb39ce939d694ad253a4e748ce919d234a4a7494e339ca32a4e73952539ca928ca519c2529ce5394253
def w43 := mergeW 1 w13 w6
def b57 : ℕ := 0x11946518c210a4e74ad274a4a7294e539ce739ce729ce5194a328c631a56d5ad295ad695b5ad6b5ab6adad6b5694a56b49d2939ce73a52949d294a4e939d2739ce7294a549d273a4e739ce7394e729ce72
def b58 : ℕ := 0x11946318c2109ce74a52749ca7294e539ce539ce5294a5194a318c631a56b5a5295a5295b5ab6ad6b5adab5ad694a56939ce739ce72a52949ce949ce939ce529ce7294a549ce739ce729ca5394e529ca72
def b59 : ℕ := 0x118c6518c210a4e73a4e74a4a5294e5394e7394a729ce51946328c631a56b4ad295ad695b56b6b5695a56b5b5693a52b49d29394a73a52739d273a4e729d2739ca5294a539d2729ca739ce7394e7294e72
def b60 : ℕ := 0x118c6318c2109ce739ce749ca5294e5394e5394a5294a51946318c631a5694a5295a5295b5696ad294a5694ad693a52939ce7394a72a52739ce739ce729ce529ca5294a539ce7294a729ca5394e5294a72
def b61 : ℕ := 0x10946318c21094a54a52749c6518ce539ce539ce5294a5094a318c6319d2949ce749ce75b5ab6ad6b5adab5ad673a569394a5294a51a52949ce949ce939ce5294a518c6349ce739ce729ca5394e529ca72
def b62 : ℕ := 0x118c6508c210a4a73a4a54a4a5294e3394e7394a719ca31946328c2319d6b3ace75a5674b56b6b56759d695b52939d2b39d29394a73a527295272a4a71952529ca52946539d2529ca739ce538ce5194e71
def w44 := mergeW 0 w9 w6
def b63 : ℕ := 0x11846118c21094e729ca7494a3294e538ce338c6328c651942308c631a56939d2959ce95b5296a52749d294a5692a4e729ca538c671a52529ca5294e519ca319c63294a529ca71946719c63394e328c672
def w45 := mergeW 1 w6 w12
def w46 := mergeW 1 w9 w12
def b64 : ℕ := 0x128c6328c210a56939d2949ce739ce7394e5394a5394e72946318ca31b5ab6adad6b56d6b5696ad2b4ad6b4adab4ad294a52949ce93a5274a4e749d273a4e73a4e739d2739ce9294a729ca739ce7394a73
def b65 : ℕ := 0x118c6328c2109d2739d2949ca5294e7394e5394a5394e71946318ca31ad695a56b5ad2b6b5696ad2b4ad6b4ada93ad2949ce7394a72a5274a4e749d273a4e739ca5294e539ce9294a729ca739ce7394a73
def b66 : ℕ := 0x128c6318c210a52939ce749ce739ce5394e5394a5294a52946318c631adab5ad6b6ad6b5b5696ad294a5694ad6b4a5293a52949ce93a52739ce739ce729ce52a4e739ce739ce7294a729ca5394e5294a72
def b67 : ℕ := 0x118c6128c210952739529494a5294e7394e3394a338ca71946308ca31ad6759d6b5a4eb6b5676a4eb3ad693a5a93ad2739ca5394a71a5274a4a7495273a4a529ca5294e539ca928ca719c6539ce5394673
def b68 : ℕ := 0x12846318c210a529294a749ce539ce538ce538c65294a52942318c631ada94ad6b6ad6b5b5276ace739d273ad6b3a4e93a529494a93a52529ce529ce519ce52a4a539ce729ce718c6729ca5394e528ca72
def w47 := mergeW 0 w3 w0
def b69 : ℕ := 0x108c6308c21094e539ca549c6318ce3394e5394a5194630946318c231a52749d294a4e94b5696ad2749d674ad2729d29294a528c651a527294e729ca7194e31946318ca339ce5294a729ca338ce3194a71
def w48 := mergeW 1 w15 w0
def w49 := mergeW 1 w15 w3
def b70 : ℕ := 0x11946328c2109d274a56949ca7294e739ce539ce5394e7194a318ca31ad6b6a56b5ad2b6b5ab6ad6d5b5ad5ada94ad6949ce739ce72a5295a4e959d294a4e739ce7294e549ce939ce729ca739ce739ca73
def w50 := mergeW 0 w3 w21
def b71 : ℕ := 0x11946308c21094a74a4e549ca7294e339ce539ce519463194a318c2319d6949ce75a4e74b5ab6ad695a5a95ad2949d6929ca539ce71a529394e939ca9294e319ce72946549ce539ce729ca338ce319ca71
def w51 := mergeW 0 w9 w21
def b72 : ℕ := 0x11846328c2109527294e949ca3294e738ce538c65394e71942318ca31ad6949d6b5a4eb6b5276ace93a5293ada92ace949ca538c671a5253a4e539d252a4e739c63294e529ce918c6729ca739ce738ca73
def b73 : ℕ := 0x11942328c2109d273a56739ca728ca739ca539ce538ce7194a318ca11ad6b6a5694ad2b5ad6b5ad6d4ad6d5a5674ad6749ce7394e719d275a4e959ce749ce539ce728ce349ce939ce529c6729ce739c653
def b74 : ℕ := 0x128c6518c210ad293a4e74a4e739ce5394e7394a729ce52946328c631adad5b56b6b5ab5b56b6b5695a56b5b56b4a52b4a56b49ce94a52739d273a4e729d273a4e739ce739d2729ca739ce7394e7294e72
def w52 := mergeW 0 w14 w0
def b75 : ℕ := 0x108c6518c2109ca53a4a74a46318ce5394e7394a729ce50946328c6319d294a4e74a5275b56b6b56759d695b5672a52b494e728c652a52729d272a4e719d273946318c6339d2729ca739ce7394e7294e72
def w53 := mergeW 0 w6 w14
def b76 : ℕ := 0x128c6118c2109d29394a7494e739ce5394e3394a328c652946308c631ada94a56b6a52b5b5676a4e739d693a56b4a5272a4e749ce92a52729ca7294e719ca31a4e739ce739ca728ca719c63394e3294672
def b77 : ℕ := 0x128c65184210ad273a4e739ce739ce5294e72946729ce32946328c630ad6d5b56b5b5695ad6b5ad695a52b4ad2b49ceb4a56b39ca74a4e739ce73a4e719ce72a4e739ce739d2729c67394e7394a718ce51
def b78 : ℕ := 0x129425284210ad673ad6729ce9394a729ca729ca739525294a328ca10b56f7b5ab4bd6b5a56d4adad5ad2f5a5295a5295a56b39ce739ce75a4e95a4e739ce73a5293952549d293a4a5394a929ca9294a32
def b79 : ℕ := 0x1294210842109ce739ce328ce9394a329ca329ca3184a1294a308c210a56b5a5274ace73a56949d2939d2b394a9595253a4e739ce719ce7394693946718c631a529394a549ca5394a51942528ca5094230
def b80 : ℕ := 0x1084252842109ce319ce729c65184a728ca728c27395250942328ca10a4eb5a5272ace75a4e94ad2939cab3a5253a4a9594e718c6319ce33a4e53a4e319ce7394a5184a129d2919425394a929ca9284a32
def b81 : ℕ := 0x12946108c2109ce949ce5494e939ce339ce339ce318ca3294a308c231a5ab5a5296ad294b5a96a5294a5ab4a52b59d673a4e74a5292a529394a9394a9294a52a52939ca749ca5394e719c6538ce519c671
def b82 : ℕ := 0x10846108c2108c6528c654946518ce338ce338c6318ca30942308c2319527394a549ca54b5256a4a5295272a52739ce739463294a50a525194a5194a5094a5294a518c2329ca51846719c6538ce518c671
def w54 := mergeW 1 w18 w0
def b83 : ℕ := 0x11946108c21094a749ce5494a7294e339ce339ce318ca3194a308c2319d6949ce75a4e74b5a96a5294a5ab4a52949d6739ca539ce71a529394a9394a9294a529ce72946549ca5394e719c6538ce519c671
def w55 := mergeW 1 w18 w9
def b84 : ℕ := 0x128c6108c2109ce9394a5494e739ce3394e3394a318ca32946308c231a5a94a5296ad294b5676a4e739d693a52b49d273a4e749ce92a527294a7294a7194a52a4e739ca739ca528ca719c6538ce5194671
def b85 : ℕ := 0x118c6108c21094a7394a5494a5294e3394e3394a318ca31946308c2319d6739ce75a4e74b5676a4e739d693a52939d2739ca5394a71a527294a7294a7194a529ca52946539ca528ca719c6538ce5194671
def b86 : ℕ := 0x11942108c21094a739ce3394a728ca339ca339ce3184a3194a308c2119d6949ce54a4e73ad695a52939d6b49ce749d6539ca5394e709d27394a93946728ca329ce728c6349ca5394e519c2528ce519c251
def b87 : ℕ := 0x10846528c2109ce529ce94a46518ce738ce738c6739d270942328ca31a52b5a5294ad296b5296b5294a52b4b5a73aceb594e7294a52a5253a5253a5252a529494a518ca329d291946739ce939ce938ce73
def w56 := mergeW 1 w28 w3
def b88 : ℕ := 0x10846518c2109ca529ca74a46518ce538ce738c6729ce50942328c6319d2b4a4e74a5275b5296b52749d294b5673a4eb494e7294a52a52529d252a4e519d27394a518c6329d271946739ce7394e728ce72
def w57 := mergeW 1 w28 w6
def b89 : ℕ := 0x10846328c21094e5294e949c6518ce738ce538c65394e70942318ca31a52959d294a4e96b5276ace93a5293ada73ace9494a5294a51a5253a4e539d252a4e7394a518ca329ce918c6729ca739ce738ca73
def b90 : ℕ := 0x10846318c21094a5294a749c6518ce538ce538c65294a50942318c6319d2949ce749ce75b5276ace739d273ad673a4e9394a5294a51a52529ce529ce519ce5294a518c6329ce718c6729ca5394e528ca72
def b91 : ℕ := 0x1084651842109ca329ca739c6518ce528ce728c2729ce30942328c6309ceb4a4e73a4e55ad295ad2749ce93ad2739cab494e7194632a4e529ce52a4e509ce7294a518c6329d2719427394e7394a7184e51
def b92 : ℕ := 0x12946318c210a5294a52749ce939ce539ce539ce5294a5294a318c631adad6ad6b6ad6b5b5ab6ad6b5adab5ad6b5a5693a5294a5293a52949ce949ce939ce52a52939ce749ce739ce729ca5394e529ca72
def b93 : ℕ := 0x11946118c21094e749d27494a7294e539ce339ce328c65194a308c631a56959d2959ce95b5a96a52b4ada94a5694a56729ca539ce71a52949ca9494e939ca319ce7294a549ca7394e719c63394e329c672
def b94 : ℕ := 0x128c6308c210a4e939ca549ce739ce3394e5394a5194632946318c231a5ab4ad296a5694b5696ad2749d674ad2b49d292a52949ce93a527294e729ca7194e31a4e739ca739ce5294a729ca338ce3194a71
def b95 : ℕ := 0x11946308c2109ca74a4e549ca7294e339ce539ce519463194a318c2319d6b4a4e759d274b5ab6ad695a5a95ad2949d6929ce739ce72a529394e939ca9294e319ce72946549ce539ce729ca338ce319ca71
def b96 : ℕ := 0x118c6528c210a5273a5294a4a5294e7394e7394a739d271946328ca31ad6b5ad6b5b56b6b56b6b56b5ad6d5b5a93ad2b59d29394a73a5274a5274a5273a52949ca5294e539d2929ca739ce939ce9394e73
def b97 : ℕ := 0x108c6328c21094e539d2949c6318ce7394e5394a5394e70946318ca31a52749d294a4e96b5696ad2b4ad6b4ada72ad29494a528c651a5274a4e749d273a4e73946318ca339ce9294a729ca739ce7394a73
def b98 : ℕ := 0x11846518c210a4e729ca74a4a3294e538ce738c6729ce51942328c631a5693ad295ad695b5296b52749d294b5692a4eb49d2938c673a52529d252a4e519d2739c63294a529d271946739ce7394e728ce72
def b99 : ℕ := 0x108c6518c2109ca53a4e74a46318ce5394e7394a729ce50946328c6319d293a4e74a5275b56b6b5695a56b5b5672a52b494e728c652a52739d273a4e729d273946318c6339d2729ca739ce7394e7294e72
def b100 : ℕ := 0x129465184210ad274ad2739ce939ce529ce729ca729ce3294a328c630ad6f6b56b5b5695adad5adab6ad6d5ad2b59d2b4a56b3a4e74a4e949ce94a4e929ce72a52939ce749d273a4a7394e7394a7194e51
def b101 : ℕ := 0x11942528c210a5273ad673a4a728ca739ca739ce739527194a328ca11ad6d6ad694b56b5ad6d5b5ad5ad6f6ad674ad6959d29394e729d275a5295a4e749d2749ce728ce349d293a4e539ca929ce939ca53
def b102 : ℕ := 0x12942328c210a5693a56739ce9394a739ca539ce538ce7294a318ca11b5ad7adab5b56d5ad6b5ad6d4ad6d5a5695ad674a52949d2929d275a4e959ce749ce53a5293952549ce939ce529c6729ce739c653
def b103 : ℕ := 0x10842328c21094e5194e739c65184a738ca538c6538ce70942318ca11a52959d273a4e95ace75ace929ce93a5653ace7494a528ca509d233a4e539ce329ce5394a5184a129ce918c6529c6729ce738c653
def b104 : ℕ := 0x128c65284210ad673a52939ce739ce7294e72946739d252946328ca30b56d6b5ad5bd6b6ad6b5ad6b5ad2d4ad6b4a4eb5a56b39ca74a4e74a4e74a5272a4e93a4e739d2739d2929c67394e939ca928ce52
def b105 : ℕ := 0x128c610842109ce7394a538ce739ce3294e32946318ca12946308c230a5694a5295ace74ad6759ce739d2929ceb494e73a4e739ca72a4e729467294a7094651a4e739ca739ca528c671946538ca508c650
def b106 : ℕ := 0x10946508c2109ce54ace54a46518ce339ce739ce719ca3094a328c231a52b5a5294ad294b5ad6b5a96a5ab6b52739d6b394e7294a52a529395293a4a929525294a518ca349d253a4e739ce538ce519ce71
def w58 := mergeW 1 w47 w1
def b107 : ℕ := 0x12846128c2109d6929ce9494e539ce738ce338c6338ca72942308ca31b5ab5a5ad6ad2d6b5296a5294a52b4a5ab3ace73a4e7494a92a5253a4a5395252a4a52a4a539d2729ca91946719c6539ce538c673
def w59 := mergeW 1 w44 w7
def w60 := mergeW 0 w6 w0
def b108 : ℕ := 0x10946128c2109ce549d694946518ce739ce339ce338ca7094a308ca31a52b5a5294ad296b5a96a52d4b5ab4a5a73ad67394e7294a52a5295a4a9595294a4a5294a518ca349ca9394e719c6539ce539c673
def b109 : ℕ := 0x12946528c210ad694ad693a4e939ce739ce739ce739d27294a328ca31b5af7b5ad5bdad6adad5b5ad6b56f6ad6b5ad6b5a56b4a5294a5295a5295a5294a5294a52939d2749d293a4e739ce939ce939ce53
def b110 : ℕ := 0x11946528c210a5274ad693a4a7294e739ce739ce739d27194a328ca31ad6d6ad6b4b56b6adad5b5ad6b56f6ad694ad6b59d2939ce73a5295a5295a5294a52949ce7294e549d293a4e739ce939ce939ce53
def b111 : ℕ := 0x11946518c210a4e74ad273a4a7294e539ce739ce729ce5194a328c631a56d5ad294ad695adad5b5ab6ad6d6ad294a56b49d2939ce73a52949d294a4e939d2739ce7294a549d273a4e739ce7394e729ce52
def b112 : ℕ := 0x118c6528c210a5273a5293a4a5294e7394e7394a739d271946328ca31ad6b5ad6b4b56b6ad6b5b56b5ad2d5ad693ad2b59d29394a73a5274a5274a5273a52949ca5294e539d2929ca739ce939ce9394e53
def b113 : ℕ := 0x11846528c210a52329ce93a4a3294e738ce738c6739d271942328ca31ace94ad6b2b4e76ad295b5294a4eb4ad692aceb59d2918c633a5253a5253a5252a52949c63294e529d291946739ce939ce938ce53
def b114 : ℕ := 0x118c6518c210a4e73a4e73a4a5294e5394e7394a729ce51946328c631a56b4ad294ad695ad6b5b5695a52b5ad293a52b49d29394a73a52739d273a4e729d2739ca5294a539d2729ca739ce7394e7294e52
def b115 : ℕ := 0x11946328c2109d274a56939ca7294e739ce539ce5394e7194a318ca31ad6b6a56b4ad2b6adab5ad6d5b56d5a5694ad6949ce739ce72a5295a4e959d294a4e739ce7294e549ce939ce729ca739ce739ca53
def b116 : ℕ := 0x11946108c21094a749ce5394a7294e339ce339ce318ca3194a308c2319d6949ce74a4e74ada95a5294a56b49ce949d6739ca539ce71a529394a9394a9294a529ce72946549ca5394e719c6538ce519c651
def w61 := mergeW 0 w4 w10
def b117 : ℕ := 0x11946528c210a5234ad692a4a7294e739ce739ce739d27194a328ca31aced6ad6b3b4e76a5ad4b5ad6b52f6a5294ad6b59d2919c633a5295a5295a5294a52949ce7294e549d293a4e739ce939ce939ce33
def b118 : ℕ := 0x118c6328c2109d2739d2939ca5294e7394e5394a5394e71946318ca31ad695a56b4ad2b6ad695ad2b4ad2b4a5693ad2949ce7394a72a5274a4e749d273a4e739ca5294e539ce9294a729ca739ce7394a53
def b119 : ℕ := 0x11946528c210a5254ad692a4a7294e739ce739ce739d27194a328ca31ad2d6ad6b4b5296a5ad4b5ad6b52f6a5294ad6b59d2929ca53a5295a5295a5294a52949ce7294e549d293a4e739ce939ce939ce33
def b120 : ℕ := 0x10946328c21094e54a56939c6518ce739ce539ce5394e7094a318ca31a52959d293a4e96adab5ad6d5b56d5a5673ad69494a5294a51a5295a4e959d294a4e7394a518ca349ce939ce729ca739ce739ca53
def b121 : ℕ := 0x11946328c2109d254a56939ca7294e739ce539ce5394e7194a318ca31ad2b6a56b3ace96adab5ad6d5b56d5a5694ad6949ce729ca52a5295a4e959d294a4e739ce7294e549ce939ce729ca739ce739ca53
def b122 : ℕ := 0x11946508c210a4a34ace53a4a7294e339ce739ce719ca3194a328c2319ced4ace72a4e74adad5b5a96a56b6ace949d6b39d2919c633a529395293a4a92952529ce72946549d253a4e739ce538ce519ce51
def b123 : ℕ := 0x118c2528c210a5272a5272a4a528ca7394a7394a7395271946328ca11ad6b5ad693b56b5a52b4b56b4a4ed5a5273ad2959d2938ca729d254a5274a4e539d2749ca528ce339d2929ca539ca929ce9394a33
def b124 : ℕ := 0x11846128c210952729ce9394a3294e738ce338c6338ca71942308ca31ad6949d6b4a4eb6ad295a5294a4eb49d692ace739ca538c671a5253a4a5395252a4a529c63294e529ca91946719c6539ce538c653
def b125 : ℕ := 0x11942518c210a4e73ad252a4a728ca539ca739ce7294e5194a328c611a56d5ad273ad694a56d4b5ab5a52d6a4e74a56949d29394e729d2749d294a4a73952539ce728ca349d273a4e539ca7294e729ca32
def b126 : ℕ := 0x10946518c2109ca54ad273a46518ce539ce739ce729ce5094a328c6319d2b4a4e73a5275adad5b5ab6ad6d6ad273a56b494e7294a52a52949d294a4e939d27394a518c6349d273a4e739ce7394e729ce52
def b127 : ℕ := 0x11946528c210a5254ad691a4a7294e739ce739ce739d27194a328ca31ad2d6ad6b3b52969dad3b5ad6b4ef69ce94ad6b59d2929ca53a5295a5295a5294a52949ce7294e549d293a4e739ce939ce939ce13
def b128 : ℕ := 0x118c6528c210a5273a5292a4a5294e7394e7394a739d271946328ca31ad6b5ad6b3b56b6a56b4b56b5aced5a5293ad2b59d29394a73a5274a5274a5273a52949ca5294e539d2929ca739ce939ce9394e33
def b129 : ℕ := 0x11946328c2109d274a56929ca7294e739ce539ce5394e7194a318ca31ad6b6a56b3ad2b6a5ab4ad6d5b52d59d294ad6949ce739ce72a5295a4e959d294a4e739ce7294e549ce939ce729ca739ce739ca33
def b130 : ℕ := 0x108c6528c2109ce53a5293a46318ce7394e7394a739d270946328ca31a5294a5293ad296ad6b5b56b5ad2d5ad672ad2b594e728c652a5274a5274a5273a5294946318ca339d2929ca739ce939ce9394e53
def b131 : ℕ := 0x11946318c2109ce74a52739ca7294e539ce539ce5294a5194a318c631a56b5a5294a5295adab5ad6b5ad6b5a5294a56939ce739ce72a52949ce949ce939ce529ce7294a549ce739ce729ca5394e529ca52
def b132 : ℕ := 0x11946518c210a4e74ad272a4a7294e539ce739ce729ce5194a328c631a56d5ad293ad695a5ad4b5ab6ad2d6a4e94a56b49d2939ce73a52949d294a4e939d2739ce7294a549d273a4e739ce7394e729ce32
def b133 : ℕ := 0x11946528c210a5234ad691a4a7294e739ce739ce739d27194a328ca31aced6ad6b2b4e769dad3b5ad6b4ef69ce94ad6b59d2919c633a5295a5295a5294a52949ce7294e549d293a4e739ce939ce939ce13
def b134 : ℕ := 0x12946328c210a5694a56939ce939ce739ce539ce5394e7294a318ca31b5ad7adad5b56d6adab5ad6d5b56d5a56b5ad694a5294a5293a5295a4e959d294a4e73a52939d2749ce939ce729ca739ce739ca53
def b135 : ℕ := 0x128c6328c210a56939d2939ce739ce7394e5394a5394e72946318ca31b5ab6adad5b56d6ad695ad2b4ad2b4a56b4ad294a52949ce93a5274a4e749d273a4e73a4e739d2739ce9294a729ca739ce7394a53
def b136 : ℕ := 0x12946318c210a5294a52739ce939ce539ce539ce5294a5294a318c631adad6ad6b5ad6b5adab5ad6b5ad6b5a52b5a5693a5294a5293a52949ce949ce939ce52a52939ce749ce739ce729ca5394e529ca52
def b137 : ℕ := 0x12946308c210a4e94a4e538ce939ce339ce539ce519463294a318c231a5ad5ad295a4e94adab59d695a569394eb59d692a5294a5293a5293946939ca9294631a52939ca749ce539ce729ca338ce319ca51
def b138 : ℕ := 0x128c6318c210a52939ce739ce739ce5394e5394a5294a52946318c631adab5ad6b5ad6b5ad695ad294a5294a52b4a5293a52949ce93a52739ce739ce729ce52a4e739ce739ce7294a729ca5394e5294a52
def b139 : ℕ := 0x10846328c21094e5294e939c6518ce738ce538c65394e70942318ca31a52959d293a4e96ad275ace93a4e93a5673ace9494a5294a51a5253a4e539d252a4e7394a518ca329ce918c6729ca739ce738ca53
def w62 := mergeW 0 w4 w26
def b140 : ℕ := 0x12946328c210a5694a56928ce939ce739ce539ce5394e7294a318ca31b5ad7adad4b4ed6a5ab49d6d5b52d39d2b5ad694a5294a5293a5295a46959d294a4671a52939d2749ce939ce729ca739ce739ca33
def b141 : ℕ := 0x12946328c210a5694a569294e939ce739ce539ce5394e7294a318ca31b5ad7adad4b52d6a5ab4a56d5b52d4a52b5ad694a5294a5293a5295a4a959d294a4a72a52939d2749ce939ce729ca739ce739ca33
def b142 : ℕ := 0x11946128c210952749d69394a7294e739ce339ce338ca7194a308ca31ad6969d6b4a4eb6ada95a52d4b56b49d694ad6739ca539ce71a5295a4a9595294a4a529ce7294e549ca9394e719c6539ce539c653
def b143 : ℕ := 0x11946328c2109d274a569394a7294e739ce539ce5394e7194a318ca31ad6b6a56b4aceb6adab5a56d5b56d49d694ad6949ce739ce72a5295a4a959d294a4a729ce7294e549ce939ce729ca739ce739ca53
def b144 : ℕ := 0x12846328c210a569294e938ce539ce738ce538c65394e72942318ca31b5a95adad5b4ed6ad2759ce93a4e93956b3ace94a529494a93a5253a46539d252a4671a4a539d2729ce918c6729ca739ce738ca53
def b145 : ℕ := 0x12942318c210a5293a52529ce9394a539ca539ce528ca5294a318c611adad6ad694ad6b4a56b4ad6b4a52b59ce95a5673a52949d2929d2749ce949ca7394e32a529394e549ce739ce529c65294e529c632
def b146 : ℕ := 0x10946308c21094e54a4e539c6518ce339ce539ce519463094a318c231a52959d293a4e94adab5ad695a5695a4e739d69294a5294a51a529394e939ca9294e3194a518ca349ce539ce729ca338ce319ca51
def b147 : ℕ := 0x128c2328c210a56929d2729ce7394a7394a5394a538ce72946318ca11b5ab6adab4b56d5a5294ad2b3a4eb49d294ad274a529494e929d254a4e749ce539ce53a4e73952539ce9294a529c6729ce7394633
def b148 : ℕ := 0x128c6128c2109d6939529394e739ce7394e3394a338ca72946308ca31b5a96a5ad5ad2d6ad675a4eb3ad2939d6b4ad273a4e749ce92a5274a4a7495273a4a52a4e739d2739ca928ca719c6539ce5394653
def b149 : ℕ := 0x12946328c210a5694a569194e939ce739ce539ce5394e7294a318ca31b5ad7adad3b52d69dab3a56d5b4ed49ceb5ad694a5294a5293a5295a4a959d294a4a72a52939d2749ce939ce729ca739ce739ca13
def b150 : ℕ := 0x12946318c210a5294a52729ce939ce539ce539ce5294a5294a318c631adad6ad6b4ad6b5a5ab4ad6b5ad2b59ceb5a5693a5294a5293a52949ce949ce939ce52a52939ce749ce739ce729ca5394e529ca32
def b151 : ℕ := 0x12946118c2109d2949d27394e939ce539ce339ce328c65294a308c631adab6a56b5a52b5ada95a52b4ad6949d2b5a5672a4e74a5292a52949ca9494e939ca31a52939ce749ca7394e719c63394e329c652
def b152 : ℕ := 0x128c6328c210a56939d2929ce739ce7394e5394a5394e72946318ca31b5ab6adad4b56d6a5694ad2b4aceb49d2b4ad294a52949ce93a5274a4e749d273a4e73a4e739d2739ce9294a729ca739ce7394a33
def b153 : ℕ := 0x12946328c210a5694a56918ce939ce739ce539ce5394e7294a318ca31b5ad7adad3b4ed69dab39d6d5b4ed394eb5ad694a5294a5293a5295a46959d294a4671a52939d2749ce939ce729ca739ce739ca13
def b154 : ℕ := 0x12946518c210ad294ad273a4e939ce539ce739ce729ce5294a328c631adaf6b56b5b5ab5adad5b5ab6ad6d6ad2b5a56b4a56b4a5294a52949d294a4e939d273a52939ce749d273a4e739ce7394e729ce52
def b155 : ℕ := 0x12946118c2109d2949d23394e939ce539ce339ce328c65294a308c631adab6a5675a52b3ada95a52b49d6949cab5a5672a4e74a5292a52949ca94946938ca31a52939ce749ca7394e719c63394e329c652
def b156 : ℕ := 0x128c6518c210ad293a4e73a4e739ce5394e7394a729ce52946328c631adad5b56b5b5ab5ad6b5b5695a52b5ad2b4a52b4a56b49ce94a52739d273a4e729d273a4e739ce739d2729ca739ce7394e7294e52
def b157 : ℕ := 0x10846518c2109ca529ca73a46518ce538ce738c6729ce50942328c6319d2b4a4e73a5275ad295b52749ce94ad273a4eb494e7294a52a52529d252a4e519d27394a518c6329d271946739ce7394e728ce52
def w63 := mergeW 0 w4 w17
def b158 : ℕ := 0x12946518c210ad294ad232a4e939ce539ce739ce729ce5294a328c631adaf6b5674b5ab3a5ad4b5ab69d2d6a4eb5a56b4a56b4a5294a52949d294a46938d233a52939ce749d273a4e739ce7394e729ce32
def b159 : ℕ := 0x12946518c210ad294ad252a4e939ce539ce739ce729ce5294a328c631adaf6b5694b5ab4a5ad4b5ab6a52d6a52b5a56b4a56b4a5294a52949d294a4a9395253a52939ce749d273a4e739ce7394e729ce32
def b160 : ℕ := 0x128c6508c210ace93a4a53a4e739ce3394e7394a719ca32946328c231a5ad4b5295ada94ad6b5b56759d295aceb49d2b3a56b49ce94a527295272a4a7195252a4e739ca739d2529ca739ce538ce5194e51
def b161 : ℕ := 0x128c6518c210ad293a4e53a4e739ce5394e7394a729ce52946328c631adad5b5695b5ab4ad6b5b56959d2b5aceb4a52b4a56b49ce94a52739d273a4a7295253a4e739ce739d2729ca739ce7394e7294e52
def b162 : ℕ := 0x10946518c2109ca54ad233a46518ce539ce739ce729ce5094a328c6319d2b4a4e73a5273adad5b5ab69d6d6aca73a56b494e7294a52a52949d294a46938d23394a518c6349d273a4e739ce7394e729ce52
def b163 : ℕ := 0x129463184210a5274a527294e939ce529ce529ca5294a3294a318c630ad6d6ad6b4ad295a5ab4a56b5ad2b49ceb59d293a5293a4e73a4e949ca949ce929ca51a52939ce749ce739ca7294a5394a5194a31
def b164 : ℕ := 0x12846118c2109d2929ca7394e539ce538ce338c6328c652942308c631adab4a56b5a52b5ad295a52749ce949d2b3a4e72a4e7494a92a52529ca5294e519ca31a4a539ce729ca71946719c63394e328c652
def b165 : ℕ := 0x119465184210a4e54ad2729ca7294e529ce729ca729ce3194a328c630a52d5ad293ad275a5ad4adab6ad2d5a4e949d2b49d2929ca53a4e949ce94a4e929ce729ce7294a549d273a4a7394e7394a7194e31
def b166 : ℕ := 0x11946508c210a4a74ace53a4a7294e339ce739ce719ca3194a328c2319d6d4ace74a5674adad5b5a96a56b6ace949d6b39d2939ce73a529395293a4a92952529ce72946549d253a4e739ce538ce519ce51
def b167 : ℕ := 0x12946518c210ad294ad251a4e939ce539ce739ce729ce5294a328c631adaf6b5693b5ab49dad3b5ab6a4ed69ceb5a56b4a56b4a5294a52949d294a4a9395253a52939ce749d273a4e739ce7394e729ce12
def b168 : ℕ := 0x128c6518c210ad293a4e72a4e739ce5394e7394a729ce52946328c631adad5b56b4b5ab5a56b4b5695a4eb5a4eb4a52b4a56b49ce94a52739d273a4e729d273a4e739ce739d2729ca739ce7394e7294e32
def b169 : ℕ := 0x12946308c210a4e94a4e539ce939ce339ce539ce519463294a318c231a5ad5ad295a5694adab5ad695a5695a4eb59d692a5294a5293a529394e939ca9294e31a52939ca749ce539ce729ca338ce319ca51
def b170 : ℕ := 0x12946518c210ad294ad231a4e939ce539ce739ce729ce5294a328c631adaf6b5673b5ab39dad3b5ab69ced69cab5a56b4a56b4a5294a52949d294a46938d233a52939ce749d273a4e739ce7394e729ce12
def b171 : ℕ := 0x128c6528c210ad693a5293a4e739ce7394e7394a739d272946328ca31b5ad6b5ad5bdad6ad6b5b56b5ad2d5ad6b4ad2b5a56b49ce94a5274a5274a5273a5294a4e739d2739d2929ca739ce939ce9394e53
def b172 : ℕ := 0x108c6528c2109ce51a5293a46318ce7394e7394a739d270946328ca31a5294a5293ad296aceb5b56b39cad5ad672ad2b594e728c652a5234a5274a5233a5294946318ca339d2929ca739ce939ce9394e53
def b173 : ℕ := 0x128c6108c2109ce9394a5394e739ce3394e3394a318ca32946308c231a5a94a5295ad294ad675a4e739d2939ceb49d273a4e749ce92a527294a7294a7194a52a4e739ca739ca528ca719c6538ce5194651
def w64 := mergeW 0 w13 w4
def b174 : ℕ := 0x128c6528c210ad691a5292a4e739ce7394e7394a739d272946328ca31b5ad6b5ad4bdad6a4eb4b56b39ced5a52b4ad2b5a56b48ce94a5234a5274a5233a5294a4e739d2739d2929ca739ce939ce9394e33
def b175 : ℕ := 0x128c6528c210ad692a5292a4e739ce7394e7394a739d272946328ca31b5ad6b5ad4bdad6a52b4b56b4a52d5a52b4ad2b5a56b494e94a5254a5274a5253a5294a4e739d2739d2929ca739ce939ce9394e33
def b176 : ℕ := 0x12846518c210ad2929ca73a4e539ce538ce738c6729ce52942328c631adab4b56b5b5ab5ad295b52749ce94ad2b3a4eb4a56b494a94a52529d252a4e519d273a4a539ce729d271946739ce7394e728ce52
def b177 : ℕ := 0x128c6518c210ad292a4e73a4e739ce5394e7394a729ce52946328c631adad5b56b5b5ab5ad2b5b56949ceb5ad2b4a52b4a56b494e94a52539d273a4e529d273a4e739ce739d2729ca739ce7394e7294e52
def b178 : ℕ := 0x128c6128c2109d6919529394e739ce7394e3394a338ca72946308ca31b5a96a5ad5ad2d6ace75a4eb39ca939d6b4ad273a4e748ce92a5234a4a7495233a4a52a4e739d2739ca928ca719c6539ce5394653
def b179 : ℕ := 0x118c65284210a5253a52929ca5294e7294e72946739d251946328ca30ad2b5ad6b3b5296a56b4ad6b5aced4a5293a4eb59d29294653a4e74a4e74a5272a4e939ca5294e539d2929c67394e939ca928ce32
def b180 : ℕ := 0x108c6508c2109ce53a4a53a46318ce3394e7394a719ca30946328c231a5294a5293ad294ad6b5b56759d295ace729d2b394e728c652a527295272a4a7195252946318ca339d2529ca739ce538ce5194e51
def b181 : ℕ := 0x128c63284210a56739d29294e739ce7294e529465394e52946318ca30b56b6adad4b52b6a5694a52b4aceb39d2b4a4e94a52939ca73a4e74a4a749d272a4a72a4e739d2739ce929467294a739ca728ca32
def b182 : ℕ := 0x12846328c210a569294e939ce539ce738ce538c65394e72942318ca31b5a95adad5b56d6ad275ace93a4e93a56b3ace94a529494a93a5253a4e539d252a4e73a4a539d2729ce918c6729ca739ce738ca53
def b183 : ℕ := 0x128c6528c210ad692a5291a4e739ce7394e7394a739d272946328ca31b5ad6b5ad3bdad69d2b3b56b4a4ed59ceb4ad2b5a56b494e94a5254a5274a5253a5294a4e739d2739d2929ca739ce939ce9394e13
def b184 : ℕ := 0x11846528c210a52729ce93a4a3294e738ce738c6739d271942328ca31ad694ad6b4b56b6ad295b5294a4eb4ad692aceb59d2938c673a5253a5253a5252a52949c63294e529d291946739ce939ce938ce53
def b185 : ℕ := 0x128c6528c210ad691a5291a4e739ce7394e7394a739d272946328ca31b5ad6b5ad3bdad69ceb3b56b39cad59ceb4ad2b5a56b48ce94a5234a5274a5233a5294a4e739d2739d2929ca739ce939ce9394e13
def w65 := mergeW 0 w8 w21
def b186 : ℕ := 0x11942328c21095273a56729ca728ca739ca539ce538ce7194a318ca11ad6969d693a4eb5a56b4ad6d4ad2d59d274ad6749ca5394e729d275a4e959ce749ce539ce728ce349ce939ce529c6729ce739c633
def b187 : ℕ := 0x11942328c2108d273a56729ca728ca739ca539ce538ce7194a318ca11ad676956939cab5a56b4ad6d4ad2d59d274ad6749c63394e719d275a4e959ce749ce539ce728ce349ce939ce529c6729ce739c633
def w66 := mergeW 0 w4 w21
def b188 : ℕ := 0x11946328c21095274a56929ca7294e739ce539ce5394e7194a318ca31ad6969d6b3a4eb6a5ab4ad6d5b52d59d294ad6949ca539ce71a5295a4e959d294a4e739ce7294e549ce939ce729ca739ce739ca33
def b189 : ℕ := 0x11946308c21094a74a4e539ca7294e339ce539ce519463194a318c2319d6949ce74a4e74adab5ad695a5695a4e949d6929ca539ce71a529394e939ca9294e319ce72946549ce539ce729ca338ce319ca51
def b190 : ℕ := 0x11846328c2109527294e939ca3294e738ce538c65394e71942318ca31ad6949d6b4a4eb6ad275ace93a4e93a5692ace949ca538c671a5253a4e539d252a4e739c63294e529ce918c6729ca739ce738ca53
def b191 : ℕ := 0x118c6318c2109ce739ce739ca5294e5394e5394a5294a51946318c631a5694a5294a5295ad695ad294a5294a5293a52939ce7394a72a52739ce739ce729ce529ca5294a539ce7294a729ca5394e5294a52
def b192 : ℕ := 0x1194632842109d254a569294a7294e729ce529ca5394e5194a318ca30ad2b6a56b3ace96a5ab4a56d5b52d49d294a52949ce729ca52a4e95a4a959d293a4a729ce7294e549ce939ca7294a739ca7294a32
def b193 : ℕ := 0x11946328c21095274a56939ca7294e739ce539ce5394e7194a318ca31ad6969d6b4a4eb6adab5ad6d5b56d5a5694ad6949ca539ce71a5295a4e959d294a4e739ce7294e549ce939ce729ca739ce739ca53
def w67 := mergeW 0 w4 w3
def b194 : ℕ := 0x11946308c2109ca74a4e529ca7294e339ce539ce519463194a318c2319d6b4a4e739d274a5ab4ad695a52959d2949d6929ce739ce72a529394e939ca9294e319ce72946549ce539ce729ca338ce319ca31
def w68 := mergeW 0 w9 w4
def b195 : ℕ := 0x11846328c2109d27294e929ca3294e738ce538c65394e71942318ca31ad674a56b3ad2b6a5274ace93a52939d292ace949ce738c672a5253a4e539d252a4e739c63294e529ce918c6729ca739ce738ca33
def b196 : ℕ := 0x11946328c21095274a56919ca7294e739ce539ce5394e7194a318ca31ad6969d6b2a4eb69dab3ad6d5b4ed594e94ad6949ca539ce71a5295a4e959d294a4e739ce7294e549ce939ce729ca739ce739ca13
def w69 := mergeW 1 w4 w21
def b197 : ℕ := 0x11946308c2108ca74a4e539ca7294e339ce539ce519463194a318c2319d67494e749ca74adab5ad695a5695a4e949d6929c6339ce70a529394e939ca9294e319ce72946549ce539ce729ca338ce319ca51
def b198 : ℕ := 0x11846328c2108d27294e939ca3294e738ce538c65394e71942318ca31ad674956b49cab6ad275ace93a4e93a5692ace949c6338c670a5253a4e539d252a4e739c63294e529ce918c6729ca739ce738ca53
def b199 : ℕ := 0x10946318c21094a54a52739c6518ce539ce539ce5294a5094a318c6319d2949ce739ce75adab5ad6b5ad6b5a5273a569394a5294a51a52949ce949ce939ce5294a518c6349ce739ce729ca5394e529ca52
def b200 : ℕ := 0x118c6128c210952739529394a5294e7394e3394a338ca71946308ca31ad6759d6b4a4eb6ad675a4eb3ad2939d693ad2739ca5394a71a5274a4a7495273a4a529ca5294e539ca928ca719c6539ce5394653
def b201 : ℕ := 0x11942318c2109ce73a52529ca728ca539ca539ce528ca5194a318c611a56b5a5273a5294a56b4ad6b4a52b59ce74a56739ce7394e719d2749ce949ca7394e329ce728ca349ce739ce529c65294e529c632
def b202 : ℕ := 0x118c2328c2109d2729d2729ca528ca7394a5394a538ce71946318ca11ad695a5693ad2b5a5294ad2b3a4eb49d273ad2749ce738ca719d254a4e749ce539ce539ca528ce339ce9294a529c6729ce7394633
def w70 := mergeW 1 w8 w21
def b203 : ℕ := 0x11942328c2109d273a56729ca728ca739ca539ce538ce7194a318ca11ad6b6a5693ad2b5a56b4ad6d4ad2d59d274ad6749ce7394e719d275a4e959ce749ce539ce728ce349ce939ce529c6729ce739c633
def b204 : ℕ := 0x11946118c21094e749d27394a7294e539ce339ce328c65194a308c631a56959d2949ce95ada95a52b4ad6949d294a56729ca539ce71a52949ca9494e939ca319ce7294a549ca7394e719c63394e329c652
def w71 := mergeW 0 w5 w14
def b205 : ℕ := 0x128c65184210ad273a4a729ce739ce5294e72946729ce32946328c630ad6d4b56b4b5695a56b4ad6759ce94a4eb49ceb4a56b39ca74a4e729ce72a4e729ce72a4e739ce739d2729c67394e7394a718ce31
def b206 : ℕ := 0x128c65184210ad273a46729ce739ce5294e72946729ce32946328c630ad6d3b56b4b5695a56b4ad65594e74a4eb49ceb4a56b39ca74a4e719ce71a4e719ce72a4e739ce739d2729c67394e7394a718ce31
def w72 := mergeW 0 w4 w14
def b207 : ℕ := 0x128c6518c210ad293a4a72a4e739ce5394e7394a729ce52946328c631adad4b56b4b5ab5a56b4b56759ce95a4eb4a52b4a56b49ce94a52729d272a4e719d273a4e739ce739d2729ca739ce7394e7294e32
def b208 : ℕ := 0x108c6518c2109ca53a4a73a46318ce5394e7394a729ce50946328c6319d294a4e73a5275ad6b5b56759d295ad272a52b494e728c652a52729d272a4e719d273946318c6339d2729ca739ce7394e7294e52
def b209 : ℕ := 0x128c6118c2109d29394a7394e739ce5394e3394a328c652946308c631ada94a56b5a52b5ad675a4e739d2939d2b4a5272a4e749ce92a52729ca7294e719ca31a4e739ce739ca728ca719c63394e3294652
def b210 : ℕ := 0x128c2518c210ad292a4e52a4e7394a5394a7394a7294e52946328c611adad5b5694b5ab4a52b4b56949ceb5a4e94a5294a56b494e939d2539d273a4a5295253a4e7394e539d2729ca539ca7294e7294a32
def b211 : ℕ := 0x128c6518c210ad293a4a73a4e739ce5394e7394a729ce52946328c631adad4b56b5b5ab5ad6b5b56759d295ad2b4a52b4a56b49ce94a52729d272a4e719d273a4e739ce739d2729ca739ce7394e7294e52
def w73 := mergeW 0 w4 w0
def b212 : ℕ := 0x108c6518c2109ca53a4e72a46318ce5394e7394a729ce50946328c6319d293a4e74a5275a56b4b5695a4eb5a4e72a52b494e728c652a52739d273a4e729d273946318c6339d2729ca739ce7394e7294e32
def w74 := mergeW 0 w6 w4
def b213 : ℕ := 0x128c6118c2109d29394e7294e739ce5394e3394a328c652946308c631ada95a56b4a52b5a5674a4e93a4e73a4eb4a5272a4e749ce92a52739ca7394e729ca31a4e739ce739ca728ca719c63394e3294632
def b214 : ℕ := 0x128c6518c210ad293a4a71a4e739ce5394e7394a729ce52946328c631adad4b56b3b5ab59d6b3b56759ca959cab4a52b4a56b49ce94a52729d272a4e719d273a4e739ce739d2729ca739ce7394e7294e12
def w75 := mergeW 1 w4 w14
def b215 : ℕ := 0x108c6518c2109ca53a4673a46318ce5394e7394a729ce50946328c6319d293a4e73a5275ad6b5b565595275ad272a52b494e728c652a52719d271a4e709d273946318c6339d2729ca739ce7394e7294e52
def b216 : ℕ := 0x128c6118c2109d2939467394e739ce5394e3394a328c652946308c631ada93a56b5a52b5ad675a4e53952739d2b4a5272a4e749ce92a52719ca7194e709ca31a4e739ce739ca728ca719c63394e3294652
def b217 : ℕ := 0x118c6508c210a4a73a4a53a4a5294e3394e7394a719ca31946328c2319d6b3ace74a5674ad6b5b56759d295ace939d2b39d29394a73a527295272a4a71952529ca52946539d2529ca739ce538ce5194e51
def b218 : ℕ := 0x12846318c210a529294a739ce539ce538ce538c65294a52942318c631ada94ad6b5ad6b5ad275ace739ce73a52b3a4e93a529494a93a52529ce529ce519ce52a4a539ce729ce718c6729ca5394e528ca52
def b219 : ℕ := 0x118c65184210a4e53a4e729ca5294e5294e72946729ce31946328c630a52b4ad293ad275a56b4ad695a4eb4a4e939ceb49d29294653a4e739ce73a4e719ce729ca5294a539d2729c67394e7394a718ce31
def b220 : ℕ := 0x128c63184210a52739ce7294e739ce5294e529465294a32946318c630ad6b5ad6b4ad295a5694a5294a4e939ceb49ce93a52939ca73a4e739ca739ce719ca51a4e739ce739ce729467294a5394a518ca31
def w76 := mergeW 1 w5 w14
def b221 : ℕ := 0x128c65184210ad273a4e729ce739ce5294e72946729ce32946328c630ad6d5b56b4b5695a56b4ad695a4eb4a4eb49ceb4a56b39ca74a4e739ce73a4e719ce72a4e739ce739d2729c67394e7394a718ce31
def b222 : ℕ := 0x128c6308c210a4e939ca539ce739ce3394e5394a5194632946318c231a5ab4ad295a5694ad695ad2749d274a4eb49d292a52949ce93a527294e729ca7194e31a4e739ca739ce5294a729ca338ce3194a51
def w77 := mergeW 0 w4 w12
def b223 : ℕ := 0x11946518c210a4a74ad272a4a7294e539ce739ce729ce5194a328c6319d6d4ace73a5675a5ad4b5ab6ad2d6a4e94a56b49d2939ce73a52949d294a4e939d2739ce72946549d273a4e739ce7394e729ce32
def b224 : ℕ := 0x11846118c21094e729ca7394a3294e538ce338c6328c651942308c631a56939d2949ce95ad295a52749ce949d292a4e729ca538c671a52529ca5294e519ca319c63294a529ca71946719c63394e328c652
def w78 := mergeW 0 w6 w12
def b225 : ℕ := 0x11946118c21094a749d27394a7294e539ce339ce328c65194a308c6319d6949ce74a4e75ada95a52b4ad6949d294a56729ca539ce71a52949ca9494e939ca319ce72946549ca7394e719c63394e329c652
def b226 : ℕ := 0x11946118c21094e749d27294a7294e539ce339ce328c65194a308c631a56959d2939ce95a5a94a52b4ad294a4e94a56729ca539ce71a52949ca9494e939ca319ce7294a549ca7394e719c63394e329c632
def w79 := mergeW 0 w9 w12
def b227 : ℕ := 0x11846518c210a4a729ca73a4a3294e538ce738c6729ce51942328c6319d694ace74a5675ad295b52749ce94ad292a4eb49d2938c673a52529d252a4e519d2739c632946529d271946739ce7394e728ce52
def b228 : ℕ := 0x11846518c210a4e729ca72a4a3294e538ce738c6729ce51942328c631a5693ad293ad695a5294b52749d294a4e92a4eb49d2938c673a52529d252a4e519d2739c63294a529d271946739ce7394e728ce32
def w80 := mergeW 1 w4 w12
def b229 : ℕ := 0x1194631842109ce54a527294a7294e529ce529ca5294a3194a318c630a52b5a5293a4e75a5ab4a56b5ad2b49ce949d2939ce729ca52a4e949ca949ce929ca519ce7294a549ce739ca7294a5394a5194a31
def b230 : ℕ := 0x118c2518c210a4e72a4e52a4a528ca5394a7394a7294e51946328c611a56b4ad273ad694a52b4b56949ceb5a4e73a52949d2938ca729d2539d273a4a52952539ca528ca339d2729ca539ca7294e7294a32
def b231 : ℕ := 0x11946308c2109ca74a4e539ca7294e339ce539ce519463194a318c2319d6b4a4e749d274adab5ad695a5695a4e949d6929ce739ce72a529394e939ca9294e319ce72946549ce539ce729ca338ce319ca51
def w81 := mergeW 0 w15 w4
def b232 : ℕ := 0x128c6328c210a5693952929ce739ce7394e5394a5394e72946318ca31b5a96adad4b56d6a5674aceb3ace939d2b4ad294a52949ce93a5274a4e749d273a4e73a4e739d2739ce928ca729ca739ce7394a33
def b233 : ℕ := 0x108c6308c21094e539ca539c6318ce3394e5394a5194630946318c231a52749d293a4e94ad695ad2749d274a4e729d29294a528c651a527294e729ca7194e31946318ca339ce5294a729ca338ce3194a51
def b234 : ℕ := 0x108c6328c21094e539d2929c6318ce7394e5394a5394e70946318ca31a52749d294a4e96a5694ad2b4aceb49d272ad29494a528c651a5274a4e749d273a4e73946318ca339ce9294a729ca739ce7394a33
def b235 : ℕ := 0x128c6308c210a4e939ca529ce739ce3394e5394a5194632946318c231a5ab4ad294a5694a5694ad2749ce749d2b49d292a52949ce93a527294e729ca7194e31a4e739ca739ce5294a729ca338ce3194a31
def w82 := mergeW 0 w15 w0
def b236 : ℕ := 0x108c6328c21094e53952939c6318ce7394e5394a5394e70946318ca31a52949d293a4e96ad675aceb3ad293a5672ad29494a528c651a5274a4e749d273a4e73946318ca339ce928ca729ca739ce7394a53
def w83 := mergeW 0 w15 w3
def b237 : ℕ := 0x128c6308c210a4e9394a539ce739ce3394e5394a5194632946318c231a5a94ad295a5694ad675ace739d293a4eb49d292a52949ce93a527294e729ca7194e31a4e739ca739ce528ca729ca338ce3194a51
def w84 := mergeW 1 w15 w4
def b238 : ℕ := 0x118c632842109d2539d29294a5294e7294e529465394e51946318ca30ad295a56b3ace96a5694a52b4aceb39d293a4e949ce7294652a4e74a4a749d272a4a729ca5294e539ce929467294a739ca728ca32
def b239 : ℕ := 0x128c2318c210a52929ce529ce7394a5394a5394a528ca52946318c611adab5ad694ad6b4a5294ad2939ce949ce94a5273a529494e929d2539ce739ca5294e32a4e7394e539ce7294a529c65294e5294632
def b240 : ℕ := 0x128c6118c2109d29394e7394e739ce5394e3394a328c652946308c631ada95a56b5a52b5ad675a4e93a52739d2b4a5272a4e749ce92a52739ca7394e729ca31a4e739ce739ca728ca719c63394e3294652
def b241 : ℕ := 0x119465284210a5254ad6929ca7294e729ce729ca739d25194a328ca30ad2d6ad6b3b5296a5ad4adad6b52f5a5294a52b59d2929ca53a4e95a4e95a5293a4e939ce7294e549d293a4a7394e939ca9294e32
def b242 : ℕ := 0x118465284210a52329ce929ca3294e728ce728c2739d251942328ca30ace94ad6b2b4e76a5294ad294a4ab3a5292a4ab59d2918c633a4e53a4e53a5251a4e939c63294e529d2919427394e939ca9284e32
def b243 : ℕ := 0x119465084210a4a34ace529ca7294e329ce729ca719ca1194a328c2309ced4ace72a4e74a5ad4ada96a52b5a4a94952b39d2919c633a4e9394e93a4a9194e519ce72946549d253a4a7394e538ca5094e30
def b244 : ℕ := 0x119465284210a5234ad6919ca7294e729ce729ca739d25194a328ca30aced6ad6b3b4e769dad3adad6b4ef59ce94a52b59d2919c633a4e95a4e95a5293a4e939ce7294e549d293a4a7394e939ca9294e12
def b245 : ℕ := 0x119461284210952549d6918ca7294e729ce329ca338ca5194a308ca30ad2969d6b2a4a969da939d2d4b4eb39ce94a52739ca529ca51a4e95a469595293a46519ce7294e549ca9394a71946539ca5294612
def b246 : ℕ := 0x11946108421094a549ce528ca7294e329ce329ca318ca1194a308c2309d2949ce73a4a54a5a949d294a52b394a94952739ca529ca51a4e939469394a91946519ce72946549ca5394a71946538ca5094630
def b247 : ℕ := 0x119465084210a4a54ace519ca7294e329ce729ca719ca1194a328c2309d2d4ace72a52549dad3ada96a4eb59ce94952b39d2929ca53a4e9394e93a4a9194e519ce72946549d253a4a7394e538ca5094e10
def w85 := mergeW 1 w9 w10
def w86 := mergeW 0 w6 w10
def b248 : ℕ := 0x119461284210952349d6928ca7294e729ce329ca338ca5194a308ca30ace969d6b2a4e76a5a949d2d4b52b395294a52739ca519c631a4e95a469595293a46519ce7294e549ca9394a71946539ca5294632
def b249 : ℕ := 0x129463284210a5674a569294e939ce729ce529ca5394e5294a318ca30b56d7adad4b52b6a5ab4a56d5b52d49d2b5a5294a5293a4e73a4e95a4a959d293a4a72a52939d2749ce939ca7294a739ca7294a32
def b250 : ℕ := 0x129463084210a4e74a4e528ce939ce329ce529ca519461294a318c230a56d5ad294a4e74a5ab49d695a529394ab595292a5293a4e73a4e93946939ca9194631a52939ca749ce539ca7294a338ca3094a30
def b251 : ℕ := 0x128463284210a567294e928ce539ce728ce528c25394e52942318ca30b5695adad4b4eb6a52749ce93a4a93952b3a4a94a529394673a4e53a46539d251a4671a4a539d2729ce918c27294a739ca7284a32
def b252 : ℕ := 0x129463284210a5674a56918ce939ce729ce529ca5394e5294a318ca30b56d7adad3b4eb69dab39d6d5b4ed39ceb5a5294a5293a4e73a4e95a46959d293a4671a52939d2749ce939ca7294a739ca7294a12
def b253 : ℕ := 0x10946328421094e34a5691946518ce729ce529ca5394e5094a318ca30a4e959d293a4a769dab3a56d5b4ed494e73a529494a5194631a4e95a4a959d293a4a7294a518ca349ce939ca7294a739ca7294a12
def b254 : ℕ := 0x10846328421094e3294e92946518ce728ce528c25394e50942318ca30a4e959d292a4a76a5274a4e93a4a929d273a4a9494a5194631a4e53a4a539d251a4a7294a518ca329ce918c27294a739ca7284a32
def b255 : ℕ := 0x128463284210a567294e9194e539ce728ce528c25394e52942318ca30b5695adad3b52b69d273a4e93a4e9294eb3a4a94a529394673a4e53a4a539d251a4a72a4a539d2729ce918c27294a739ca7284a12
def w87 := mergeW 1 w26 w3
def w88 := mergeW 0 w26 w0
def b256 : ℕ := 0x10946328421094e34a56928c6518ce729ce529ca5394e5094a318ca30a4e959d292a4e76a5ab49d6d5b52d395273a529494a5194631a4e95a46959d293a467194a518ca349ce939ca7294a739ca7294a32
def b257 : ℕ := 0x12942518c210ad293ad252a4e9394a539ca739ce7294e5294a328c611adaf6b5694b5ab4a56d4b5ab5a52d6a4e95a5694a56b49d2939d2749d294a4a7395253a529394e549d273a4e539ca7294e729ca32
def b258 : ℕ := 0x12942118c2109d2939d23294e9394a539ca339ce328465294a308c611adab6a5674a52b3a5694a52b39d29494a95a5652a4e749d2919d2749ca94946738ca31a529394e549ca7394e519c23294e329c232
def b259 : ℕ := 0x10942518c2109ca53ad232a465184a539ca739ce7294e5094a328c6119d2b4a4e72a5273a56d4b5ab59d2d6a4a53a569494e728ca519d2749d294a46738d23394a51846149d273a4e539ca7294e729ca32
def b260 : ℕ := 0x12942518c210ad293ad231a4e9394a539ca739ce7294e5294a328c611adaf6b5673b5ab39d6d3b5ab59ced69ce95a5694a56b49d2939d2749d294a46738d233a529394e549d273a4e539ca7294e729ca12
def b261 : ℕ := 0x12842518c210ad2919ca51a4e5394a538ca738c67294e52942328c611adab4b5693b5ab49ce93b527394e949ca93a4e94a56b48ca939d2329d252a4a3195253a4a5394e529d271946539ca7294e728ca12
def b262 : ℕ := 0x10842518c2109ca519ca52a465184a538ca738c67294e50942328c6119d2b4a4e52a5274a4e94b527394a94a4e53a4e9494e728ca519d2329d252a4a319525394a51846129d271946539ca7294e728ca32
def b263 : ℕ := 0x10942518c2109ca53ad251a465184a539ca739ce7294e5094a328c6119d2b4a4e53a52749d6d3b5ab5a4ed69ca53a569494e728ca519d2749d294a4a739525394a51846149d273a4e539ca7294e729ca12
def w89 := mergeW 1 w6 w17
def w90 := mergeW 0 w9 w17
def b264 : ℕ := 0x12842518c210ad2919ca32a4e5394a538ca738c67294e52942328c611adab4b5674b5ab3a4e94b52739ca94a4a93a4e94a56b48ca939d2329d252a46318d233a4a5394e529d271946539ca7294e728ca32
def b265 : ℕ := 0x128c2528c210ad692a5272a4e7394a7394a7394a7395272946328ca11b5ad6b5ab4bdad5a52b4b56b4a4ed5a5294ad295a56b494e939d254a5274a4e539d274a4e73952539d2929ca539ca929ce9394a33
def b266 : ℕ := 0x108c2528c2109ce51a5272a463184a7394a7394a7395270946328ca11a5294a5272ad295a4eb4b56b39cad5a5252ad29594e728c6519d234a5274a4e339d2749463184a139d2929ca539ca929ce9394a33
def b267 : ℕ := 0x128c2128c2109d6919527294e7394a7394a3394a3384a72946308ca11b5a96a5ab4ad2d5a4e74a4eb39ca9395294ad253a4e748ce919d234a4a7494e339ca32a4e73952539ca928ca519c2529ce5394233
def b268 : ℕ := 0x128c2528c210ad691a5271a4e7394a7394a7394a7395272946328ca11b5ad6b5ab3bdad59ceb3b56b39ced59ce94ad295a56b48ce939d234a5274a4e339d274a4e73952539d2929ca539ca929ce9394a13
def b269 : ℕ := 0x128c2508c210ace92a4a31a4e7394a3394a7394a7194a32946328c211a5ad4b5273ada939d2b3b567494a959ce949d293a56b494e939d25295272a46518d232a4e7394a539d2529ca539ca528ce5194a11
def b270 : ℕ := 0x128c2108c2109ce9294a3294e7394a3394a3394a3184a32946308c211a5a94a5274ad293a5274a4e7294e9394a949d253a4e7494e919d25294a72946518ca32a4e7394a539ca528ca519c2528ce5194231
def b271 : ℕ := 0x128c2128c2109d6929527194e7394a7394a3394a3384a72946308ca11b5a96a5ab3ad2d59d273a4eb2a4a939ce94ad253a4e7494e919d254a4a7494e539ca32a4e73952539ca928ca519c2529ce5394213
def w91 := mergeW 1 w13 w0
def w92 := mergeW 0 w13 w3
def b272 : ℕ := 0x128c2508c210ace91a4a32a4e7394a3394a7394a7194a32946328c211a5ad4b5274ada93a4eb4b56739ca95a4a949d293a56b48ce939d23295272a46318d232a4e7394a539d2529ca539ca528ce5194a31
def b273 : ℕ := 0x12946108c2109ce949ce5394e939ce339ce339ce318ca3294a308c231a5ab5a5295ad294ada95a5294a56b49ceb59d673a4e74a5292a529394a9394a9294a52a52939ca749ca5394e719c6538ce519c651
def b274 : ℕ := 0x10846108c2108c6528c653946518ce338ce338c6318ca30942308c2319527394a539ca54ad255a4a5294e729ce739ce739463294a50a525194a5194a5094a5294a518c2329ca51846719c6538ce518c651
def w93 := mergeW 1 w18 w2
def w94 := mergeW 1 w18 w5
def w95 := mergeW 1 w18 w8
def b275 : ℕ := 0x10946108c2108c6549ce52946518ce339ce339ce318ca3094a308c2319527394a549ca54a5a94a5294a52b494a739d6739463294a50a529394a9394a9294a5294a518c2349ca5394e719c6538ce519c631
def b276 : ℕ := 0x12846108c2109ce928c65294e539ce338ce338c6318ca32942308c231a5a73a5294ad294a5254a4a529527294ab39ce73a4e7494a92a525194a5194a5094a52a4a539ca729ca51846719c6538ce518c631
def b277 : ℕ := 0x118c6108c21094a7394a5394a5294e3394e3394a318ca31946308c2319d6739ce74a4e74ad675a4e739d2939ce939d2739ca5394a71a527294a7294a7194a529ca52946539ca528ca719c6538ce5194651
def w96 := mergeW 1 w18 w4
def w97 := mergeW 1 w18 w1
def b278 : ℕ := 0x10846528c2109ce529ce93a46518ce738ce738c6739d270942328ca31a52b5a5293ad296ad295b5294a4eb4ad673aceb594e7294a52a5253a5253a5252a529494a518ca329d291946739ce939ce938ce53
def w98 := mergeW 1 w28 w2
def w99 := mergeW 1 w28 w5
def w100 := mergeW 1 w28 w8
def b279 : ℕ := 0x10846508c2109c6529c652a46518ce338ce738c6719ca30942328c231952b3a4a529d254a5294b525494a74a52739ceb394e7294a52a525195251a4a509525294a518c2329d251946739ce538ce518ce31
def b280 : ℕ := 0x10846128c2108ce528ce92946518ce738ce338c6338ca70942308ca31a5275952929ca96a5254a4a92a4a72a5273ace739463294a50a5253a4a5395252a4a5294a518ca329ca91846719c6539ce538c633
def b281 : ℕ := 0x10846318c21094a5294a739c6518ce538ce538c65294a50942318c6319d2949ce739ce75ad275ace739ce73a5273a4e9394a5294a51a52529ce529ce519ce5294a518c6329ce718c6729ca5394e528ca52
def w101 := mergeW 1 w28 w4
def w102 := mergeW 1 w28 w1
def w103 := mergeW 0 w4 w29
def b282 : ℕ := 0x12946318c210a5294a52729ce939ce539ce539ce529465294a318c631adad6ad6b4a56b5a5ab4ad6b5ad2959ceb5a5692a5294a5293a52949ce949ce939ce31a52939ce749ce739ce729ca3394e329ca32
def w104 := mergeW 1 w4 w29
def b283 : ℕ := 0x10946318c21094a54a52729c6518ce539ce539ce5294a5094a318c6319d2949ce749ce75a5ab4ad6b5ad2b59ce73a569394a5294a51a52949ce949ce939ce5294a518c6349ce739ce729ca5394e529ca32
def b284 : ℕ := 0x12846318c210a529294a729ce539ce538ce538c65294a52942318c631ada94ad6b4ad6b5a5274ace739d2739ceb3a4e93a529494a93a52529ce529ce519ce52a4a539ce729ce718c6729ca5394e528ca32
def w105 := mergeW 0 w29 w0
def b285 : ℕ := 0x10946318c21094a54a52739c6518ce539ce539ce529465094a318c6319d2949ce73a4e75adab5ad6b5ad695a5273a569294a5294a51a52949ce949ce939ce3194a518c6349ce739ce729ca3394e329ca52
def w106 := mergeW 0 w9 w29
def b286 : ℕ := 0x12846318c210a529294a739ce539ce538ce538c65294652942318c631ada94ad6b5a56b5ad275ace739ce93a52b3a4e92a529494a93a52529ce529ce519ce31a4a539ce729ce718c6729ca3394e328ca52
def w107 := mergeW 0 w4 w19
def b287 : ℕ := 0x118c6528c210a5273a5292a4a3294e7394e7394a739d271946328ca31ad694ad6b3b56b6a56b4b56b5aced5a5292ad2b59d2938c673a5274a5274a5273a52949c63294e539d2929ca739ce939ce9394e33
def w108 := mergeW 1 w4 w19
def b288 : ℕ := 0x118c6508c210a4a73a4a52a4a5294e3394e7394a719ca31946328c2319d6b3ace73a5674a56b4b56759ce95a52939d2b39d29394a73a527295272a4a71952529ca52946539d2529ca739ce538ce5194e31
def b289 : ℕ := 0x118c6128c210952739529294a5294e7394e3394a338ca71946308ca31ad6759d6b3a4eb6a5674a4eb3ace93a5293ad2739ca5394a71a5274a4a7495273a4a529ca5294e539ca928ca719c6539ce5394633
def w109 := mergeW 0 w3 w19
def b290 : ℕ := 0x118c6508c210a4a73a4a53a4a3294e3394e7394a719ca31946328c2319d694ace74a5674ad6b5b56759d295ace929d2b39d2938c673a527295272a4a71952529c632946539d2529ca739ce538ce5194e51
def w110 := mergeW 0 w6 w19
def b291 : ℕ := 0x118c6128c210952739529394a3294e7394e3394a338ca71946308ca31ad6949d6b4a4eb6ad675a4eb3ad2939d692ad2739ca538c671a5274a4a7495273a4a529c63294e539ca928ca719c6539ce5394653
def b292 : ℕ := 0x108c6328c21094e539d2939c6318ce7394e5394a5394e70946318ca31a52749d293a4e96ad695ad2b4ad2b4a5672ad29494a528c651a5274a4e749d273a4e73946318ca339ce9294a729ca739ce7394a53
def b293 : ℕ := 0x11846518c210a4e729ca73a4a3294e538ce738c6729ce51942328c631a5693ad294ad695ad295b52749ce94ad292a4eb49d2938c673a52529d252a4e519d2739c63294a529d271946739ce7394e728ce52
def w111 := mergeW 0 w9 w22
def b294 : ℕ := 0x11846528c210a52729ce93a4a3294e738ce738c6739d271942328ca31ad694ad6b3b56b6ad295b5294a4eb4ad692aceb59d2938c673a5253a5253a5252a52949c63294e529d291946739ce939ce938ce53
def w112 := mergeW 0 w3 w22
def b295 : ℕ := 0x11946508c210a4a74ace53a4a7294e339ce739ce719ca3194a328c2319d6d4ace73a5674adad5b5a96a56b6ace949d6b39d2939ce73a529395293a4a92952529ce72946549d253a4e739ce538ce519ce51
def w113 := mergeW 0 w6 w22
def b296 : ℕ := 0x11946128c210952749d69394a7294e739ce339ce338ca7194a308ca31ad6969d6b3a4eb6ada95a52d4b56b49d694ad6739ca539ce71a5295a4a9595294a4a529ce7294e549ca9394e719c6539ce539c653
def w114 := mergeW 0 w6 w37
def b297 : ℕ := 0x12946118c2109d2949d27394e939ce539ce339ce328c65294a308c631adab6a56b5a52b5ada95a52b4ad6949ceb5a5672a4e74a5292a52949ca9494e939ca31a52939ce749ca7394e719c63394e329c652
def w115 := mergeW 0 w37 w0
def b298 : ℕ := 0x10946518c2109ca54ad273a46518ce539ce739ce729ce5094a328c6319d2b4a4e73a5275adad5b5ab6ad6d6ace73a56b494e7294a52a52949d294a4e939d27394a518c6349d273a4e739ce7394e729ce52
def w116 := mergeW 0 w9 w37
def b299 : ℕ := 0x12846518c210ad2929ca73a4e539ce538ce738c6729ce52942328c631adab4b56b5b5ab5ad295b52749ce94aceb3a4eb4a56b494a94a52529d252a4e519d273a4a539ce729d271946739ce7394e728ce52
def w117 := mergeW 0 w31 w3
def b300 : ℕ := 0x12946308c210a4e94a4e539ce939ce339ce539ce519463294a318c231a5ad5ad295a5694adab5ad695a56959ceb59d692a5294a5293a529394e939ca9294e31a52939ca749ce539ce729ca338ce319ca51
def w118 := mergeW 0 w9 w31
def b301 : ℕ := 0x12846328c210a569294e939ce539ce738ce538c65394e72942318ca31b5a95adad5b56d6ad275ace93a4e939d6b3ace94a529494a93a5253a4e539d252a4e73a4a539d2729ce918c6729ca739ce738ca53
def w119 := mergeW 0 w31 w0
def b302 : ℕ := 0x10946328c21094e54a56939c6518ce739ce539ce5394e7094a318ca31a52959d293a4e96adab5ad6d5b56d59d673ad69494a5294a51a5295a4e959d294a4e7394a518ca349ce939ce729ca739ce739ca53
def w120 := mergeW 0 w41 w0
def b303 : ℕ := 0x108c6528c2109ce53a5293a46318ce7394e7394a739d270946328ca31a5294a5293ad296ad6b5b56b5aced5ad672ad2b594e728c652a5274a5274a5273a5294946318ca339d2929ca739ce939ce9394e53
def w121 := mergeW 0 w6 w41
def b304 : ℕ := 0x128c6128c2109d6939529394e739ce7394e3394a338ca72946308ca31b5a96a5ad5ad2d6ad675a4eb3ace939d6b4ad273a4e749ce92a5274a4a7495273a4a52a4e739d2739ca928ca719c6539ce5394653
def w122 := mergeW 0 w41 w3
def b305 : ℕ := 0x128c6508c210ace93a4a53a4e739ce3394e7394a719ca32946328c231a5ad4b5295ada94ad6b5b56759ce95aceb49d2b3a56b49ce94a527295272a4a7195252a4e739ca739d2529ca739ce538ce5194e51
def b306 : ℕ := 0x129465184210ad274ad2729ce939ce529ce729ca729ce3294a328c630ad6f6b56b4b5695a5ad4adab6ad2d5a4eb59d2b4a56b3a4e74a4e949ce94a4e929ce72a52939ce749d273a4a7394e7394a7194e31
def w123 := mergeW 0 w9 w30
def b307 : ℕ := 0x128465184210ad2729ca729ce539ce528ce728c2729ce12942328c630ad6b4b56b4b5675a5294ad2749ca93a4ab394ab4a56b394674a4e529ce52a4e519ce71a4a539ce729d2719427394e7394a7084e30
def w124 := mergeW 0 w6 w30
def b308 : ℕ := 0x1294611842109d2749d2728ce939ce529ce329ca328c61294a308c630ad6b6a56b4a4e75a5a949d2b4ad29394ab595272a4e73a4e72a4e949c69494e919c631a52939ce749ca7394a719463394a3094630
def b309 : ℕ := 0x1094651842109ca34ad2719c6518ce529ce729ca729ce3094a328c6309ceb4a4e73a4e559dad3adab6aced59ca739d2b494e7194632a4e949ce94a4e929ce7294a518c6349d273a4a7394e7394a7194e11
def b310 : ℕ := 0x11942528c210a5273ad672a4a728ca739ca739ce739527194a328ca11ad6d6ad693b56b5a56d4b5ad5ad2f6a5274ad6959d29394e729d275a5295a4e749d2749ce728ce349d293a4e539ca929ce939ca33
def w125 := mergeW 0 w6 w34
def b311 : ℕ := 0x11942128c210952739d67294a7284a739ca339ce3384a7194a308ca11ad6969d672a4eb5a5694a52d3ad2b495254ad6539ca538ce719d275a4a9594e749ca329ce7284e149ca9394e519c2529ce539c233
def w126 := mergeW 0 w9 w34
def b312 : ℕ := 0x11842528c210a52719ce72a4a3284a738ca738c67395271942328ca11ad694ad672b56b5a4e94b52939cab4a5252ace959d2938c6719d233a5253a4e329d2749c63284e129d291946539ca929ce938ca33
def b313 : ℕ := 0x11942508c210a4a73ace31a4a728ca339ca739ce7194a3194a328c2119d6d4ace52a56739d6d3b5a959ceb69ce749d6939d29394e729d27395293a46728d2329ce728c6349d253a4e539ca528ce519ca11
def b314 : ℕ := 0x12942328c210a5693a56729ce9394a739ca539ce538ce7294a318ca11b5ad7adab4b56d5a56b4ad6d4ad2d59d295ad674a52949d2929d275a4e959ce749ce53a5293952549ce939ce529c6729ce739c633
def w127 := mergeW 0 w25 w0
def b315 : ℕ := 0x10942328c21094e53a56729c65184a739ca539ce5384e7094a318ca11a52959d272a4e95a56b4ad6d3ad2d595253ad65494a528ca519d275a4e959ce749ce3394a5184a149ce939ce529c2729ce739c233
def w128 := mergeW 0 w25 w3
def b316 : ℕ := 0x12942308c210a4e93a4e329ce9394a339ca539ce518463294a318c211a5ad5ad274a5693a56b4ad6939d29594a959d652a52949d2919d27394e939c6728ce31a529394a549ce539ce529c2328ce319c231
def b317 : ℕ := 0x12842328c210a569194e719ce5394a738ca538c6538ce72942318ca11b5a95adab3b56d59ce73ace929ce9394e93ace74a52948ca929d233a4e539ce329ce53a4a53952529ce918c6529c6729ce738c613
def b318 : ℕ := 0x128c65284210ad673a52929ce739ce7294e72946739d252946328ca30b56d6b5ad4bd6b6a56b4ad6b5aced4a52b4a4eb5a56b39ca74a4e74a4e74a5272a4e93a4e739d2739d2929c67394e939ca928ce32
def w129 := mergeW 0 w20 w3
def b319 : ℕ := 0x128c65084210ace73a4a529ce739ce3294e72942719ca12946328c230a56d4b5294ad674a56b4ad6759ca93a4ab494ab3a56b39c674a4e7294e72a4a7194e51a4e739ca739d2529c27394e538ca5084e30
def w130 := mergeW 0 w20 w0
def b320 : ℕ := 0x108c652842109ce33a52929c6318ce7294e72942739d250946328ca30a4e94a5292ace76a56b4ad6b5acad3a5272a4ab594e718c632a4e74a4e74a5271a4e93946318ca339d2929c27394e939ca9284e32
def b321 : ℕ := 0x128c612842109d673952918ce739ce7294e32946338ca52946308ca30b5696a5ad3aceb69d6739ceb3aca929ceb4a4e73a4e739ca72a4e74a467495272a4651a4e739d2739ca928c671946539ca528c612
def b322 : ℕ := 0x10946508c2109ce54ace53a46518ce339ce739ce719ca3094a328c231a52b5a5293ad294adad5b5a96a56b6ace739d6b394e7294a52a529395293a4a929525294a518ca349d253a4e739ce538ce519ce51
def w131 := mergeW 1 w47 w2
def w132 := mergeW 1 w6 w47
def w133 := mergeW 1 w9 w47
def w134 := mergeW 1 w5 w47
def w135 := mergeW 1 w8 w47
def b323 : ℕ := 0x12846128c2109d6929ce9394e539ce738ce338c6338ca72942308ca31b5ab5a5ad5ad2d6ad295a5294a4eb49d6b3ace73a4e7494a92a5253a4a5395252a4a52a4a539d2729ca91946719c6539ce538c653
def w136 := mergeW 1 w44 w2
def w137 := mergeW 1 w44 w0
def w138 := mergeW 1 w44 w3
def w139 := mergeW 1 w44 w5
def w140 := mergeW 1 w44 w8
def b324 : ℕ := 0x10946528c2109ce54ad692a46518ce739ce739ce739d27094a328ca31a52b5a5294ad296a5ad4b5ad6b52f6a5273ad6b594e7294a52a5295a5295a5294a529494a518ca349d293a4e739ce939ce939ce33
def w141 := mergeW 1 w6 w73
def b325 : ℕ := 0x10946328c21094e54a56929c6518ce739ce539ce5394e7094a318ca31a52959d294a4e96a5ab4ad6d5b52d59d273ad69494a5294a51a5295a4e959d294a4e7394a518ca349ce939ce729ca739ce739ca33
def w142 := mergeW 1 w73 w3
def b326 : ℕ := 0x10946518c2109ca54ad272a46518ce539ce739ce729ce5094a328c6319d2b4a4e74a5275a5ad4b5ab6ad2d6a4e73a56b494e7294a52a52949d294a4e939d27394a518c6349d273a4e739ce7394e729ce32
def w143 := mergeW 1 w9 w73
def b327 : ℕ := 0x108c6528c2109ce53a5292a46318ce7394e7394a739d270946328ca31a5294a5294ad296a56b4b56b5aced5a5272ad2b594e728c652a5274a5274a5273a5294946318ca339d2929ca739ce939ce9394e33
def b328 : ℕ := 0x12946508c210ace94ace52a4e939ce339ce739ce719ca3294a328c231a5af5b5294ada94a5ad4b5a96a52b6a52b59d6b3a56b4a5294a529395293a4a9295252a52939ca749d253a4e739ce538ce519ce31
def w144 := mergeW 1 w9 w67
def b329 : ℕ := 0x128c6508c210ace93a4a52a4e739ce3394e7394a719ca32946328c231a5ad4b5294ada94a56b4b56759ce95a52b49d2b3a56b49ce94a527295272a4a7195252a4e739ca739d2529ca739ce538ce5194e31
def w145 := mergeW 1 w67 w0
def b330 : ℕ := 0x11946508c210a4a74ace52a4a7294e339ce739ce719ca3194a328c2319d6d4ace73a5674a5ad4b5a96a52b6a52949d6b39d2939ce73a529395293a4a92952529ce72946549d253a4e739ce538ce519ce31
def w146 := mergeW 1 w67 w6
def b331 : ℕ := 0x12946308c210a4e94a4e529ce939ce339ce539ce519463294a318c231a5ad5ad294a5694a5ab4ad695a52959d2b59d692a5294a5293a529394e939ca9294e31a52939ca749ce539ce729ca338ce319ca31
def b332 : ℕ := 0x12946128c2109d6949d69294e939ce739ce339ce338ca7294a308ca31b5ab7a5ad4ad2d6a5a94a52d4b52b4a52b5ad673a4e74a5292a5295a4a9595294a4a52a52939d2749ca9394e719c6539ce539c633
def w147 := mergeW 1 w74 w0
def b333 : ℕ := 0x11946128c210952749d69294a7294e739ce339ce338ca7194a308ca31ad6969d6b3a4eb6a5a94a52d4b52b4a5294ad6739ca539ce71a5295a4a9595294a4a529ce7294e549ca9394e719c6539ce539c633
def w148 := mergeW 1 w9 w74
def b334 : ℕ := 0x128c6128c2109d6939529294e739ce7394e3394a338ca72946308ca31b5a96a5ad4ad2d6a5674a4eb3ace93a52b4ad273a4e749ce92a5274a4a7495273a4a52a4e739d2739ca928ca719c6539ce5394633
def w149 := mergeW 1 w74 w3
def b335 : ℕ := 0x12946118c2109d2949d27294e939ce539ce339ce328c65294a308c631adab6a56b4a52b5a5a94a52b4ad294a4eb5a5672a4e74a5292a52949ca9494e939ca31a52939ce749ca7394e719c63394e329c632
def b336 : ℕ := 0x12846528c210ad6929ce92a4e539ce738ce738c6739d272942328ca31b5ab5b5ad4bdad6a5294b5294a52b4a52b3aceb5a56b494a94a5253a5253a5252a5294a4a539d2729d291946739ce939ce938ce33
def w150 := mergeW 1 w68 w3
def b337 : ℕ := 0x12846518c210ad2929ca72a4e539ce538ce738c6729ce52942328c631adab4b56b4b5ab5a5294b52749d294a4eb3a4eb4a56b494a94a52529d252a4e519d273a4a539ce729d271946739ce7394e728ce32
def w151 := mergeW 1 w68 w6
def b338 : ℕ := 0x12846328c210a569294e929ce539ce738ce538c65394e72942318ca31b5a95adad4b56d6a5274ace93a52939d2b3ace94a529494a93a5253a4e539d252a4e73a4a539d2729ce918c6729ca739ce738ca33
def w152 := mergeW 1 w68 w0
def b339 : ℕ := 0x11846528c210a52729ce92a4a3294e738ce738c6739d271942328ca31ad694ad6b3b56b6a5294b5294a52b4a5292aceb59d2938c673a5253a5253a5252a52949c63294e529d291946739ce939ce938ce33
def b340 : ℕ := 0x11946528c210a5274ad692a4a7294e739ce739ce739d27194a328ca31ad6d6ad6b3b56b6a5ad4b5ad6b52f6a5294ad6b59d2939ce73a5295a5295a5294a52949ce7294e549d293a4e739ce939ce939ce33
def b341 : ℕ := 0x11846528c210a52729ce92a4a3294e738ce738c6739d271942328ca31ad694ad6b2b56b6a5294b5294a4ab4a5292aceb59d2938c673a5253a5253a5252a52949c63294e529d291946739ce939ce938ce33
def b342 : ℕ := 0x11946128c210952749d69294a7294e739ce339ce338ca7194a308ca31ad6969d6b2a4eb6a5a94a52d4b52b495294ad6739ca539ce71a5295a4a9595294a4a529ce7294e549ca9394e719c6539ce539c633
def b343 : ℕ := 0x11946508c210a4a74ace52a4a7294e339ce739ce719ca3194a328c2319d6d4ace72a5674a5ad4b5a96a52b6a4a949d6b39d2939ce73a529395293a4a92952529ce72946549d253a4e739ce538ce519ce31
def b344 : ℕ := 0x12946518c210ad294ad272a4e939ce539ce739ce729ce5294a328c631adaf6b56b4b5ab5a5ad4b5ab6ad2d6a4eb5a56b4a56b4a5294a52949d294a4e939d273a52939ce749d273a4e739ce7394e729ce32
def b345 : ℕ := 0x12946118c2109d2949d27294e939ce539ce339ce328c65294a308c631adab6a56b4a52b5a5a94a52b4ad29494ab5a5672a4e74a5292a52949ca9494e939ca31a52939ce749ca7394e719c63394e329c632
def b346 : ℕ := 0x12846518c210ad2929ca72a4e539ce538ce738c6729ce52942328c631adab4b56b4b5ab5a5294b52749ca94a4ab3a4eb4a56b494a94a52529d252a4e519d273a4a539ce729d271946739ce7394e728ce32
def b347 : ℕ := 0x10946518c2109ca54ad272a46518ce539ce739ce729ce5094a328c6319d2b4a4e72a5275a5ad4b5ab6ad2d6a4a73a56b494e7294a52a52949d294a4e939d27394a518c6349d273a4e739ce7394e729ce32
def b348 : ℕ := 0x12946328c210a5694a56929ce939ce739ce539ce5394e7294a318ca31b5ad7adad4b56d6a5ab4ad6d5b52d59d2b5ad694a5294a5293a5295a4e959d294a4e73a52939d2749ce939ce729ca739ce739ca33
def b349 : ℕ := 0x12946308c210a4e94a4e529ce939ce339ce539ce519463294a318c231a5ad5ad294a5694a5ab4ad695a529594ab59d692a5294a5293a529394e939ca9294e31a52939ca749ce539ce729ca338ce319ca31
def b350 : ℕ := 0x10946328c21094e54a56929c6518ce739ce539ce5394e7094a318ca31a52959d292a4e96a5ab4ad6d5b52d595273ad69494a5294a51a5295a4e959d294a4e7394a518ca349ce939ce729ca739ce739ca33
def b351 : ℕ := 0x12846328c210a569294e929ce539ce738ce538c65394e72942318ca31b5a95adad4b56d6a5274ace93a4a93952b3ace94a529494a93a5253a4e539d252a4e73a4a539d2729ce918c6729ca739ce738ca33
def b352 : ℕ := 0x128c6528c210ad693a5292a4e739ce7394e7394a739d272946328ca31b5ad6b5ad4bdad6a56b4b56b5aced5a52b4ad2b5a56b49ce94a5274a5274a5273a5294a4e739d2739d2929ca739ce939ce9394e33
def b353 : ℕ := 0x108c6528c2109ce53a5292a46318ce7394e7394a739d270946328ca31a5294a5292ad296a56b4b56b5acad5a5272ad2b594e728c652a5274a5274a5273a5294946318ca339d2929ca739ce939ce9394e33
def b354 : ℕ := 0x128c6508c210ace93a4a52a4e739ce3394e7394a719ca32946328c231a5ad4b5294ada94a56b4b56759ca95a4ab49d2b3a56b49ce94a527295272a4a7195252a4e739ca739d2529ca739ce538ce5194e31
def b355 : ℕ := 0x128c6128c2109d6939529294e739ce7394e3394a338ca72946308ca31b5a96a5ad4ad2d6a5674a4eb3aca93952b4ad273a4e749ce92a5274a4a7495273a4a52a4e739d2739ca928ca719c6539ce5394633
def b356 : ℕ := 0x10946128c2109ce549d693946518ce739ce339ce338ca7094a308ca31a52b5a5293ad296ada95a52d4b56b49d673ad67394e7294a52a5295a4a9595294a4a5294a518ca349ca9394e719c6539ce539c653
def w153 := mergeW 1 w60 w5
def b357 : ℕ := 0x1094612842109ce349d6928c6518ce729ce329ca338ca5094a308ca30a4eb5a5292ace76a5a949d2d4b52b395273a527394e7194632a4e95a469595293a465194a518ca349ca9394a71946539ca5294632
def w154 := mergeW 0 w9 w3
def b358 : ℕ := 0x12846508c210ace929ce53a4e539ce338ce738c6719ca32942328c231a5ab5b5295ada94ad295b5294a4eb4aceb39ceb3a56b494a94a525395253a4a5295252a4a539ca729d251946739ce538ce518ce51
def w155 := mergeW 1 w154 w8
def b359 : ℕ := 0x12842508c210ace919ce32a4e5394a338ca738c67194a32942328c211a5ab5b5274ada93a4e94b52939cab4a4a939ce93a56b48ca939d23395253a46328d232a4a5394a529d251946539ca528ce518ca31
def b360 : ℕ := 0x10946528c2109ce54ad691a46518ce739ce739ce739d27094a328ca31a52b5a5293ad2969dad3b5ad6b4ef69ce73ad6b594e7294a52a5295a5295a5294a529494a518ca349d293a4e739ce939ce939ce13
def b361 : ℕ := 0x12946508c210ace94ace51a4e939ce339ce739ce719ca3294a328c231a5af5b5293ada949dad3b5a96a4eb69ceb59d6b3a56b4a5294a529395293a4a9295252a52939ca749d253a4e739ce538ce519ce11
def b362 : ℕ := 0x12946128c2109d6949d69194e939ce739ce339ce338ca7294a308ca31b5ab7a5ad3ad2d69da93a52d4b4eb49ceb5ad673a4e74a5292a5295a4a9595294a4a52a52939d2749ca9394e719c6539ce539c613
def s0 : Snap := (b0, [w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s1 : Snap := (b1, [w10, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s2 : Snap := (b2, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w11])
def s3 : Snap := (b3, [w10, w12, w1, w2, w3, w5, w6, w7, w8, w9])
def s4 : Snap := (b4, [w10, w0, w1, w2, w3, w4, w6, w7, w8, w9])
def s5 : Snap := (b5, [w10, w0, w1, w2, w3, w5, w6, w7, w13, w8, w9])
def s6 : Snap := (b6, [w10, w0, w1, w2, w14, w3, w5, w6, w7, w8, w9])
def s7 : Snap := (b7, [w10, w0, w1, w2, w3, w5, w15, w6, w7, w8, w9])
def s8 : Snap := (b8, [w16, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s9 : Snap := (b9, [w10, w0, w1, w2, w17, w3, w5, w6, w7, w8, w9])
def s10 : Snap := (b10, [w10, w0, w1, w2, w3, w5, w6, w7, w8, w9, w11])
def s11 : Snap := (b11, [w10, w0, w1, w2, w3, w5, w6, w7, w8, w9, w18])
def s12 : Snap := (b12, [w10, w19, w1, w2, w3, w5, w6, w7, w8, w9])
def s13 : Snap := (b12, [w10, w0, w1, w2, w3, w20, w6, w7, w8, w9])
def s14 : Snap := (b13, [w10, w21, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s15 : Snap := (b14, [w10, w12, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s16 : Snap := (b4, [w22, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s17 : Snap := (b15, [w0, w1, w2, w3, w23, w5, w6, w7, w8, w9])
def s18 : Snap := (b3, [w24, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s19 : Snap := (b16, [w10, w0, w1, w2, w3, w5, w25, w6, w7, w8, w9])
def s20 : Snap := (b17, [w0, w1, w2, w3, w26, w5, w6, w7, w8, w9])
def s21 : Snap := (b18, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w27])
def s22 : Snap := (b19, [w0, w1, w2, w3, w26, w5, w15, w7, w8, w9])
def s23 : Snap := (b20, [w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s24 : Snap := (b21, [w0, w1, w2, w17, w3, w26, w5, w6, w7, w8, w9])
def s25 : Snap := (b22, [w0, w1, w2, w14, w3, w26, w5, w6, w7, w8, w9])
def s26 : Snap := (b23, [w12, w0, w1, w2, w3, w26, w5, w6, w7, w8, w9])
def s27 : Snap := (b24, [w0, w1, w2, w3, w26, w5, w6, w7, w13, w8, w9])
def s28 : Snap := (b25, [w0, w1, w2, w3, w26, w5, w6, w7, w8, w9, w27])
def s29 : Snap := (b26, [w0, w1, w2, w3, w26, w5, w6, w7, w8, w9, w28])
def s30 : Snap := (b27, [w0, w1, w2, w29, w3, w26, w5, w7, w8, w9])
def s31 : Snap := (b27, [w0, w1, w2, w30, w3, w26, w6, w7, w8, w9])
def s32 : Snap := (b28, [w21, w0, w1, w2, w3, w26, w5, w6, w7, w8, w9])
def s33 : Snap := (b29, [w0, w1, w2, w3, w26, w5, w15, w6, w7, w8, w9])
def s34 : Snap := (b20, [w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s35 : Snap := (b30, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w32])
def s36 : Snap := (b19, [w0, w1, w2, w3, w33, w5, w6, w7, w8, w9])
def s37 : Snap := (b16, [w34, w0, w1, w2, w3, w26, w5, w6, w7, w8, w9])
def s38 : Snap := (b31, [w0, w1, w2, w17, w3, w5, w6, w7, w8, w9])
def s39 : Snap := (b32, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w35])
def s40 : Snap := (b33, [w12, w0, w1, w2, w17, w5, w6, w7, w8, w9])
def s41 : Snap := (b34, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w9])
def s42 : Snap := (b35, [w21, w0, w1, w2, w17, w3, w5, w6, w7, w8, w9])
def s43 : Snap := (b36, [w0, w1, w2, w17, w3, w5, w15, w6, w7, w8, w9])
def s44 : Snap := (b37, [w0, w1, w2, w36, w3, w5, w6, w7, w8, w9])
def s45 : Snap := (b38, [w0, w1, w2, w17, w3, w5, w6, w7, w8, w9, w35])
def s46 : Snap := (b39, [w0, w1, w2, w17, w3, w5, w6, w7, w8, w9, w28])
def s47 : Snap := (b40, [w0, w1, w2, w29, w17, w5, w6, w7, w8, w9])
def s48 : Snap := (b40, [w0, w1, w2, w17, w3, w5, w25, w6, w7, w9])
def s49 : Snap := (b41, [w0, w1, w2, w17, w14, w3, w5, w6, w7, w8, w9])
def s50 : Snap := (b42, [w12, w0, w1, w2, w17, w3, w5, w6, w7, w8, w9])
def s51 : Snap := (b34, [w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s52 : Snap := (b43, [w0, w1, w2, w3, w38, w5, w6, w7, w8, w9])
def s53 : Snap := (b33, [w39, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s54 : Snap := (b44, [w0, w1, w2, w17, w3, w20, w5, w6, w7, w8, w9])
def s55 : Snap := (b45, [w0, w1, w2, w3, w5, w6, w7, w13, w8, w9])
def s56 : Snap := (b46, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w40])
def s57 : Snap := (b47, [w0, w1, w2, w3, w5, w15, w6, w7, w13, w8])
def s58 : Snap := (b48, [w0, w1, w2, w3, w4, w5, w6, w7, w13, w9])
def s59 : Snap := (b49, [w21, w0, w1, w2, w3, w5, w6, w7, w13, w8, w9])
def s60 : Snap := (b50, [w12, w0, w1, w2, w3, w5, w6, w7, w13, w8, w9])
def s61 : Snap := (b51, [w0, w1, w2, w3, w5, w6, w7, w13, w8, w9, w40])
def s62 : Snap := (b52, [w0, w1, w2, w3, w5, w6, w7, w13, w8, w9, w18])
def s63 : Snap := (b53, [w19, w0, w1, w2, w3, w5, w6, w7, w13, w8])
def s64 : Snap := (b53, [w34, w0, w1, w2, w3, w5, w6, w7, w13, w9])
def s65 : Snap := (b54, [w0, w1, w2, w14, w3, w5, w6, w7, w13, w8, w9])
def s66 : Snap := (b55, [w0, w1, w2, w3, w5, w15, w6, w7, w13, w8, w9])
def s67 : Snap := (b48, [w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s68 : Snap := (b56, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w42])
def s69 : Snap := (b47, [w0, w1, w2, w3, w5, w43, w6, w7, w8, w9])
def s70 : Snap := (b44, [w0, w1, w2, w30, w3, w5, w6, w7, w13, w8, w9])
def s71 : Snap := (b57, [w12, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s72 : Snap := (b58, [w12, w21, w1, w2, w3, w5, w6, w7, w8, w9])
def s73 : Snap := (b59, [w12, w0, w1, w2, w14, w5, w6, w7, w8, w9])
def s74 : Snap := (b60, [w12, w0, w1, w2, w3, w5, w15, w6, w7, w8, w9])
def s75 : Snap := (b9, [w12, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s76 : Snap := (b35, [w12, w0, w1, w2, w3, w5, w25, w6, w7, w8, w9])
def s77 : Snap := (b6, [w12, w0, w1, w2, w3, w20, w5, w6, w7, w8, w9])
def s78 : Snap := (b61, [w12, w21, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s79 : Snap := (b62, [w12, w0, w1, w2, w14, w3, w5, w6, w7, w8, w9])
def s80 : Snap := (b63, [w12, w0, w1, w2, w3, w5, w6, w7, w8, w9, w44])
def s81 : Snap := (b58, [w45, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s82 : Snap := (b59, [w46, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s83 : Snap := (b64, [w0, w1, w2, w3, w5, w15, w6, w7, w8, w9])
def s84 : Snap := (b65, [w21, w0, w1, w2, w3, w5, w15, w7, w8, w9])
def s85 : Snap := (b66, [w0, w1, w2, w14, w3, w5, w15, w6, w7, w8])
def s86 : Snap := (b24, [w0, w1, w2, w3, w4, w5, w15, w6, w7, w8, w9])
def s87 : Snap := (b22, [w0, w1, w2, w30, w3, w5, w15, w6, w7, w8, w9])
def s88 : Snap := (b49, [w34, w0, w1, w2, w3, w5, w15, w6, w7, w8, w9])
def s89 : Snap := (b67, [w21, w0, w1, w2, w3, w5, w15, w6, w7, w8, w9])
def s90 : Snap := (b68, [w0, w1, w2, w14, w3, w5, w15, w6, w7, w8, w9])
def s91 : Snap := (b69, [w0, w1, w2, w3, w47, w5, w15, w6, w7, w8, w9])
def s92 : Snap := (b65, [w48, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s93 : Snap := (b66, [w0, w1, w2, w49, w3, w5, w6, w7, w8, w9])
def s94 : Snap := (b70, [w21, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s95 : Snap := (b60, [w21, w0, w1, w2, w14, w3, w5, w6, w7, w8, w9])
def s96 : Snap := (b16, [w21, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s97 : Snap := (b71, [w0, w1, w2, w3, w50, w5, w6, w7, w8, w9])
def s98 : Snap := (b72, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w51])
def s99 : Snap := (b73, [w34, w21, w1, w2, w3, w5, w6, w7, w8, w9])
def s100 : Snap := (b73, [w21, w0, w1, w2, w3, w5, w25, w7, w8, w9])
def s101 : Snap := (b23, [w21, w0, w1, w2, w30, w3, w5, w6, w7, w8, w9])
def s102 : Snap := (b74, [w0, w1, w2, w14, w3, w5, w6, w7, w8, w9])
def s103 : Snap := (b44, [w0, w1, w2, w14, w3, w4, w5, w6, w7, w8, w9])
def s104 : Snap := (b75, [w0, w1, w2, w3, w52, w5, w6, w7, w8, w9])
def s105 : Snap := (b76, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w53])
def s106 : Snap := (b77, [w0, w1, w2, w30, w14, w5, w6, w7, w8, w9])
def s107 : Snap := (b77, [w0, w1, w2, w14, w3, w20, w5, w6, w7, w8])
def s108 : Snap := (b50, [w34, w0, w1, w2, w14, w3, w5, w6, w7, w8, w9])
def s109 : Snap := (b78, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s110 : Snap := (b79, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w18])
def s111 : Snap := (b80, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w28])
def s112 : Snap := (b21, [w0, w1, w2, w29, w3, w4, w5, w6, w7, w8, w9])
def s113 : Snap := (b81, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w18])
def s114 : Snap := (b82, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w28, w18])
def s115 : Snap := (b83, [w54, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s116 : Snap := (b84, [w0, w1, w2, w3, w5, w6, w7, w8, w55, w9])
def s117 : Snap := (b85, [w19, w0, w1, w2, w3, w5, w6, w7, w8, w9, w18])
def s118 : Snap := (b86, [w34, w0, w1, w2, w3, w5, w6, w7, w8, w9, w18])
def s119 : Snap := (b87, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w28])
def s120 : Snap := (b88, [w0, w1, w2, w56, w3, w5, w6, w7, w8, w9])
def s121 : Snap := (b89, [w0, w1, w2, w3, w5, w57, w6, w7, w8, w9])
def s122 : Snap := (b90, [w0, w1, w2, w29, w3, w5, w6, w7, w8, w9, w28])
def s123 : Snap := (b91, [w0, w1, w2, w30, w3, w5, w6, w7, w8, w9, w28])
def s124 : Snap := (b92, [w0, w1, w2, w29, w3, w5, w6, w7, w8, w9])
def s125 : Snap := (b23, [w10, w0, w1, w2, w29, w3, w5, w6, w7, w8, w9])
def s126 : Snap := (b36, [w0, w1, w2, w29, w3, w5, w6, w7, w13, w8, w9])
def s127 : Snap := (b93, [w21, w0, w1, w2, w29, w3, w5, w6, w7, w8, w9])
def s128 : Snap := (b94, [w0, w1, w2, w29, w14, w3, w5, w6, w7, w8, w9])
def s129 : Snap := (b60, [w19, w0, w1, w2, w29, w3, w5, w6, w7, w8, w9])
def s130 : Snap := (b95, [w12, w0, w1, w2, w29, w3, w5, w6, w7, w8, w9])
def s131 : Snap := (b96, [w19, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s132 : Snap := (b5, [w19, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s133 : Snap := (b7, [w19, w0, w1, w2, w3, w26, w5, w6, w7, w8, w9])
def s134 : Snap := (b50, [w19, w0, w1, w2, w17, w3, w5, w6, w7, w8, w9])
def s135 : Snap := (b97, [w19, w21, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s136 : Snap := (b98, [w19, w0, w1, w2, w14, w3, w5, w6, w7, w8, w9])
def s137 : Snap := (b99, [w12, w19, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s138 : Snap := (b100, [w0, w1, w2, w30, w3, w5, w6, w7, w8, w9])
def s139 : Snap := (b9, [w34, w0, w1, w2, w30, w3, w5, w6, w7, w8, w9])
def s140 : Snap := (b101, [w34, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s141 : Snap := (b102, [w0, w1, w2, w3, w5, w25, w6, w7, w8, w9])
def s142 : Snap := (b103, [w0, w1, w2, w3, w5, w25, w6, w7, w8, w9, w28])
def s143 : Snap := (b36, [w0, w1, w2, w14, w3, w5, w25, w6, w7, w8, w9])
def s144 : Snap := (b24, [w0, w1, w2, w3, w20, w5, w25, w6, w7, w8, w9])
def s145 : Snap := (b104, [w0, w1, w2, w3, w20, w5, w6, w7, w8, w9])
def s146 : Snap := (b105, [w0, w1, w2, w3, w20, w5, w6, w7, w8, w9, w18])
def s147 : Snap := (b7, [w21, w0, w1, w2, w3, w20, w5, w6, w7, w8, w9])
def s148 : Snap := (b106, [w0, w1, w2, w3, w47, w5, w6, w7, w8, w9])
def s149 : Snap := (b106, [w0, w58, w2, w3, w5, w6, w7, w8, w9])
def s150 : Snap := (b107, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w44])
def s151 : Snap := (b107, [w0, w1, w2, w3, w5, w6, w59, w8, w9])
def s152 : Snap := (b108, [w0, w1, w2, w3, w5, w6, w60, w7, w8, w9])
def s153 : Snap := (b109, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s154 : Snap := (b110, [w10, w0, w1, w2, w3, w4, w6, w7, w8, w9])
def s155 : Snap := (b111, [w10, w12, w1, w2, w3, w4, w6, w7, w8, w9])
def s156 : Snap := (b111, [w10, w0, w1, w2, w17, w3, w4, w6, w7, w9])
def s157 : Snap := (b112, [w10, w0, w1, w2, w3, w4, w6, w7, w13, w9])
def s158 : Snap := (b113, [w10, w0, w1, w2, w3, w4, w6, w7, w8, w9, w11])
def s159 : Snap := (b114, [w10, w0, w1, w2, w14, w3, w4, w6, w7, w8, w9])
def s160 : Snap := (b115, [w16, w0, w1, w2, w3, w4, w6, w7, w8, w9])
def s161 : Snap := (b112, [w10, w19, w1, w2, w3, w4, w6, w7, w8, w9])
def s162 : Snap := (b116, [w10, w0, w1, w2, w3, w4, w6, w7, w8, w9, w18])
def s163 : Snap := (b117, [w10, w0, w1, w2, w3, w61, w6, w7, w8, w9])
def s164 : Snap := (b118, [w10, w0, w1, w2, w3, w4, w15, w6, w7, w8, w9])
def s165 : Snap := (b119, [w0, w1, w2, w3, w61, w6, w7, w8, w9])
def s166 : Snap := (b120, [w10, w21, w0, w1, w2, w3, w4, w6, w7, w8, w9])
def s167 : Snap := (b121, [w16, w10, w0, w1, w2, w3, w4, w6, w7, w8, w9])
def s168 : Snap := (b122, [w10, w0, w1, w2, w3, w23, w4, w6, w7, w8, w9])
def s169 : Snap := (b112, [w10, w0, w1, w2, w3, w41, w6, w7, w8, w9])
def s170 : Snap := (b123, [w10, w0, w1, w2, w3, w4, w6, w7, w13, w8, w9])
def s171 : Snap := (b124, [w10, w0, w1, w2, w3, w4, w6, w7, w8, w9, w44])
def s172 : Snap := (b125, [w10, w0, w1, w2, w17, w3, w4, w6, w7, w8, w9])
def s173 : Snap := (b126, [w10, w12, w0, w1, w2, w3, w4, w6, w7, w8, w9])
def s174 : Snap := (b127, [w0, w1, w2, w3, w4, w61, w6, w7, w8, w9])
def s175 : Snap := (b128, [w10, w0, w1, w2, w3, w41, w4, w6, w7, w8, w9])
def s176 : Snap := (b129, [w10, w0, w1, w2, w3, w31, w4, w6, w7, w8, w9])
def s177 : Snap := (b130, [w10, w19, w0, w1, w2, w3, w4, w6, w7, w8, w9])
def s178 : Snap := (b131, [w10, w0, w1, w2, w29, w3, w4, w6, w7, w8, w9])
def s179 : Snap := (b132, [w10, w0, w1, w2, w37, w3, w4, w6, w7, w8, w9])
def s180 : Snap := (b133, [w10, w0, w1, w2, w3, w4, w61, w6, w7, w8, w9])
def s181 : Snap := (b134, [w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s182 : Snap := (b135, [w0, w1, w2, w3, w26, w4, w15, w7, w8, w9])
def s183 : Snap := (b135, [w0, w1, w2, w3, w26, w4, w6, w7, w13, w9])
def s184 : Snap := (b136, [w0, w1, w2, w17, w3, w26, w4, w6, w7, w9])
def s185 : Snap := (b137, [w0, w1, w2, w3, w26, w4, w6, w7, w8, w9, w27])
def s186 : Snap := (b138, [w0, w1, w2, w14, w3, w26, w4, w6, w7, w8, w9])
def s187 : Snap := (b136, [w0, w1, w2, w29, w3, w26, w4, w7, w8, w9])
def s188 : Snap := (b139, [w0, w1, w2, w3, w26, w4, w6, w7, w8, w9, w28])
def s189 : Snap := (b140, [w0, w1, w2, w3, w26, w62, w6, w7, w8, w9])
def s190 : Snap := (b131, [w12, w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s191 : Snap := (b141, [w0, w1, w2, w3, w62, w6, w7, w8, w9])
def s192 : Snap := (b142, [w21, w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s193 : Snap := (b143, [w16, w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s194 : Snap := (b144, [w0, w1, w2, w3, w26, w4, w6, w7, w8, w9, w32])
def s195 : Snap := (b136, [w0, w1, w2, w37, w3, w26, w6, w7, w8, w9])
def s196 : Snap := (b145, [w0, w1, w2, w17, w3, w26, w4, w6, w7, w8, w9])
def s197 : Snap := (b146, [w0, w1, w2, w3, w47, w26, w4, w6, w7, w8, w9])
def s198 : Snap := (b147, [w0, w1, w2, w3, w26, w4, w6, w7, w13, w8, w9])
def s199 : Snap := (b148, [w0, w1, w2, w3, w26, w4, w15, w6, w7, w8, w9])
def s200 : Snap := (b149, [w0, w1, w2, w3, w4, w62, w6, w7, w8, w9])
def s201 : Snap := (b150, [w0, w1, w2, w37, w3, w26, w4, w6, w7, w8, w9])
def s202 : Snap := (b129, [w22, w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s203 : Snap := (b151, [w0, w1, w2, w29, w3, w26, w4, w6, w7, w8, w9])
def s204 : Snap := (b118, [w19, w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s205 : Snap := (b152, [w0, w1, w2, w3, w26, w41, w4, w6, w7, w8, w9])
def s206 : Snap := (b153, [w0, w1, w2, w3, w26, w4, w62, w6, w7, w8, w9])
def s207 : Snap := (b154, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w9])
def s208 : Snap := (b111, [w12, w0, w1, w2, w17, w4, w5, w6, w7, w9])
def s209 : Snap := (b155, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w9, w35])
def s210 : Snap := (b131, [w21, w0, w1, w2, w17, w3, w4, w5, w6, w7, w9])
def s211 : Snap := (b156, [w0, w1, w2, w36, w3, w4, w5, w6, w7, w9])
def s212 : Snap := (b136, [w0, w1, w2, w29, w17, w4, w5, w6, w7, w9])
def s213 : Snap := (b157, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w9, w28])
def s214 : Snap := (b158, [w0, w1, w2, w17, w3, w5, w6, w7, w63, w9])
def s215 : Snap := (b138, [w0, w1, w2, w17, w3, w4, w5, w15, w6, w7, w9])
def s216 : Snap := (b159, [w0, w1, w2, w3, w5, w6, w7, w63, w9])
def s217 : Snap := (b160, [w0, w1, w2, w17, w14, w3, w4, w5, w6, w7, w9])
def s218 : Snap := (b161, [w0, w1, w2, w36, w17, w3, w4, w5, w6, w7, w9])
def s219 : Snap := (b162, [w0, w1, w2, w17, w3, w38, w4, w5, w6, w7, w9])
def s220 : Snap := (b136, [w0, w1, w2, w17, w3, w31, w5, w6, w7, w9])
def s221 : Snap := (b163, [w0, w1, w2, w17, w3, w26, w4, w5, w6, w7, w9])
def s222 : Snap := (b164, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w9, w44])
def s223 : Snap := (b165, [w10, w0, w1, w2, w17, w3, w4, w5, w6, w7, w9])
def s224 : Snap := (b166, [w12, w0, w1, w2, w17, w3, w4, w5, w6, w7, w9])
def s225 : Snap := (b167, [w0, w1, w2, w3, w4, w5, w6, w7, w63, w9])
def s226 : Snap := (b150, [w0, w1, w2, w17, w3, w31, w4, w5, w6, w7, w9])
def s227 : Snap := (b168, [w0, w1, w2, w17, w3, w41, w4, w5, w6, w7, w9])
def s228 : Snap := (b169, [w0, w1, w2, w29, w17, w3, w4, w5, w6, w7, w9])
def s229 : Snap := (b114, [w19, w0, w1, w2, w17, w3, w4, w5, w6, w7, w9])
def s230 : Snap := (b132, [w22, w0, w1, w2, w17, w3, w4, w5, w6, w7, w9])
def s231 : Snap := (b170, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w63, w9])
def s232 : Snap := (b171, [w0, w1, w2, w3, w4, w5, w6, w7, w13, w9])
def s233 : Snap := (b135, [w0, w1, w2, w3, w4, w5, w15, w6, w7, w13])
def s234 : Snap := (b172, [w0, w1, w2, w3, w4, w5, w6, w7, w13, w9, w40])
def s235 : Snap := (b118, [w21, w0, w1, w2, w3, w4, w5, w6, w7, w13, w9])
def s236 : Snap := (b112, [w19, w0, w1, w2, w3, w4, w5, w6, w7, w13])
def s237 : Snap := (b173, [w0, w1, w2, w3, w4, w5, w6, w7, w13, w9, w18])
def s238 : Snap := (b174, [w0, w1, w2, w3, w5, w6, w7, w13, w64, w9])
def s239 : Snap := (b114, [w12, w0, w1, w2, w3, w4, w5, w6, w7, w13, w9])
def s240 : Snap := (b175, [w0, w1, w2, w3, w5, w6, w7, w64, w9])
def s241 : Snap := (b176, [w0, w1, w2, w14, w3, w4, w5, w6, w7, w13, w9])
def s242 : Snap := (b177, [w0, w1, w2, w36, w3, w4, w5, w6, w7, w13, w9])
def s243 : Snap := (b178, [w0, w1, w2, w3, w4, w5, w6, w7, w13, w9, w42])
def s244 : Snap := (b112, [w22, w0, w1, w2, w3, w5, w6, w7, w13, w9])
def s245 : Snap := (b179, [w10, w0, w1, w2, w3, w4, w5, w6, w7, w13, w9])
def s246 : Snap := (b180, [w0, w1, w2, w3, w47, w4, w5, w6, w7, w13, w9])
def s247 : Snap := (b181, [w0, w1, w2, w3, w26, w4, w5, w6, w7, w13, w9])
def s248 : Snap := (b182, [w0, w1, w2, w3, w4, w5, w15, w6, w7, w13, w9])
def s249 : Snap := (b183, [w0, w1, w2, w3, w4, w5, w6, w7, w64, w9])
def s250 : Snap := (b128, [w22, w0, w1, w2, w3, w4, w5, w6, w7, w13, w9])
def s251 : Snap := (b168, [w0, w1, w2, w37, w3, w4, w5, w6, w7, w13, w9])
def s252 : Snap := (b184, [w19, w0, w1, w2, w3, w4, w5, w6, w7, w13, w9])
def s253 : Snap := (b138, [w0, w1, w2, w29, w3, w4, w5, w6, w7, w13, w9])
def s254 : Snap := (b152, [w0, w1, w2, w3, w31, w4, w5, w6, w7, w13, w9])
def s255 : Snap := (b185, [w0, w1, w2, w3, w4, w5, w6, w7, w13, w64, w9])
def s256 : Snap := (b115, [w21, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s257 : Snap := (b186, [w0, w1, w2, w3, w4, w5, w6, w7, w9, w65])
def s258 : Snap := (b187, [w21, w0, w1, w2, w3, w4, w5, w6, w7, w9, w65])
def s259 : Snap := (b188, [w0, w1, w2, w3, w5, w66, w6, w7, w8, w9])
def s260 : Snap := (b131, [w12, w21, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s261 : Snap := (b118, [w21, w0, w1, w2, w3, w4, w5, w15, w7, w8, w9])
def s262 : Snap := (b189, [w0, w1, w2, w3, w50, w4, w5, w6, w7, w8, w9])
def s263 : Snap := (b190, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w51])
def s264 : Snap := (b191, [w21, w0, w1, w2, w14, w3, w4, w5, w6, w7, w8, w9])
def s265 : Snap := (b192, [w16, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s266 : Snap := (b193, [w16, w21, w0, w1, w2, w3, w4, w6, w7, w8, w9])
def s267 : Snap := (b131, [w45, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s268 : Snap := (b118, [w48, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s269 : Snap := (b194, [w21, w0, w1, w2, w3, w5, w6, w7, w8, w67, w9])
def s270 : Snap := (b195, [w21, w0, w1, w2, w3, w5, w6, w7, w8, w9, w68])
def s271 : Snap := (b120, [w22, w21, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s272 : Snap := (b142, [w21, w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s273 : Snap := (b131, [w21, w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s274 : Snap := (b118, [w21, w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s275 : Snap := (b196, [w0, w1, w2, w3, w4, w5, w66, w6, w7, w8, w9])
def s276 : Snap := (b115, [w69, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s277 : Snap := (b197, [w21, w0, w1, w2, w3, w50, w4, w5, w6, w7, w8, w9])
def s278 : Snap := (b198, [w21, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w51])
def s279 : Snap := (b199, [w12, w21, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s280 : Snap := (b200, [w21, w0, w1, w2, w3, w4, w5, w15, w6, w7, w8, w9])
def s281 : Snap := (b201, [w21, w0, w1, w2, w17, w3, w4, w5, w6, w7, w8, w9])
def s282 : Snap := (b202, [w21, w0, w1, w2, w3, w4, w5, w6, w7, w13, w8, w9])
def s283 : Snap := (b203, [w70, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s284 : Snap := (b203, [w34, w21, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s285 : Snap := (b203, [w21, w0, w1, w2, w3, w4, w5, w25, w7, w8, w9])
def s286 : Snap := (b204, [w21, w0, w1, w2, w29, w3, w4, w5, w6, w7, w8, w9])
def s287 : Snap := (b156, [w0, w1, w2, w14, w3, w4, w5, w6, w7, w8, w9])
def s288 : Snap := (b205, [w0, w1, w2, w3, w4, w6, w7, w8, w9, w71])
def s289 : Snap := (b206, [w0, w1, w2, w14, w3, w4, w6, w7, w8, w9, w71])
def s290 : Snap := (b207, [w0, w1, w2, w3, w5, w6, w7, w8, w72, w9])
def s291 : Snap := (b114, [w12, w0, w1, w2, w14, w4, w5, w6, w7, w8, w9])
def s292 : Snap := (b138, [w0, w1, w2, w14, w3, w4, w5, w15, w6, w7, w8])
def s293 : Snap := (b208, [w0, w1, w2, w3, w52, w4, w5, w6, w7, w8, w9])
def s294 : Snap := (b209, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w53])
def s295 : Snap := (b210, [w0, w1, w2, w36, w3, w4, w5, w6, w7, w8, w9])
def s296 : Snap := (b211, [w0, w1, w2, w36, w14, w3, w4, w5, w6, w7, w9])
def s297 : Snap := (b114, [w46, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s298 : Snap := (b138, [w0, w1, w2, w49, w3, w4, w5, w6, w7, w8, w9])
def s299 : Snap := (b212, [w0, w1, w2, w14, w3, w5, w73, w6, w7, w8, w9])
def s300 : Snap := (b213, [w0, w1, w2, w14, w3, w5, w6, w74, w7, w8, w9])
def s301 : Snap := (b160, [w0, w1, w2, w37, w14, w3, w5, w6, w7, w8, w9])
def s302 : Snap := (b176, [w0, w1, w2, w14, w3, w41, w5, w6, w7, w8, w9])
def s303 : Snap := (b114, [w22, w0, w1, w2, w14, w3, w5, w6, w7, w8, w9])
def s304 : Snap := (b138, [w0, w1, w2, w14, w3, w31, w5, w6, w7, w8, w9])
def s305 : Snap := (b214, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w72, w9])
def s306 : Snap := (b156, [w0, w1, w2, w75, w3, w5, w6, w7, w8, w9])
def s307 : Snap := (b215, [w0, w1, w2, w14, w3, w52, w4, w5, w6, w7, w8, w9])
def s308 : Snap := (b216, [w0, w1, w2, w14, w3, w4, w5, w6, w7, w8, w9, w53])
def s309 : Snap := (b217, [w12, w0, w1, w2, w14, w3, w4, w5, w6, w7, w8, w9])
def s310 : Snap := (b218, [w0, w1, w2, w14, w3, w4, w5, w15, w6, w7, w8, w9])
def s311 : Snap := (b219, [w10, w0, w1, w2, w14, w3, w4, w5, w6, w7, w8, w9])
def s312 : Snap := (b220, [w0, w1, w2, w14, w3, w26, w4, w5, w6, w7, w8, w9])
def s313 : Snap := (b221, [w0, w1, w2, w76, w3, w4, w5, w6, w7, w8, w9])
def s314 : Snap := (b221, [w0, w1, w2, w30, w14, w4, w5, w6, w7, w8, w9])
def s315 : Snap := (b221, [w0, w1, w2, w14, w3, w4, w20, w5, w6, w7, w8])
def s316 : Snap := (b222, [w0, w1, w2, w29, w14, w3, w4, w5, w6, w7, w8, w9])
def s317 : Snap := (b111, [w12, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s318 : Snap := (b223, [w0, w1, w2, w3, w5, w77, w6, w7, w8, w9])
def s319 : Snap := (b165, [w10, w12, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s320 : Snap := (b125, [w12, w0, w1, w2, w17, w4, w5, w6, w7, w8, w9])
def s321 : Snap := (b131, [w12, w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s322 : Snap := (b114, [w12, w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s323 : Snap := (b191, [w12, w0, w1, w2, w3, w4, w5, w15, w6, w7, w8, w9])
def s324 : Snap := (b224, [w12, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w44])
def s325 : Snap := (b225, [w0, w1, w2, w3, w4, w5, w6, w78, w7, w8, w9])
def s326 : Snap := (b226, [w12, w0, w1, w2, w3, w5, w6, w74, w7, w8, w9])
def s327 : Snap := (b227, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w79])
def s328 : Snap := (b228, [w12, w0, w1, w2, w3, w5, w6, w7, w8, w9, w68])
def s329 : Snap := (b111, [w80, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s330 : Snap := (b126, [w22, w12, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s331 : Snap := (b166, [w12, w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s332 : Snap := (b165, [w24, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s333 : Snap := (b125, [w39, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s334 : Snap := (b229, [w12, w0, w1, w2, w3, w26, w4, w5, w6, w7, w8, w9])
def s335 : Snap := (b230, [w12, w0, w1, w2, w3, w4, w5, w6, w7, w13, w8, w9])
def s336 : Snap := (b231, [w12, w0, w1, w2, w29, w3, w4, w5, w6, w7, w8, w9])
def s337 : Snap := (b201, [w12, w0, w1, w2, w3, w4, w5, w25, w6, w7, w8, w9])
def s338 : Snap := (b135, [w0, w1, w2, w3, w4, w5, w15, w6, w7, w8, w9])
def s339 : Snap := (b232, [w0, w1, w2, w3, w5, w6, w81, w7, w8, w9])
def s340 : Snap := (b181, [w0, w1, w2, w3, w26, w4, w5, w15, w7, w8, w9])
def s341 : Snap := (b147, [w0, w1, w2, w3, w4, w5, w15, w6, w7, w13, w8])
def s342 : Snap := (b118, [w22, w0, w1, w2, w3, w5, w15, w6, w7, w8, w9])
def s343 : Snap := (b138, [w0, w1, w2, w37, w3, w5, w15, w6, w7, w8, w9])
def s344 : Snap := (b233, [w0, w1, w2, w3, w47, w4, w5, w15, w6, w7, w8, w9])
def s345 : Snap := (b234, [w0, w1, w2, w3, w5, w73, w15, w6, w7, w8, w9])
def s346 : Snap := (b235, [w0, w1, w2, w3, w5, w15, w6, w7, w8, w67, w9])
def s347 : Snap := (b236, [w0, w1, w2, w3, w4, w5, w6, w82, w7, w8, w9])
def s348 : Snap := (b237, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w83])
def s349 : Snap := (b135, [w0, w1, w2, w3, w84, w5, w6, w7, w8, w9])
def s350 : Snap := (b181, [w0, w1, w2, w3, w33, w4, w5, w6, w7, w8, w9])
def s351 : Snap := (b148, [w0, w1, w2, w3, w31, w5, w15, w6, w7, w8, w9])
def s352 : Snap := (b147, [w0, w1, w2, w3, w4, w5, w43, w6, w7, w8, w9])
def s353 : Snap := (b182, [w0, w1, w2, w3, w41, w5, w15, w6, w7, w8, w9])
def s354 : Snap := (b238, [w10, w0, w1, w2, w3, w4, w5, w15, w6, w7, w8, w9])
def s355 : Snap := (b239, [w0, w1, w2, w17, w3, w4, w5, w15, w6, w7, w8, w9])
def s356 : Snap := (b220, [w0, w1, w2, w30, w3, w4, w5, w15, w6, w7, w8, w9])
def s357 : Snap := (b240, [w0, w1, w2, w29, w3, w4, w5, w15, w6, w7, w8, w9])
def s358 : Snap := (b241, [w10, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s359 : Snap := (b242, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w11])
def s360 : Snap := (b192, [w10, w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s361 : Snap := (b179, [w10, w0, w1, w2, w3, w4, w20, w6, w7, w8, w9])
def s362 : Snap := (b241, [w22, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s363 : Snap := (b243, [w0, w1, w2, w3, w23, w4, w5, w6, w7, w8, w9])
def s364 : Snap := (b192, [w10, w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s365 : Snap := (b244, [w0, w1, w2, w3, w61, w5, w6, w7, w8, w9])
def s366 : Snap := (b165, [w10, w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s367 : Snap := (b165, [w10, w0, w1, w2, w30, w3, w4, w6, w7, w8, w9])
def s368 : Snap := (b179, [w10, w19, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s369 : Snap := (b179, [w10, w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s370 : Snap := (b245, [w10, w0, w1, w2, w3, w5, w6, w74, w7, w8, w9])
def s371 : Snap := (b246, [w10, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w18])
def s372 : Snap := (b247, [w10, w0, w1, w2, w3, w5, w6, w7, w8, w67, w9])
def s373 : Snap := (b179, [w85, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s374 : Snap := (b248, [w0, w1, w2, w3, w4, w5, w6, w86, w7, w8, w9])
def s375 : Snap := (b249, [w0, w1, w2, w3, w26, w4, w5, w6, w7, w8, w9])
def s376 : Snap := (b250, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w27])
def s377 : Snap := (b163, [w0, w1, w2, w30, w3, w26, w4, w6, w7, w8, w9])
def s378 : Snap := (b249, [w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s379 : Snap := (b251, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w32])
def s380 : Snap := (b192, [w22, w0, w1, w2, w3, w26, w5, w6, w7, w8, w9])
def s381 : Snap := (b252, [w0, w1, w2, w3, w62, w5, w6, w7, w8, w9])
def s382 : Snap := (b181, [w0, w1, w2, w3, w26, w41, w5, w6, w7, w8, w9])
def s383 : Snap := (b181, [w0, w1, w2, w3, w26, w4, w20, w6, w7, w8, w9])
def s384 : Snap := (b163, [w0, w1, w2, w29, w3, w26, w4, w5, w7, w8, w9])
def s385 : Snap := (b163, [w0, w1, w2, w37, w3, w26, w5, w6, w7, w8, w9])
def s386 : Snap := (b253, [w0, w1, w2, w3, w26, w5, w73, w6, w7, w8, w9])
def s387 : Snap := (b254, [w0, w1, w2, w3, w26, w4, w5, w6, w7, w8, w9, w28])
def s388 : Snap := (b255, [w0, w1, w2, w3, w26, w5, w6, w7, w8, w9, w68])
def s389 : Snap := (b163, [w0, w1, w2, w87, w3, w4, w5, w6, w7, w8, w9])
def s390 : Snap := (b256, [w0, w1, w2, w3, w88, w4, w5, w6, w7, w8, w9])
def s391 : Snap := (b257, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w8, w9])
def s392 : Snap := (b258, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w35])
def s393 : Snap := (b210, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w13, w9])
def s394 : Snap := (b145, [w0, w1, w2, w17, w3, w4, w5, w25, w6, w7, w9])
def s395 : Snap := (b257, [w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s396 : Snap := (b259, [w0, w1, w2, w3, w38, w4, w5, w6, w7, w8, w9])
def s397 : Snap := (b210, [w0, w1, w2, w17, w3, w41, w5, w6, w7, w8, w9])
def s398 : Snap := (b260, [w0, w1, w2, w3, w5, w6, w7, w63, w8, w9])
def s399 : Snap := (b125, [w22, w0, w1, w2, w17, w3, w5, w6, w7, w8, w9])
def s400 : Snap := (b125, [w34, w0, w1, w2, w17, w3, w4, w5, w6, w7, w9])
def s401 : Snap := (b145, [w0, w1, w2, w29, w17, w4, w5, w6, w7, w8, w9])
def s402 : Snap := (b145, [w0, w1, w2, w17, w3, w31, w5, w6, w7, w8, w9])
def s403 : Snap := (b261, [w0, w1, w2, w17, w3, w5, w6, w7, w8, w9, w68])
def s404 : Snap := (b262, [w0, w1, w2, w17, w3, w4, w5, w6, w7, w8, w9, w28])
def s405 : Snap := (b263, [w0, w1, w2, w17, w3, w5, w73, w6, w7, w8, w9])
def s406 : Snap := (b145, [w0, w1, w2, w89, w3, w4, w5, w6, w7, w8, w9])
def s407 : Snap := (b264, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w90])
def s408 : Snap := (b265, [w0, w1, w2, w3, w4, w5, w6, w7, w13, w8, w9])
def s409 : Snap := (b266, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w40])
def s410 : Snap := (b123, [w34, w0, w1, w2, w3, w4, w5, w6, w7, w13, w9])
def s411 : Snap := (b265, [w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s412 : Snap := (b267, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w42])
def s413 : Snap := (b210, [w0, w1, w2, w37, w3, w5, w6, w7, w13, w8, w9])
def s414 : Snap := (b268, [w0, w1, w2, w3, w5, w6, w7, w64, w8, w9])
def s415 : Snap := (b147, [w0, w1, w2, w3, w31, w5, w6, w7, w13, w8, w9])
def s416 : Snap := (b147, [w0, w1, w2, w3, w4, w5, w25, w6, w7, w13, w9])
def s417 : Snap := (b123, [w19, w0, w1, w2, w3, w4, w5, w6, w7, w13, w8])
def s418 : Snap := (b123, [w22, w0, w1, w2, w3, w5, w6, w7, w13, w8, w9])
def s419 : Snap := (b269, [w0, w1, w2, w3, w5, w6, w7, w13, w8, w67, w9])
def s420 : Snap := (b270, [w0, w1, w2, w3, w4, w5, w6, w7, w13, w8, w9, w18])
def s421 : Snap := (b271, [w0, w1, w2, w3, w5, w6, w74, w7, w13, w8, w9])
def s422 : Snap := (b123, [w91, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s423 : Snap := (b272, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w92, w9])
def s424 : Snap := (b273, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w18])
def s425 : Snap := (b274, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w28, w18])
def s426 : Snap := (b273, [w0, w1, w93, w3, w4, w5, w6, w7, w8, w9])
def s427 : Snap := (b116, [w54, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s428 : Snap := (b173, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w55, w9])
def s429 : Snap := (b273, [w0, w1, w2, w3, w4, w94, w6, w7, w8, w9])
def s430 : Snap := (b273, [w0, w1, w2, w3, w4, w5, w6, w7, w95, w9])
def s431 : Snap := (b275, [w0, w1, w2, w3, w5, w73, w6, w7, w8, w9, w18])
def s432 : Snap := (b276, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w68, w18])
def s433 : Snap := (b116, [w22, w0, w1, w2, w3, w5, w6, w7, w8, w9, w18])
def s434 : Snap := (b173, [w0, w1, w2, w3, w41, w5, w6, w7, w8, w9, w18])
def s435 : Snap := (b277, [w19, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w18])
def s436 : Snap := (b273, [w0, w1, w2, w3, w96, w5, w6, w7, w8, w9])
def s437 : Snap := (b273, [w54, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s438 : Snap := (b273, [w0, w97, w2, w3, w4, w5, w6, w7, w8, w9])
def s439 : Snap := (b278, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w28])
def s440 : Snap := (b278, [w0, w1, w98, w3, w4, w5, w6, w7, w8, w9])
def s441 : Snap := (b157, [w0, w1, w2, w56, w3, w4, w5, w6, w7, w8, w9])
def s442 : Snap := (b139, [w0, w1, w2, w3, w4, w5, w57, w6, w7, w8, w9])
def s443 : Snap := (b278, [w0, w1, w2, w3, w4, w99, w6, w7, w8, w9])
def s444 : Snap := (b278, [w0, w1, w2, w3, w4, w5, w6, w7, w100, w9])
def s445 : Snap := (b279, [w0, w1, w2, w3, w5, w6, w7, w8, w67, w9, w28])
def s446 : Snap := (b280, [w0, w1, w2, w3, w5, w6, w74, w7, w8, w9, w28])
def s447 : Snap := (b157, [w0, w1, w2, w37, w3, w5, w6, w7, w8, w9, w28])
def s448 : Snap := (b139, [w0, w1, w2, w3, w31, w5, w6, w7, w8, w9, w28])
def s449 : Snap := (b281, [w0, w1, w2, w29, w3, w4, w5, w6, w7, w8, w9, w28])
def s450 : Snap := (b278, [w0, w1, w2, w3, w101, w5, w6, w7, w8, w9])
def s451 : Snap := (b278, [w0, w102, w2, w3, w4, w5, w6, w7, w8, w9])
def s452 : Snap := (b278, [w0, w1, w2, w56, w4, w5, w6, w7, w8, w9])
def s453 : Snap := (b136, [w0, w1, w2, w29, w3, w4, w5, w6, w7, w8, w9])
def s454 : Snap := (b282, [w0, w1, w2, w3, w5, w6, w103, w7, w8, w9])
def s455 : Snap := (b136, [w0, w1, w2, w104, w3, w5, w6, w7, w8, w9])
def s456 : Snap := (b283, [w0, w1, w2, w29, w3, w5, w73, w6, w7, w8, w9])
def s457 : Snap := (b284, [w0, w1, w2, w29, w3, w5, w6, w7, w8, w9, w68])
def s458 : Snap := (b169, [w0, w1, w2, w37, w29, w3, w5, w6, w7, w8, w9])
def s459 : Snap := (b151, [w0, w1, w2, w29, w3, w31, w5, w6, w7, w8, w9])
def s460 : Snap := (b131, [w22, w0, w1, w2, w29, w3, w5, w6, w7, w8, w9])
def s461 : Snap := (b138, [w0, w1, w2, w29, w3, w41, w5, w6, w7, w8, w9])
def s462 : Snap := (b285, [w0, w1, w2, w105, w3, w4, w5, w6, w7, w8, w9])
def s463 : Snap := (b286, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w106])
def s464 : Snap := (b112, [w19, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s465 : Snap := (b287, [w0, w1, w2, w3, w5, w107, w6, w7, w8, w9])
def s466 : Snap := (b112, [w108, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s467 : Snap := (b288, [w19, w0, w1, w2, w3, w5, w6, w7, w8, w67, w9])
def s468 : Snap := (b289, [w19, w0, w1, w2, w3, w5, w6, w74, w7, w8, w9])
def s469 : Snap := (b130, [w22, w19, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s470 : Snap := (b184, [w19, w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s471 : Snap := (b114, [w19, w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s472 : Snap := (b118, [w19, w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s473 : Snap := (b290, [w0, w1, w2, w3, w109, w4, w5, w6, w7, w8, w9])
def s474 : Snap := (b291, [w0, w1, w2, w3, w4, w5, w6, w110, w7, w8, w9])
def s475 : Snap := (b292, [w19, w21, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s476 : Snap := (b293, [w19, w0, w1, w2, w14, w3, w4, w5, w6, w7, w8, w9])
def s477 : Snap := (b110, [w22, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s478 : Snap := (b294, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w111])
def s479 : Snap := (b295, [w0, w1, w2, w3, w112, w5, w6, w7, w8, w9])
def s480 : Snap := (b296, [w0, w1, w2, w3, w5, w6, w113, w7, w8, w9])
def s481 : Snap := (b124, [w22, w0, w1, w2, w3, w5, w6, w7, w8, w9, w44])
def s482 : Snap := (b154, [w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s483 : Snap := (b297, [w0, w1, w2, w3, w5, w6, w114, w7, w8, w9])
def s484 : Snap := (b298, [w0, w1, w2, w115, w3, w5, w6, w7, w8, w9])
def s485 : Snap := (b299, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w116])
def s486 : Snap := (b164, [w0, w1, w2, w37, w3, w5, w6, w7, w8, w9, w44])
def s487 : Snap := (b134, [w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s488 : Snap := (b300, [w0, w1, w2, w3, w5, w6, w7, w8, w117, w9])
def s489 : Snap := (b301, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w118])
def s490 : Snap := (b302, [w0, w1, w2, w3, w119, w5, w6, w7, w8, w9])
def s491 : Snap := (b146, [w0, w1, w2, w3, w47, w31, w5, w6, w7, w8, w9])
def s492 : Snap := (b171, [w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s493 : Snap := (b303, [w0, w1, w2, w3, w5, w120, w6, w7, w8, w9])
def s494 : Snap := (b304, [w0, w1, w2, w3, w5, w6, w121, w7, w8, w9])
def s495 : Snap := (b305, [w0, w1, w2, w3, w5, w6, w7, w8, w122, w9])
def s496 : Snap := (b180, [w0, w1, w2, w3, w47, w41, w5, w6, w7, w8, w9])
def s497 : Snap := (b306, [w0, w1, w2, w30, w3, w4, w5, w6, w7, w8, w9])
def s498 : Snap := (b306, [w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s499 : Snap := (b165, [w22, w0, w1, w2, w30, w3, w5, w6, w7, w8, w9])
def s500 : Snap := (b221, [w0, w1, w2, w30, w3, w4, w5, w6, w7, w13, w9])
def s501 : Snap := (b163, [w0, w1, w2, w30, w3, w31, w5, w6, w7, w8, w9])
def s502 : Snap := (b221, [w0, w1, w2, w30, w3, w41, w5, w6, w7, w8, w9])
def s503 : Snap := (b307, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w123])
def s504 : Snap := (b308, [w0, w1, w2, w3, w4, w5, w6, w124, w7, w8, w9])
def s505 : Snap := (b309, [w0, w1, w2, w30, w3, w5, w73, w6, w7, w8, w9])
def s506 : Snap := (b310, [w34, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s507 : Snap := (b310, [w22, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s508 : Snap := (b125, [w34, w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s509 : Snap := (b203, [w34, w0, w1, w2, w3, w26, w4, w6, w7, w8, w9])
def s510 : Snap := (b123, [w34, w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s511 : Snap := (b203, [w34, w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s512 : Snap := (b311, [w0, w1, w2, w3, w4, w5, w6, w125, w7, w8, w9])
def s513 : Snap := (b312, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w126])
def s514 : Snap := (b313, [w34, w0, w1, w2, w3, w5, w6, w7, w8, w67, w9])
def s515 : Snap := (b314, [w0, w1, w2, w3, w4, w5, w25, w6, w7, w8, w9])
def s516 : Snap := (b314, [w0, w1, w2, w3, w31, w5, w6, w7, w8, w9])
def s517 : Snap := (b147, [w0, w1, w2, w3, w41, w5, w25, w6, w7, w8, w9])
def s518 : Snap := (b203, [w10, w0, w1, w2, w3, w4, w25, w6, w7, w8, w9])
def s519 : Snap := (b145, [w0, w1, w2, w37, w3, w5, w25, w6, w7, w8, w9])
def s520 : Snap := (b203, [w22, w0, w1, w2, w3, w5, w25, w6, w7, w8, w9])
def s521 : Snap := (b315, [w0, w1, w2, w3, w4, w5, w6, w127, w7, w8, w9])
def s522 : Snap := (b316, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w128, w9])
def s523 : Snap := (b317, [w0, w1, w2, w3, w5, w25, w6, w7, w8, w9, w68])
def s524 : Snap := (b318, [w0, w1, w2, w3, w4, w20, w5, w6, w7, w8, w9])
def s525 : Snap := (b318, [w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s526 : Snap := (b181, [w0, w1, w2, w3, w31, w20, w5, w6, w7, w8, w9])
def s527 : Snap := (b221, [w0, w1, w2, w17, w3, w4, w20, w5, w6, w7, w9])
def s528 : Snap := (b179, [w22, w0, w1, w2, w3, w20, w5, w6, w7, w8, w9])
def s529 : Snap := (b221, [w0, w1, w2, w37, w3, w20, w5, w6, w7, w8, w9])
def s530 : Snap := (b319, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w129])
def s531 : Snap := (b320, [w0, w1, w2, w3, w4, w5, w130, w6, w7, w8, w9])
def s532 : Snap := (b321, [w0, w1, w2, w3, w20, w5, w6, w74, w7, w8, w9])
def s533 : Snap := (b322, [w0, w1, w2, w3, w47, w4, w5, w6, w7, w8, w9])
def s534 : Snap := (b322, [w0, w1, w131, w3, w4, w5, w6, w7, w8, w9])
def s535 : Snap := (b322, [w0, w58, w2, w3, w4, w5, w6, w7, w8, w9])
def s536 : Snap := (b146, [w0, w1, w2, w132, w3, w4, w5, w6, w7, w8, w9])
def s537 : Snap := (b180, [w0, w1, w2, w3, w133, w4, w5, w6, w7, w8, w9])
def s538 : Snap := (b322, [w0, w1, w2, w134, w3, w4, w6, w7, w8, w9])
def s539 : Snap := (b322, [w0, w1, w2, w135, w3, w4, w5, w6, w7, w9])
def s540 : Snap := (b323, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w44])
def s541 : Snap := (b323, [w0, w1, w136, w3, w4, w5, w6, w7, w8, w9])
def s542 : Snap := (b323, [w0, w1, w2, w3, w4, w5, w6, w59, w8, w9])
def s543 : Snap := (b124, [w137, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s544 : Snap := (b164, [w0, w1, w2, w138, w3, w4, w5, w6, w7, w8, w9])
def s545 : Snap := (b323, [w0, w1, w2, w3, w4, w139, w6, w7, w8, w9])
def s546 : Snap := (b323, [w0, w1, w2, w3, w4, w5, w6, w7, w140, w9])
def s547 : Snap := (b324, [w0, w1, w2, w3, w5, w73, w6, w7, w8, w9])
def s548 : Snap := (b325, [w0, w1, w2, w3, w141, w5, w6, w7, w8, w9])
def s549 : Snap := (b326, [w0, w1, w2, w142, w3, w5, w6, w7, w8, w9])
def s550 : Snap := (b324, [w0, w1, w2, w3, w61, w6, w7, w8, w9])
def s551 : Snap := (b327, [w0, w1, w2, w3, w5, w143, w6, w7, w8, w9])
def s552 : Snap := (b328, [w0, w1, w2, w3, w5, w6, w7, w8, w67, w9])
def s553 : Snap := (b329, [w0, w1, w2, w3, w5, w6, w7, w8, w144, w9])
def s554 : Snap := (b330, [w145, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s555 : Snap := (b328, [w0, w1, w2, w3, w5, w6, w7, w63, w9])
def s556 : Snap := (b331, [w0, w1, w2, w3, w5, w146, w6, w7, w8, w9])
def s557 : Snap := (b332, [w0, w1, w2, w3, w5, w6, w74, w7, w8, w9])
def s558 : Snap := (b333, [w147, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s559 : Snap := (b334, [w0, w1, w2, w3, w5, w6, w148, w7, w8, w9])
def s560 : Snap := (b332, [w0, w1, w2, w3, w62, w6, w7, w8, w9])
def s561 : Snap := (b335, [w0, w1, w2, w149, w3, w5, w6, w7, w8, w9])
def s562 : Snap := (b336, [w0, w1, w2, w3, w5, w6, w7, w8, w9, w68])
def s563 : Snap := (b337, [w0, w1, w2, w150, w3, w5, w6, w7, w8, w9])
def s564 : Snap := (b338, [w0, w1, w2, w3, w5, w151, w6, w7, w8, w9])
def s565 : Snap := (b336, [w0, w1, w2, w3, w5, w6, w7, w64, w9])
def s566 : Snap := (b339, [w152, w0, w1, w2, w3, w5, w6, w7, w8, w9])
def s567 : Snap := (b340, [w22, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9])
def s568 : Snap := (b341, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w111])
def s569 : Snap := (b342, [w0, w1, w2, w3, w4, w5, w6, w113, w7, w8, w9])
def s570 : Snap := (b343, [w0, w1, w2, w3, w112, w4, w5, w6, w7, w8, w9])
def s571 : Snap := (b128, [w22, w0, w1, w2, w3, w41, w5, w6, w7, w8, w9])
def s572 : Snap := (b132, [w22, w0, w1, w2, w37, w3, w5, w6, w7, w8, w9])
def s573 : Snap := (b344, [w0, w1, w2, w37, w3, w4, w5, w6, w7, w8, w9])
def s574 : Snap := (b345, [w0, w1, w2, w3, w4, w5, w6, w114, w7, w8, w9])
def s575 : Snap := (b346, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w116])
def s576 : Snap := (b347, [w0, w1, w2, w115, w3, w4, w5, w6, w7, w8, w9])
def s577 : Snap := (b150, [w0, w1, w2, w37, w3, w31, w5, w6, w7, w8, w9])
def s578 : Snap := (b348, [w0, w1, w2, w3, w31, w4, w5, w6, w7, w8, w9])
def s579 : Snap := (b349, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w117, w9])
def s580 : Snap := (b350, [w0, w1, w2, w3, w119, w4, w5, w6, w7, w8, w9])
def s581 : Snap := (b351, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w118])
def s582 : Snap := (b152, [w0, w1, w2, w3, w31, w41, w5, w6, w7, w8, w9])
def s583 : Snap := (b352, [w0, w1, w2, w3, w41, w4, w5, w6, w7, w8, w9])
def s584 : Snap := (b353, [w0, w1, w2, w3, w4, w5, w120, w6, w7, w8, w9])
def s585 : Snap := (b354, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w122, w9])
def s586 : Snap := (b355, [w0, w1, w2, w3, w4, w5, w6, w121, w7, w8, w9])
def s587 : Snap := (b356, [w0, w1, w2, w3, w4, w5, w6, w60, w7, w8, w9])
def s588 : Snap := (b356, [w0, w1, w2, w3, w153, w4, w6, w7, w8, w9])
def s589 : Snap := (b357, [w0, w1, w2, w3, w153, w4, w5, w6, w7, w8, w9])
def s590 : Snap := (b358, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w154])
def s591 : Snap := (b358, [w0, w1, w2, w3, w4, w5, w6, w7, w155, w9])
def s592 : Snap := (b359, [w0, w1, w2, w3, w4, w5, w6, w7, w155, w8, w9])
def s593 : Snap := (b360, [w0, w1, w2, w3, w4, w5, w73, w6, w7, w8, w9])
def s594 : Snap := (b361, [w0, w1, w2, w3, w4, w5, w6, w7, w8, w67, w9])
def s595 : Snap := (b362, [w0, w1, w2, w3, w4, w5, w6, w74, w7, w8, w9])
noncomputable def testCut (k : ℕ) (cs : List Snap) (s : Snap) := runCut rootL rootM rootG k cs s
def Valid (k : ℕ) (s : Snap) := BoundAt (PZ 0) (tz 0) rootL rootM k s
def RootCtx := Ctx (PZ 0) rootL rootM rootG (tz 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma init0 : initialCheck 0 14 (fun z v => !listed [s0, s153] z v)=false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert0 : testCut 14 [s1, s20, s38, s55, s71, s83, s94, s102, s109, s113, s119, s124, s131, s138, s140, s141, s145, s148, s150, s152] s0=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert1 : testCut 13 [s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19] s1=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert2 : testCut 12 [] s2=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert3 : testCut 12 [] s3=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert4 : testCut 12 [] s4=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert5 : testCut 12 [] s5=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert6 : testCut 12 [] s6=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert7 : testCut 12 [] s7=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert8 : testCut 12 [] s8=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert9 : testCut 12 [] s9=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert10 : testCut 12 [] s10=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert11 : testCut 12 [] s11=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert12 : testCut 12 [] s12=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert13 : testCut 12 [] s13=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert14 : testCut 12 [] s14=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert15 : testCut 12 [] s15=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert16 : testCut 12 [] s16=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert17 : testCut 12 [] s17=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert18 : testCut 12 [] s18=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert19 : testCut 12 [] s19=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert20 : testCut 13 [s21, s22, s23, s24, s25, s26, s8, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37] s20=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert21 : testCut 12 [] s21=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert22 : testCut 12 [] s22=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert23 : testCut 12 [] s23=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert24 : testCut 12 [] s24=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert25 : testCut 12 [] s25=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert26 : testCut 12 [] s26=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert27 : testCut 12 [] s27=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert28 : testCut 12 [] s28=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert29 : testCut 12 [] s29=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert30 : testCut 12 [] s30=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert31 : testCut 12 [] s31=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert32 : testCut 12 [] s32=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert33 : testCut 12 [] s33=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert34 : testCut 12 [] s34=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert35 : testCut 12 [] s35=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert36 : testCut 12 [] s36=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert37 : testCut 12 [] s37=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert38 : testCut 13 [s39, s40, s41, s24, s42, s43, s44, s9, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54] s38=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert39 : testCut 12 [] s39=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert40 : testCut 12 [] s40=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert41 : testCut 12 [] s41=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert42 : testCut 12 [] s42=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert43 : testCut 12 [] s43=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert44 : testCut 12 [] s44=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert45 : testCut 12 [] s45=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert46 : testCut 12 [] s46=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert47 : testCut 12 [] s47=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert48 : testCut 12 [] s48=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert49 : testCut 12 [] s49=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert50 : testCut 12 [] s50=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert51 : testCut 12 [] s51=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert52 : testCut 12 [] s52=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert53 : testCut 12 [] s53=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert54 : testCut 12 [] s54=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert55 : testCut 13 [s56, s57, s58, s5, s59, s60, s44, s27, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70] s55=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert56 : testCut 12 [] s56=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert57 : testCut 12 [] s57=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert58 : testCut 12 [] s58=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert59 : testCut 12 [] s59=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert60 : testCut 12 [] s60=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert61 : testCut 12 [] s61=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert62 : testCut 12 [] s62=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert63 : testCut 12 [] s63=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert64 : testCut 12 [] s64=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert65 : testCut 12 [] s65=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert66 : testCut 12 [] s66=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert67 : testCut 12 [] s67=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert68 : testCut 12 [] s68=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert69 : testCut 12 [] s69=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert70 : testCut 12 [] s70=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert71 : testCut 13 [s72, s73, s3, s40, s26, s60, s74, s75, s15, s50, s76, s77, s78, s79, s80, s18, s53, s81, s82] s71=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert72 : testCut 12 [] s72=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert73 : testCut 12 [] s73=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert74 : testCut 12 [] s74=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert75 : testCut 12 [] s75=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert76 : testCut 12 [] s76=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert77 : testCut 12 [] s77=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert78 : testCut 12 [] s78=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert79 : testCut 12 [] s79=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert80 : testCut 12 [] s80=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert81 : testCut 12 [] s81=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert82 : testCut 12 [] s82=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert83 : testCut 13 [s84, s85, s22, s57, s7, s43, s74, s86, s87, s33, s88, s66, s89, s90, s91, s36, s69, s92, s93] s83=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert84 : testCut 12 [] s84=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert85 : testCut 12 [] s85=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert86 : testCut 12 [] s86=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert87 : testCut 12 [] s87=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert88 : testCut 12 [] s88=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert89 : testCut 12 [] s89=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert90 : testCut 12 [] s90=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert91 : testCut 12 [] s91=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert92 : testCut 12 [] s92=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert93 : testCut 12 [] s93=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert94 : testCut 13 [s72, s84, s42, s59, s8, s95, s96, s97, s98, s14, s32, s78, s89, s99, s100, s81, s92, s101] s94=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert95 : testCut 12 [] s95=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert96 : testCut 12 [] s96=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert97 : testCut 12 [] s97=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert98 : testCut 12 [] s98=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert99 : testCut 12 [] s99=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert100 : testCut 12 [] s100=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert101 : testCut 12 [] s101=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert102 : testCut 13 [s73, s85, s6, s25, s44, s95, s103, s104, s105, s49, s65, s79, s90, s106, s107, s82, s93, s108] s102=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert103 : testCut 12 [] s103=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert104 : testCut 12 [] s104=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert105 : testCut 12 [] s105=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert106 : testCut 12 [] s106=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert107 : testCut 12 [] s107=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert108 : testCut 12 [] s108=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert109 : testCut 13 [s4, s23, s41, s58, s75, s86, s96, s103, s110, s111, s16, s51, s34, s67, s112] s109=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert110 : testCut 12 [] s110=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert111 : testCut 12 [] s111=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert112 : testCut 12 [] s112=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert113 : testCut 13 [s114, s11, s62, s115, s116, s117, s110, s118] s113=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert114 : testCut 12 [] s114=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert115 : testCut 12 [] s115=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert116 : testCut 12 [] s116=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert117 : testCut 12 [] s117=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert118 : testCut 12 [] s118=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert119 : testCut 13 [s114, s29, s46, s120, s121, s122, s111, s123] s119=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert120 : testCut 12 [] s120=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert121 : testCut 12 [] s121=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert122 : testCut 12 [] s122=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert123 : testCut 12 [] s123=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert124 : testCut 13 [s122, s30, s47, s112, s81, s93, s125, s126, s127, s128, s129, s130] s124=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert125 : testCut 12 [] s125=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert126 : testCut 12 [] s126=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert127 : testCut 12 [] s127=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert128 : testCut 12 [] s128=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert129 : testCut 12 [] s129=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert130 : testCut 12 [] s130=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert131 : testCut 13 [s117, s12, s63, s132, s82, s92, s133, s134, s135, s136, s129, s137] s131=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert132 : testCut 12 [] s132=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert133 : testCut 12 [] s133=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert134 : testCut 12 [] s134=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert135 : testCut 12 [] s135=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert136 : testCut 12 [] s136=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert137 : testCut 12 [] s137=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert138 : testCut 13 [s31, s87, s51, s18, s106, s123, s70, s101, s139] s138=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert139 : testCut 12 [] s139=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert140 : testCut 13 [s64, s88, s16, s53, s99, s118, s37, s108, s139] s140=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert141 : testCut 13 [s48, s76, s34, s69, s100, s142, s19, s143, s144] s141=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert142 : testCut 12 [] s142=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert143 : testCut 12 [] s143=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert144 : testCut 12 [] s144=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert145 : testCut 13 [s13, s77, s67, s36, s107, s146, s54, s147, s144] s145=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert146 : testCut 12 [] s146=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert147 : testCut 12 [] s147=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert148 : testCut 13 [s149, s91] s148=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert149 : testCut 12 [] s149=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert150 : testCut 13 [s151, s80] s150=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert151 : testCut 12 [] s151=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert152 : testCut 13 [] s152=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert153 : testCut 14 [s154, s181, s207, s232, s256, s287, s317, s338, s358, s375, s391, s408, s424, s439, s453, s464, s477, s482, s487, s492, s497, s506, s515, s524, s533, s540, s547, s552, s557, s562, s567, s573, s578, s583, s587, s590, s593, s594, s595] s153=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert154 : testCut 13 [s155, s156, s157, s158, s159, s160, s161, s162, s163, s164, s165, s166, s167, s168, s169, s170, s171, s172, s173, s174, s175, s176, s177, s178, s179, s180] s154=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert155 : testCut 12 [] s155=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert156 : testCut 12 [] s156=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert157 : testCut 12 [] s157=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert158 : testCut 12 [] s158=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert159 : testCut 12 [] s159=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert160 : testCut 12 [] s160=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert161 : testCut 12 [] s161=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert162 : testCut 12 [] s162=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert163 : testCut 12 [] s163=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert164 : testCut 12 [] s164=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert165 : testCut 12 [] s165=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert166 : testCut 12 [] s166=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert167 : testCut 12 [] s167=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert168 : testCut 12 [] s168=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert169 : testCut 12 [] s169=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert170 : testCut 12 [] s170=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert171 : testCut 12 [] s171=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert172 : testCut 12 [] s172=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert173 : testCut 12 [] s173=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert174 : testCut 12 [] s174=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert175 : testCut 12 [] s175=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert176 : testCut 12 [] s176=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert177 : testCut 12 [] s177=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert178 : testCut 12 [] s178=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert179 : testCut 12 [] s179=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert180 : testCut 12 [] s180=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert181 : testCut 13 [s182, s183, s184, s185, s186, s160, s187, s188, s189, s190, s191, s192, s193, s194, s195, s196, s197, s198, s199, s200, s201, s202, s203, s204, s205, s206] s181=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert182 : testCut 12 [] s182=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert183 : testCut 12 [] s183=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert184 : testCut 12 [] s184=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert185 : testCut 12 [] s185=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert186 : testCut 12 [] s186=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert187 : testCut 12 [] s187=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert188 : testCut 12 [] s188=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert189 : testCut 12 [] s189=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert190 : testCut 12 [] s190=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert191 : testCut 12 [] s191=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert192 : testCut 12 [] s192=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert193 : testCut 12 [] s193=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert194 : testCut 12 [] s194=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert195 : testCut 12 [] s195=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert196 : testCut 12 [] s196=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert197 : testCut 12 [] s197=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert198 : testCut 12 [] s198=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert199 : testCut 12 [] s199=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert200 : testCut 12 [] s200=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert201 : testCut 12 [] s201=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert202 : testCut 12 [] s202=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert203 : testCut 12 [] s203=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert204 : testCut 12 [] s204=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert205 : testCut 12 [] s205=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert206 : testCut 12 [] s206=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert207 : testCut 13 [s208, s156, s184, s209, s210, s211, s212, s213, s214, s215, s216, s217, s218, s219, s220, s221, s222, s223, s224, s225, s226, s227, s228, s229, s230, s231] s207=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert208 : testCut 12 [] s208=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert209 : testCut 12 [] s209=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert210 : testCut 12 [] s210=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert211 : testCut 12 [] s211=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert212 : testCut 12 [] s212=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert213 : testCut 12 [] s213=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert214 : testCut 12 [] s214=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert215 : testCut 12 [] s215=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert216 : testCut 12 [] s216=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert217 : testCut 12 [] s217=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert218 : testCut 12 [] s218=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert219 : testCut 12 [] s219=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert220 : testCut 12 [] s220=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert221 : testCut 12 [] s221=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert222 : testCut 12 [] s222=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert223 : testCut 12 [] s223=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert224 : testCut 12 [] s224=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert225 : testCut 12 [] s225=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert226 : testCut 12 [] s226=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert227 : testCut 12 [] s227=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert228 : testCut 12 [] s228=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert229 : testCut 12 [] s229=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert230 : testCut 12 [] s230=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert231 : testCut 12 [] s231=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert232 : testCut 13 [s233, s183, s157, s234, s235, s211, s236, s237, s238, s239, s240, s241, s242, s243, s244, s245, s246, s247, s248, s249, s250, s251, s252, s253, s254, s255] s232=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert233 : testCut 12 [] s233=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert234 : testCut 12 [] s234=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert235 : testCut 12 [] s235=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert236 : testCut 12 [] s236=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert237 : testCut 12 [] s237=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert238 : testCut 12 [] s238=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert239 : testCut 12 [] s239=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert240 : testCut 12 [] s240=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert241 : testCut 12 [] s241=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert242 : testCut 12 [] s242=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert243 : testCut 12 [] s243=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert244 : testCut 12 [] s244=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert245 : testCut 12 [] s245=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert246 : testCut 12 [] s246=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert247 : testCut 12 [] s247=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert248 : testCut 12 [] s248=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert249 : testCut 12 [] s249=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert250 : testCut 12 [] s250=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert251 : testCut 12 [] s251=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert252 : testCut 12 [] s252=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert253 : testCut 12 [] s253=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert254 : testCut 12 [] s254=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert255 : testCut 12 [] s255=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert256 : testCut 13 [s257, s210, s235, s258, s160, s259, s260, s261, s166, s192, s262, s263, s264, s265, s266, s267, s268, s269, s270, s271, s272, s273, s274, s275, s276, s277, s278, s279, s280, s281, s282, s283, s284, s285, s286] s256=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert257 : testCut 12 [] s257=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert258 : testCut 12 [] s258=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert259 : testCut 12 [] s259=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert260 : testCut 12 [] s260=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert261 : testCut 12 [] s261=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert262 : testCut 12 [] s262=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert263 : testCut 12 [] s263=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert264 : testCut 12 [] s264=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert265 : testCut 12 [] s265=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert266 : testCut 12 [] s266=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert267 : testCut 12 [] s267=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert268 : testCut 12 [] s268=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert269 : testCut 12 [] s269=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert270 : testCut 12 [] s270=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert271 : testCut 12 [] s271=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert272 : testCut 12 [] s272=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert273 : testCut 12 [] s273=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert274 : testCut 12 [] s274=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert275 : testCut 12 [] s275=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert276 : testCut 12 [] s276=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert277 : testCut 12 [] s277=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert278 : testCut 12 [] s278=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert279 : testCut 12 [] s279=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert280 : testCut 12 [] s280=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert281 : testCut 12 [] s281=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert282 : testCut 12 [] s282=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert283 : testCut 12 [] s283=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert284 : testCut 12 [] s284=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert285 : testCut 12 [] s285=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert286 : testCut 12 [] s286=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert287 : testCut 13 [s288, s159, s186, s289, s211, s290, s291, s292, s217, s241, s293, s294, s264, s295, s296, s297, s298, s299, s300, s301, s302, s303, s304, s305, s306, s307, s308, s309, s310, s311, s312, s313, s314, s315, s316] s287=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert288 : testCut 12 [] s288=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert289 : testCut 12 [] s289=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert290 : testCut 12 [] s290=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert291 : testCut 12 [] s291=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert292 : testCut 12 [] s292=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert293 : testCut 12 [] s293=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert294 : testCut 12 [] s294=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert295 : testCut 12 [] s295=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert296 : testCut 12 [] s296=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert297 : testCut 12 [] s297=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert298 : testCut 12 [] s298=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert299 : testCut 12 [] s299=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert300 : testCut 12 [] s300=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert301 : testCut 12 [] s301=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert302 : testCut 12 [] s302=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert303 : testCut 12 [] s303=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert304 : testCut 12 [] s304=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert305 : testCut 12 [] s305=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert306 : testCut 12 [] s306=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert307 : testCut 12 [] s307=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert308 : testCut 12 [] s308=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert309 : testCut 12 [] s309=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert310 : testCut 12 [] s310=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert311 : testCut 12 [] s311=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert312 : testCut 12 [] s312=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert313 : testCut 12 [] s313=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert314 : testCut 12 [] s314=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert315 : testCut 12 [] s315=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert316 : testCut 12 [] s316=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert317 : testCut 13 [s155, s208, s260, s190, s291, s239, s318, s173, s319, s224, s320, s267, s321, s297, s322, s323, s324, s325, s326, s327, s328, s329, s330, s331, s332, s333, s279, s334, s309, s335, s336, s337] s317=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert318 : testCut 12 [] s318=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert319 : testCut 12 [] s319=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert320 : testCut 12 [] s320=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert321 : testCut 12 [] s321=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert322 : testCut 12 [] s322=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert323 : testCut 12 [] s323=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert324 : testCut 12 [] s324=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert325 : testCut 12 [] s325=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert326 : testCut 12 [] s326=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert327 : testCut 12 [] s327=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert328 : testCut 12 [] s328=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert329 : testCut 12 [] s329=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert330 : testCut 12 [] s330=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert331 : testCut 12 [] s331=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert332 : testCut 12 [] s332=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert333 : testCut 12 [] s333=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert334 : testCut 12 [] s334=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert335 : testCut 12 [] s335=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert336 : testCut 12 [] s336=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert337 : testCut 12 [] s337=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert338 : testCut 13 [s182, s233, s164, s261, s215, s292, s339, s340, s199, s341, s248, s342, s343, s268, s298, s323, s344, s345, s346, s347, s348, s349, s350, s351, s352, s353, s354, s280, s355, s310, s356, s357] s338=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert339 : testCut 12 [] s339=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert340 : testCut 12 [] s340=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert341 : testCut 12 [] s341=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert342 : testCut 12 [] s342=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert343 : testCut 12 [] s343=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert344 : testCut 12 [] s344=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert345 : testCut 12 [] s345=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert346 : testCut 12 [] s346=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert347 : testCut 12 [] s347=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert348 : testCut 12 [] s348=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert349 : testCut 12 [] s349=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert350 : testCut 12 [] s350=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert351 : testCut 12 [] s351=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert352 : testCut 12 [] s352=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert353 : testCut 12 [] s353=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert354 : testCut 12 [] s354=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert355 : testCut 12 [] s355=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert356 : testCut 12 [] s356=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert357 : testCut 12 [] s357=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert358 : testCut 13 [s359, s360, s245, s265, s223, s319, s361, s362, s363, s364, s365, s366, s367, s368, s369, s332, s370, s371, s354, s311, s372, s373, s374] s358=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert359 : testCut 12 [] s359=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert360 : testCut 12 [] s360=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert361 : testCut 12 [] s361=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert362 : testCut 12 [] s362=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert363 : testCut 12 [] s363=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert364 : testCut 12 [] s364=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert365 : testCut 12 [] s365=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert366 : testCut 12 [] s366=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert367 : testCut 12 [] s367=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert368 : testCut 12 [] s368=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert369 : testCut 12 [] s369=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert370 : testCut 12 [] s370=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert371 : testCut 12 [] s371=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert372 : testCut 12 [] s372=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert373 : testCut 12 [] s373=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert374 : testCut 12 [] s374=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert375 : testCut 13 [s376, s360, s221, s265, s247, s340, s377, s378, s379, s380, s381, s382, s383, s384, s385, s350, s386, s387, s334, s312, s388, s389, s390] s375=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert376 : testCut 12 [] s376=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert377 : testCut 12 [] s377=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert378 : testCut 12 [] s378=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert379 : testCut 12 [] s379=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert380 : testCut 12 [] s380=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert381 : testCut 12 [] s381=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert382 : testCut 12 [] s382=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert383 : testCut 12 [] s383=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert384 : testCut 12 [] s384=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert385 : testCut 12 [] s385=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert386 : testCut 12 [] s386=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert387 : testCut 12 [] s387=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert388 : testCut 12 [] s388=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert389 : testCut 12 [] s389=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert390 : testCut 12 [] s390=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert391 : testCut 13 [s392, s393, s196, s295, s172, s320, s394, s395, s396, s397, s398, s399, s400, s401, s402, s333, s403, s404, s355, s281, s405, s406, s407] s391=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert392 : testCut 12 [] s392=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert393 : testCut 12 [] s393=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert394 : testCut 12 [] s394=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert395 : testCut 12 [] s395=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert396 : testCut 12 [] s396=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert397 : testCut 12 [] s397=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert398 : testCut 12 [] s398=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert399 : testCut 12 [] s399=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert400 : testCut 12 [] s400=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert401 : testCut 12 [] s401=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert402 : testCut 12 [] s402=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert403 : testCut 12 [] s403=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert404 : testCut 12 [] s404=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert405 : testCut 12 [] s405=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert406 : testCut 12 [] s406=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert407 : testCut 12 [] s407=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert408 : testCut 13 [s409, s393, s170, s295, s198, s341, s410, s411, s412, s413, s414, s415, s416, s417, s418, s352, s419, s420, s335, s282, s421, s422, s423] s408=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert409 : testCut 12 [] s409=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert410 : testCut 12 [] s410=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert411 : testCut 12 [] s411=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert412 : testCut 12 [] s412=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert413 : testCut 12 [] s413=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert414 : testCut 12 [] s414=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert415 : testCut 12 [] s415=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert416 : testCut 12 [] s416=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert417 : testCut 12 [] s417=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert418 : testCut 12 [] s418=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert419 : testCut 12 [] s419=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert420 : testCut 12 [] s420=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert421 : testCut 12 [] s421=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert422 : testCut 12 [] s422=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert423 : testCut 12 [] s423=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert424 : testCut 13 [s162, s237, s425, s426, s427, s428, s429, s430, s431, s432, s433, s434, s435, s436, s437, s438] s424=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert425 : testCut 12 [] s425=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert426 : testCut 12 [] s426=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert427 : testCut 12 [] s427=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert428 : testCut 12 [] s428=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert429 : testCut 12 [] s429=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert430 : testCut 12 [] s430=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert431 : testCut 12 [] s431=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert432 : testCut 12 [] s432=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert433 : testCut 12 [] s433=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert434 : testCut 12 [] s434=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert435 : testCut 12 [] s435=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert436 : testCut 12 [] s436=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert437 : testCut 12 [] s437=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert438 : testCut 12 [] s438=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert439 : testCut 13 [s188, s213, s425, s440, s441, s442, s443, s444, s445, s446, s447, s448, s449, s450, s451, s452] s439=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert440 : testCut 12 [] s440=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert441 : testCut 12 [] s441=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert442 : testCut 12 [] s442=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert443 : testCut 12 [] s443=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert444 : testCut 12 [] s444=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert445 : testCut 12 [] s445=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert446 : testCut 12 [] s446=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert447 : testCut 12 [] s447=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert448 : testCut 12 [] s448=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert449 : testCut 12 [] s449=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert450 : testCut 12 [] s450=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert451 : testCut 12 [] s451=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert452 : testCut 12 [] s452=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert453 : testCut 13 [s187, s212, s267, s298, s454, s449, s384, s401, s203, s228, s178, s253, s455, s456, s457, s458, s459, s460, s461, s462, s463, s389, s406, s286, s316] s453=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert454 : testCut 12 [] s454=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert455 : testCut 12 [] s455=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert456 : testCut 12 [] s456=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert457 : testCut 12 [] s457=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert458 : testCut 12 [] s458=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert459 : testCut 12 [] s459=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert460 : testCut 12 [] s460=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert461 : testCut 12 [] s461=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert462 : testCut 12 [] s462=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert463 : testCut 12 [] s463=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert464 : testCut 13 [s161, s236, s297, s268, s465, s435, s368, s417, s177, s252, s204, s229, s466, s467, s468, s469, s470, s471, s472, s473, s474, s373, s422, s475, s476] s464=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert465 : testCut 12 [] s465=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert466 : testCut 12 [] s466=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert467 : testCut 12 [] s467=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert468 : testCut 12 [] s468=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert469 : testCut 12 [] s469=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert470 : testCut 12 [] s470=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert471 : testCut 12 [] s471=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert472 : testCut 12 [] s472=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert473 : testCut 12 [] s473=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert474 : testCut 12 [] s474=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert475 : testCut 12 [] s475=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert476 : testCut 12 [] s476=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert477 : testCut 13 [s244, s478, s342, s433, s380, s399, s271, s418, s479, s480, s329, s303, s466, s330, s276, s481] s477=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert478 : testCut 12 [] s478=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert479 : testCut 12 [] s479=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert480 : testCut 12 [] s480=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert481 : testCut 12 [] s481=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert482 : testCut 13 [s195, s483, s343, s447, s413, s366, s301, s385, s484, s485, s329, s273, s455, s331, s306, s486] s482=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert483 : testCut 12 [] s483=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert484 : testCut 12 [] s484=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert485 : testCut 12 [] s485=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert486 : testCut 12 [] s486=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert487 : testCut 13 [s220, s488, s321, s448, s364, s415, s272, s402, s489, s490, s349, s304, s455, s351, s276, s491] s487=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert488 : testCut 12 [] s488=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert489 : testCut 12 [] s489=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert490 : testCut 12 [] s490=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert491 : testCut 12 [] s491=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert492 : testCut 13 [s169, s493, s322, s434, s397, s382, s302, s369, s494, s495, s349, s274, s466, s353, s306, s496] s492=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert493 : testCut 12 [] s493=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert494 : testCut 12 [] s494=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert495 : testCut 12 [] s495=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert496 : testCut 12 [] s496=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert497 : testCut 13 [s377, s498, s367, s332, s499, s500, s501, s502, s313, s389, s314, s503, s504, s505] s497=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert498 : testCut 12 [] s498=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert499 : testCut 12 [] s499=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert500 : testCut 12 [] s500=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert501 : testCut 12 [] s501=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert502 : testCut 12 [] s502=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert503 : testCut 12 [] s503=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert504 : testCut 12 [] s504=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert505 : testCut 12 [] s505=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert506 : testCut 13 [s410, s507, s400, s333, s508, s509, s510, s511, s283, s284, s422, s512, s513, s514] s506=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert507 : testCut 12 [] s507=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert508 : testCut 12 [] s508=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert509 : testCut 12 [] s509=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert510 : testCut 12 [] s510=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert511 : testCut 12 [] s511=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert512 : testCut 12 [] s512=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert513 : testCut 12 [] s513=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert514 : testCut 12 [] s514=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert515 : testCut 13 [s394, s516, s416, s352, s517, s518, s519, s520, s283, s406, s285, s521, s522, s523] s515=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert516 : testCut 12 [] s516=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert517 : testCut 12 [] s517=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert518 : testCut 12 [] s518=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert519 : testCut 12 [] s519=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert520 : testCut 12 [] s520=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert521 : testCut 12 [] s521=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert522 : testCut 12 [] s522=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert523 : testCut 12 [] s523=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert524 : testCut 13 [s361, s525, s383, s350, s526, s527, s528, s529, s313, s373, s315, s530, s531, s532] s524=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert525 : testCut 12 [] s525=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert526 : testCut 12 [] s526=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert527 : testCut 12 [] s527=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert528 : testCut 12 [] s528=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert529 : testCut 12 [] s529=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert530 : testCut 12 [] s530=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert531 : testCut 12 [] s531=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert532 : testCut 12 [] s532=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert533 : testCut 13 [s534, s197, s246, s535, s536, s537, s344, s538, s539] s533=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert534 : testCut 12 [] s534=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert535 : testCut 12 [] s535=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert536 : testCut 12 [] s536=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert537 : testCut 12 [] s537=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert538 : testCut 12 [] s538=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert539 : testCut 12 [] s539=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert540 : testCut 13 [s541, s171, s222, s542, s543, s544, s324, s545, s546] s540=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert541 : testCut 12 [] s541=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert542 : testCut 12 [] s542=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert543 : testCut 12 [] s543=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert544 : testCut 12 [] s544=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert545 : testCut 12 [] s545=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert546 : testCut 12 [] s546=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert547 : testCut 13 [s548, s431, s549, s550, s299, s551] s547=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert548 : testCut 12 [] s548=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert549 : testCut 12 [] s549=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert550 : testCut 12 [] s550=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert551 : testCut 12 [] s551=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert552 : testCut 13 [s553, s445, s554, s555, s269, s556] s552=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert553 : testCut 12 [] s553=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert554 : testCut 12 [] s554=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert555 : testCut 12 [] s555=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert556 : testCut 12 [] s556=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert557 : testCut 13 [s558, s446, s559, s560, s300, s561] s557=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert558 : testCut 12 [] s558=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert559 : testCut 12 [] s559=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert560 : testCut 12 [] s560=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert561 : testCut 12 [] s561=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert562 : testCut 13 [s563, s432, s564, s565, s270, s566] s562=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert563 : testCut 12 [] s563=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert564 : testCut 12 [] s564=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert565 : testCut 12 [] s565=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert566 : testCut 12 [] s566=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert567 : testCut 13 [s250, s568, s202, s230, s569, s570, s571, s572] s567=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert568 : testCut 12 [] s568=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert569 : testCut 12 [] s569=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert570 : testCut 12 [] s570=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert571 : testCut 12 [] s571=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert572 : testCut 12 [] s572=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert573 : testCut 13 [s201, s574, s251, s179, s575, s576, s577, s572] s573=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert574 : testCut 12 [] s574=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert575 : testCut 12 [] s575=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert576 : testCut 12 [] s576=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert577 : testCut 12 [] s577=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert578 : testCut 13 [s226, s579, s176, s254, s580, s581, s577, s582] s578=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert579 : testCut 12 [] s579=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert580 : testCut 12 [] s580=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert581 : testCut 12 [] s581=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert582 : testCut 12 [] s582=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert583 : testCut 13 [s175, s584, s227, s205, s585, s586, s571, s582] s583=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert584 : testCut 12 [] s584=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert585 : testCut 12 [] s585=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert586 : testCut 12 [] s586=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert587 : testCut 13 [s588, s589] s587=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert588 : testCut 12 [] s588=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert589 : testCut 12 [] s589=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert590 : testCut 13 [s591, s592] s590=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert591 : testCut 12 [] s591=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert592 : testCut 12 [] s592=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert593 : testCut 13 [] s593=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert594 : testCut 13 [] s594=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert595 : testCut 13 [] s595=false := by decide +kernel

lemma v2 (h : RootCtx) : Valid 12 s2 := cut_sound h (by simp) cert2
lemma v3 (h : RootCtx) : Valid 12 s3 := cut_sound h (by simp) cert3
lemma v4 (h : RootCtx) : Valid 12 s4 := cut_sound h (by simp) cert4
lemma v5 (h : RootCtx) : Valid 12 s5 := cut_sound h (by simp) cert5
lemma v6 (h : RootCtx) : Valid 12 s6 := cut_sound h (by simp) cert6
lemma v7 (h : RootCtx) : Valid 12 s7 := cut_sound h (by simp) cert7
lemma v8 (h : RootCtx) : Valid 12 s8 := cut_sound h (by simp) cert8
lemma v9 (h : RootCtx) : Valid 12 s9 := cut_sound h (by simp) cert9
lemma v10 (h : RootCtx) : Valid 12 s10 := cut_sound h (by simp) cert10
lemma v11 (h : RootCtx) : Valid 12 s11 := cut_sound h (by simp) cert11
lemma v12 (h : RootCtx) : Valid 12 s12 := cut_sound h (by simp) cert12
lemma v13 (h : RootCtx) : Valid 12 s13 := cut_sound h (by simp) cert13
lemma v14 (h : RootCtx) : Valid 12 s14 := cut_sound h (by simp) cert14
lemma v15 (h : RootCtx) : Valid 12 s15 := cut_sound h (by simp) cert15
lemma v16 (h : RootCtx) : Valid 12 s16 := cut_sound h (by simp) cert16
lemma v17 (h : RootCtx) : Valid 12 s17 := cut_sound h (by simp) cert17
lemma v18 (h : RootCtx) : Valid 12 s18 := cut_sound h (by simp) cert18
lemma v19 (h : RootCtx) : Valid 12 s19 := cut_sound h (by simp) cert19
lemma v21 (h : RootCtx) : Valid 12 s21 := cut_sound h (by simp) cert21
lemma v22 (h : RootCtx) : Valid 12 s22 := cut_sound h (by simp) cert22
lemma v23 (h : RootCtx) : Valid 12 s23 := cut_sound h (by simp) cert23
lemma v24 (h : RootCtx) : Valid 12 s24 := cut_sound h (by simp) cert24
lemma v25 (h : RootCtx) : Valid 12 s25 := cut_sound h (by simp) cert25
lemma v26 (h : RootCtx) : Valid 12 s26 := cut_sound h (by simp) cert26
lemma v27 (h : RootCtx) : Valid 12 s27 := cut_sound h (by simp) cert27
lemma v28 (h : RootCtx) : Valid 12 s28 := cut_sound h (by simp) cert28
lemma v29 (h : RootCtx) : Valid 12 s29 := cut_sound h (by simp) cert29
lemma v30 (h : RootCtx) : Valid 12 s30 := cut_sound h (by simp) cert30
lemma v31 (h : RootCtx) : Valid 12 s31 := cut_sound h (by simp) cert31
lemma v32 (h : RootCtx) : Valid 12 s32 := cut_sound h (by simp) cert32
lemma v33 (h : RootCtx) : Valid 12 s33 := cut_sound h (by simp) cert33
lemma v34 (h : RootCtx) : Valid 12 s34 := cut_sound h (by simp) cert34
lemma v35 (h : RootCtx) : Valid 12 s35 := cut_sound h (by simp) cert35
lemma v36 (h : RootCtx) : Valid 12 s36 := cut_sound h (by simp) cert36
lemma v37 (h : RootCtx) : Valid 12 s37 := cut_sound h (by simp) cert37
lemma v39 (h : RootCtx) : Valid 12 s39 := cut_sound h (by simp) cert39
lemma v40 (h : RootCtx) : Valid 12 s40 := cut_sound h (by simp) cert40
lemma v41 (h : RootCtx) : Valid 12 s41 := cut_sound h (by simp) cert41
lemma v42 (h : RootCtx) : Valid 12 s42 := cut_sound h (by simp) cert42
lemma v43 (h : RootCtx) : Valid 12 s43 := cut_sound h (by simp) cert43
lemma v44 (h : RootCtx) : Valid 12 s44 := cut_sound h (by simp) cert44
lemma v45 (h : RootCtx) : Valid 12 s45 := cut_sound h (by simp) cert45
lemma v46 (h : RootCtx) : Valid 12 s46 := cut_sound h (by simp) cert46
lemma v47 (h : RootCtx) : Valid 12 s47 := cut_sound h (by simp) cert47
lemma v48 (h : RootCtx) : Valid 12 s48 := cut_sound h (by simp) cert48
lemma v49 (h : RootCtx) : Valid 12 s49 := cut_sound h (by simp) cert49
lemma v50 (h : RootCtx) : Valid 12 s50 := cut_sound h (by simp) cert50
lemma v51 (h : RootCtx) : Valid 12 s51 := cut_sound h (by simp) cert51
lemma v52 (h : RootCtx) : Valid 12 s52 := cut_sound h (by simp) cert52
lemma v53 (h : RootCtx) : Valid 12 s53 := cut_sound h (by simp) cert53
lemma v54 (h : RootCtx) : Valid 12 s54 := cut_sound h (by simp) cert54
lemma v56 (h : RootCtx) : Valid 12 s56 := cut_sound h (by simp) cert56
lemma v57 (h : RootCtx) : Valid 12 s57 := cut_sound h (by simp) cert57
lemma v58 (h : RootCtx) : Valid 12 s58 := cut_sound h (by simp) cert58
lemma v59 (h : RootCtx) : Valid 12 s59 := cut_sound h (by simp) cert59
lemma v60 (h : RootCtx) : Valid 12 s60 := cut_sound h (by simp) cert60
lemma v61 (h : RootCtx) : Valid 12 s61 := cut_sound h (by simp) cert61
lemma v62 (h : RootCtx) : Valid 12 s62 := cut_sound h (by simp) cert62
lemma v63 (h : RootCtx) : Valid 12 s63 := cut_sound h (by simp) cert63
lemma v64 (h : RootCtx) : Valid 12 s64 := cut_sound h (by simp) cert64
lemma v65 (h : RootCtx) : Valid 12 s65 := cut_sound h (by simp) cert65
lemma v66 (h : RootCtx) : Valid 12 s66 := cut_sound h (by simp) cert66
lemma v67 (h : RootCtx) : Valid 12 s67 := cut_sound h (by simp) cert67
lemma v68 (h : RootCtx) : Valid 12 s68 := cut_sound h (by simp) cert68
lemma v69 (h : RootCtx) : Valid 12 s69 := cut_sound h (by simp) cert69
lemma v70 (h : RootCtx) : Valid 12 s70 := cut_sound h (by simp) cert70
lemma v72 (h : RootCtx) : Valid 12 s72 := cut_sound h (by simp) cert72
lemma v73 (h : RootCtx) : Valid 12 s73 := cut_sound h (by simp) cert73
lemma v74 (h : RootCtx) : Valid 12 s74 := cut_sound h (by simp) cert74
lemma v75 (h : RootCtx) : Valid 12 s75 := cut_sound h (by simp) cert75
lemma v76 (h : RootCtx) : Valid 12 s76 := cut_sound h (by simp) cert76
lemma v77 (h : RootCtx) : Valid 12 s77 := cut_sound h (by simp) cert77
lemma v78 (h : RootCtx) : Valid 12 s78 := cut_sound h (by simp) cert78
lemma v79 (h : RootCtx) : Valid 12 s79 := cut_sound h (by simp) cert79
lemma v80 (h : RootCtx) : Valid 12 s80 := cut_sound h (by simp) cert80
lemma v81 (h : RootCtx) : Valid 12 s81 := cut_sound h (by simp) cert81
lemma v82 (h : RootCtx) : Valid 12 s82 := cut_sound h (by simp) cert82
lemma v84 (h : RootCtx) : Valid 12 s84 := cut_sound h (by simp) cert84
lemma v85 (h : RootCtx) : Valid 12 s85 := cut_sound h (by simp) cert85
lemma v86 (h : RootCtx) : Valid 12 s86 := cut_sound h (by simp) cert86
lemma v87 (h : RootCtx) : Valid 12 s87 := cut_sound h (by simp) cert87
lemma v88 (h : RootCtx) : Valid 12 s88 := cut_sound h (by simp) cert88
lemma v89 (h : RootCtx) : Valid 12 s89 := cut_sound h (by simp) cert89
lemma v90 (h : RootCtx) : Valid 12 s90 := cut_sound h (by simp) cert90
lemma v91 (h : RootCtx) : Valid 12 s91 := cut_sound h (by simp) cert91
lemma v92 (h : RootCtx) : Valid 12 s92 := cut_sound h (by simp) cert92
lemma v93 (h : RootCtx) : Valid 12 s93 := cut_sound h (by simp) cert93
lemma v95 (h : RootCtx) : Valid 12 s95 := cut_sound h (by simp) cert95
lemma v96 (h : RootCtx) : Valid 12 s96 := cut_sound h (by simp) cert96
lemma v97 (h : RootCtx) : Valid 12 s97 := cut_sound h (by simp) cert97
lemma v98 (h : RootCtx) : Valid 12 s98 := cut_sound h (by simp) cert98
lemma v99 (h : RootCtx) : Valid 12 s99 := cut_sound h (by simp) cert99
lemma v100 (h : RootCtx) : Valid 12 s100 := cut_sound h (by simp) cert100
lemma v101 (h : RootCtx) : Valid 12 s101 := cut_sound h (by simp) cert101
lemma v103 (h : RootCtx) : Valid 12 s103 := cut_sound h (by simp) cert103
lemma v104 (h : RootCtx) : Valid 12 s104 := cut_sound h (by simp) cert104
lemma v105 (h : RootCtx) : Valid 12 s105 := cut_sound h (by simp) cert105
lemma v106 (h : RootCtx) : Valid 12 s106 := cut_sound h (by simp) cert106
lemma v107 (h : RootCtx) : Valid 12 s107 := cut_sound h (by simp) cert107
lemma v108 (h : RootCtx) : Valid 12 s108 := cut_sound h (by simp) cert108
lemma v110 (h : RootCtx) : Valid 12 s110 := cut_sound h (by simp) cert110
lemma v111 (h : RootCtx) : Valid 12 s111 := cut_sound h (by simp) cert111
lemma v112 (h : RootCtx) : Valid 12 s112 := cut_sound h (by simp) cert112
lemma v114 (h : RootCtx) : Valid 12 s114 := cut_sound h (by simp) cert114
lemma v115 (h : RootCtx) : Valid 12 s115 := cut_sound h (by simp) cert115
lemma v116 (h : RootCtx) : Valid 12 s116 := cut_sound h (by simp) cert116
lemma v117 (h : RootCtx) : Valid 12 s117 := cut_sound h (by simp) cert117
lemma v118 (h : RootCtx) : Valid 12 s118 := cut_sound h (by simp) cert118
lemma v120 (h : RootCtx) : Valid 12 s120 := cut_sound h (by simp) cert120
lemma v121 (h : RootCtx) : Valid 12 s121 := cut_sound h (by simp) cert121
lemma v122 (h : RootCtx) : Valid 12 s122 := cut_sound h (by simp) cert122
lemma v123 (h : RootCtx) : Valid 12 s123 := cut_sound h (by simp) cert123
lemma v125 (h : RootCtx) : Valid 12 s125 := cut_sound h (by simp) cert125
lemma v126 (h : RootCtx) : Valid 12 s126 := cut_sound h (by simp) cert126
lemma v127 (h : RootCtx) : Valid 12 s127 := cut_sound h (by simp) cert127
lemma v128 (h : RootCtx) : Valid 12 s128 := cut_sound h (by simp) cert128
lemma v129 (h : RootCtx) : Valid 12 s129 := cut_sound h (by simp) cert129
lemma v130 (h : RootCtx) : Valid 12 s130 := cut_sound h (by simp) cert130
lemma v132 (h : RootCtx) : Valid 12 s132 := cut_sound h (by simp) cert132
lemma v133 (h : RootCtx) : Valid 12 s133 := cut_sound h (by simp) cert133
lemma v134 (h : RootCtx) : Valid 12 s134 := cut_sound h (by simp) cert134
lemma v135 (h : RootCtx) : Valid 12 s135 := cut_sound h (by simp) cert135
lemma v136 (h : RootCtx) : Valid 12 s136 := cut_sound h (by simp) cert136
lemma v137 (h : RootCtx) : Valid 12 s137 := cut_sound h (by simp) cert137
lemma v139 (h : RootCtx) : Valid 12 s139 := cut_sound h (by simp) cert139
lemma v142 (h : RootCtx) : Valid 12 s142 := cut_sound h (by simp) cert142
lemma v143 (h : RootCtx) : Valid 12 s143 := cut_sound h (by simp) cert143
lemma v144 (h : RootCtx) : Valid 12 s144 := cut_sound h (by simp) cert144
lemma v146 (h : RootCtx) : Valid 12 s146 := cut_sound h (by simp) cert146
lemma v147 (h : RootCtx) : Valid 12 s147 := cut_sound h (by simp) cert147
lemma v149 (h : RootCtx) : Valid 12 s149 := cut_sound h (by simp) cert149
lemma v151 (h : RootCtx) : Valid 12 s151 := cut_sound h (by simp) cert151
lemma v155 (h : RootCtx) : Valid 12 s155 := cut_sound h (by simp) cert155
lemma v156 (h : RootCtx) : Valid 12 s156 := cut_sound h (by simp) cert156
lemma v157 (h : RootCtx) : Valid 12 s157 := cut_sound h (by simp) cert157
lemma v158 (h : RootCtx) : Valid 12 s158 := cut_sound h (by simp) cert158
lemma v159 (h : RootCtx) : Valid 12 s159 := cut_sound h (by simp) cert159
lemma v160 (h : RootCtx) : Valid 12 s160 := cut_sound h (by simp) cert160
lemma v161 (h : RootCtx) : Valid 12 s161 := cut_sound h (by simp) cert161
lemma v162 (h : RootCtx) : Valid 12 s162 := cut_sound h (by simp) cert162
lemma v163 (h : RootCtx) : Valid 12 s163 := cut_sound h (by simp) cert163
lemma v164 (h : RootCtx) : Valid 12 s164 := cut_sound h (by simp) cert164
lemma v165 (h : RootCtx) : Valid 12 s165 := cut_sound h (by simp) cert165
lemma v166 (h : RootCtx) : Valid 12 s166 := cut_sound h (by simp) cert166
lemma v167 (h : RootCtx) : Valid 12 s167 := cut_sound h (by simp) cert167
lemma v168 (h : RootCtx) : Valid 12 s168 := cut_sound h (by simp) cert168
lemma v169 (h : RootCtx) : Valid 12 s169 := cut_sound h (by simp) cert169
lemma v170 (h : RootCtx) : Valid 12 s170 := cut_sound h (by simp) cert170
lemma v171 (h : RootCtx) : Valid 12 s171 := cut_sound h (by simp) cert171
lemma v172 (h : RootCtx) : Valid 12 s172 := cut_sound h (by simp) cert172
lemma v173 (h : RootCtx) : Valid 12 s173 := cut_sound h (by simp) cert173
lemma v174 (h : RootCtx) : Valid 12 s174 := cut_sound h (by simp) cert174
lemma v175 (h : RootCtx) : Valid 12 s175 := cut_sound h (by simp) cert175
lemma v176 (h : RootCtx) : Valid 12 s176 := cut_sound h (by simp) cert176
lemma v177 (h : RootCtx) : Valid 12 s177 := cut_sound h (by simp) cert177
lemma v178 (h : RootCtx) : Valid 12 s178 := cut_sound h (by simp) cert178
lemma v179 (h : RootCtx) : Valid 12 s179 := cut_sound h (by simp) cert179
lemma v180 (h : RootCtx) : Valid 12 s180 := cut_sound h (by simp) cert180
lemma v182 (h : RootCtx) : Valid 12 s182 := cut_sound h (by simp) cert182
lemma v183 (h : RootCtx) : Valid 12 s183 := cut_sound h (by simp) cert183
lemma v184 (h : RootCtx) : Valid 12 s184 := cut_sound h (by simp) cert184
lemma v185 (h : RootCtx) : Valid 12 s185 := cut_sound h (by simp) cert185
lemma v186 (h : RootCtx) : Valid 12 s186 := cut_sound h (by simp) cert186
lemma v187 (h : RootCtx) : Valid 12 s187 := cut_sound h (by simp) cert187
lemma v188 (h : RootCtx) : Valid 12 s188 := cut_sound h (by simp) cert188
lemma v189 (h : RootCtx) : Valid 12 s189 := cut_sound h (by simp) cert189
lemma v190 (h : RootCtx) : Valid 12 s190 := cut_sound h (by simp) cert190
lemma v191 (h : RootCtx) : Valid 12 s191 := cut_sound h (by simp) cert191
lemma v192 (h : RootCtx) : Valid 12 s192 := cut_sound h (by simp) cert192
lemma v193 (h : RootCtx) : Valid 12 s193 := cut_sound h (by simp) cert193
lemma v194 (h : RootCtx) : Valid 12 s194 := cut_sound h (by simp) cert194
lemma v195 (h : RootCtx) : Valid 12 s195 := cut_sound h (by simp) cert195
lemma v196 (h : RootCtx) : Valid 12 s196 := cut_sound h (by simp) cert196
lemma v197 (h : RootCtx) : Valid 12 s197 := cut_sound h (by simp) cert197
lemma v198 (h : RootCtx) : Valid 12 s198 := cut_sound h (by simp) cert198
lemma v199 (h : RootCtx) : Valid 12 s199 := cut_sound h (by simp) cert199
lemma v200 (h : RootCtx) : Valid 12 s200 := cut_sound h (by simp) cert200
lemma v201 (h : RootCtx) : Valid 12 s201 := cut_sound h (by simp) cert201
lemma v202 (h : RootCtx) : Valid 12 s202 := cut_sound h (by simp) cert202
lemma v203 (h : RootCtx) : Valid 12 s203 := cut_sound h (by simp) cert203
lemma v204 (h : RootCtx) : Valid 12 s204 := cut_sound h (by simp) cert204
lemma v205 (h : RootCtx) : Valid 12 s205 := cut_sound h (by simp) cert205
lemma v206 (h : RootCtx) : Valid 12 s206 := cut_sound h (by simp) cert206
lemma v208 (h : RootCtx) : Valid 12 s208 := cut_sound h (by simp) cert208
lemma v209 (h : RootCtx) : Valid 12 s209 := cut_sound h (by simp) cert209
lemma v210 (h : RootCtx) : Valid 12 s210 := cut_sound h (by simp) cert210
lemma v211 (h : RootCtx) : Valid 12 s211 := cut_sound h (by simp) cert211
lemma v212 (h : RootCtx) : Valid 12 s212 := cut_sound h (by simp) cert212
lemma v213 (h : RootCtx) : Valid 12 s213 := cut_sound h (by simp) cert213
lemma v214 (h : RootCtx) : Valid 12 s214 := cut_sound h (by simp) cert214
lemma v215 (h : RootCtx) : Valid 12 s215 := cut_sound h (by simp) cert215
lemma v216 (h : RootCtx) : Valid 12 s216 := cut_sound h (by simp) cert216
lemma v217 (h : RootCtx) : Valid 12 s217 := cut_sound h (by simp) cert217
lemma v218 (h : RootCtx) : Valid 12 s218 := cut_sound h (by simp) cert218
lemma v219 (h : RootCtx) : Valid 12 s219 := cut_sound h (by simp) cert219
lemma v220 (h : RootCtx) : Valid 12 s220 := cut_sound h (by simp) cert220
lemma v221 (h : RootCtx) : Valid 12 s221 := cut_sound h (by simp) cert221
lemma v222 (h : RootCtx) : Valid 12 s222 := cut_sound h (by simp) cert222
lemma v223 (h : RootCtx) : Valid 12 s223 := cut_sound h (by simp) cert223
lemma v224 (h : RootCtx) : Valid 12 s224 := cut_sound h (by simp) cert224
lemma v225 (h : RootCtx) : Valid 12 s225 := cut_sound h (by simp) cert225
lemma v226 (h : RootCtx) : Valid 12 s226 := cut_sound h (by simp) cert226
lemma v227 (h : RootCtx) : Valid 12 s227 := cut_sound h (by simp) cert227
lemma v228 (h : RootCtx) : Valid 12 s228 := cut_sound h (by simp) cert228
lemma v229 (h : RootCtx) : Valid 12 s229 := cut_sound h (by simp) cert229
lemma v230 (h : RootCtx) : Valid 12 s230 := cut_sound h (by simp) cert230
lemma v231 (h : RootCtx) : Valid 12 s231 := cut_sound h (by simp) cert231
lemma v233 (h : RootCtx) : Valid 12 s233 := cut_sound h (by simp) cert233
lemma v234 (h : RootCtx) : Valid 12 s234 := cut_sound h (by simp) cert234
lemma v235 (h : RootCtx) : Valid 12 s235 := cut_sound h (by simp) cert235
lemma v236 (h : RootCtx) : Valid 12 s236 := cut_sound h (by simp) cert236
lemma v237 (h : RootCtx) : Valid 12 s237 := cut_sound h (by simp) cert237
lemma v238 (h : RootCtx) : Valid 12 s238 := cut_sound h (by simp) cert238
lemma v239 (h : RootCtx) : Valid 12 s239 := cut_sound h (by simp) cert239
lemma v240 (h : RootCtx) : Valid 12 s240 := cut_sound h (by simp) cert240
lemma v241 (h : RootCtx) : Valid 12 s241 := cut_sound h (by simp) cert241
lemma v242 (h : RootCtx) : Valid 12 s242 := cut_sound h (by simp) cert242
lemma v243 (h : RootCtx) : Valid 12 s243 := cut_sound h (by simp) cert243
lemma v244 (h : RootCtx) : Valid 12 s244 := cut_sound h (by simp) cert244
lemma v245 (h : RootCtx) : Valid 12 s245 := cut_sound h (by simp) cert245
lemma v246 (h : RootCtx) : Valid 12 s246 := cut_sound h (by simp) cert246
lemma v247 (h : RootCtx) : Valid 12 s247 := cut_sound h (by simp) cert247
lemma v248 (h : RootCtx) : Valid 12 s248 := cut_sound h (by simp) cert248
lemma v249 (h : RootCtx) : Valid 12 s249 := cut_sound h (by simp) cert249
lemma v250 (h : RootCtx) : Valid 12 s250 := cut_sound h (by simp) cert250
lemma v251 (h : RootCtx) : Valid 12 s251 := cut_sound h (by simp) cert251
lemma v252 (h : RootCtx) : Valid 12 s252 := cut_sound h (by simp) cert252
lemma v253 (h : RootCtx) : Valid 12 s253 := cut_sound h (by simp) cert253
lemma v254 (h : RootCtx) : Valid 12 s254 := cut_sound h (by simp) cert254
lemma v255 (h : RootCtx) : Valid 12 s255 := cut_sound h (by simp) cert255
lemma v257 (h : RootCtx) : Valid 12 s257 := cut_sound h (by simp) cert257
lemma v258 (h : RootCtx) : Valid 12 s258 := cut_sound h (by simp) cert258
lemma v259 (h : RootCtx) : Valid 12 s259 := cut_sound h (by simp) cert259
lemma v260 (h : RootCtx) : Valid 12 s260 := cut_sound h (by simp) cert260
lemma v261 (h : RootCtx) : Valid 12 s261 := cut_sound h (by simp) cert261
lemma v262 (h : RootCtx) : Valid 12 s262 := cut_sound h (by simp) cert262
lemma v263 (h : RootCtx) : Valid 12 s263 := cut_sound h (by simp) cert263
lemma v264 (h : RootCtx) : Valid 12 s264 := cut_sound h (by simp) cert264
lemma v265 (h : RootCtx) : Valid 12 s265 := cut_sound h (by simp) cert265
lemma v266 (h : RootCtx) : Valid 12 s266 := cut_sound h (by simp) cert266
lemma v267 (h : RootCtx) : Valid 12 s267 := cut_sound h (by simp) cert267
lemma v268 (h : RootCtx) : Valid 12 s268 := cut_sound h (by simp) cert268
lemma v269 (h : RootCtx) : Valid 12 s269 := cut_sound h (by simp) cert269
lemma v270 (h : RootCtx) : Valid 12 s270 := cut_sound h (by simp) cert270
lemma v271 (h : RootCtx) : Valid 12 s271 := cut_sound h (by simp) cert271
lemma v272 (h : RootCtx) : Valid 12 s272 := cut_sound h (by simp) cert272
lemma v273 (h : RootCtx) : Valid 12 s273 := cut_sound h (by simp) cert273
lemma v274 (h : RootCtx) : Valid 12 s274 := cut_sound h (by simp) cert274
lemma v275 (h : RootCtx) : Valid 12 s275 := cut_sound h (by simp) cert275
lemma v276 (h : RootCtx) : Valid 12 s276 := cut_sound h (by simp) cert276
lemma v277 (h : RootCtx) : Valid 12 s277 := cut_sound h (by simp) cert277
lemma v278 (h : RootCtx) : Valid 12 s278 := cut_sound h (by simp) cert278
lemma v279 (h : RootCtx) : Valid 12 s279 := cut_sound h (by simp) cert279
lemma v280 (h : RootCtx) : Valid 12 s280 := cut_sound h (by simp) cert280
lemma v281 (h : RootCtx) : Valid 12 s281 := cut_sound h (by simp) cert281
lemma v282 (h : RootCtx) : Valid 12 s282 := cut_sound h (by simp) cert282
lemma v283 (h : RootCtx) : Valid 12 s283 := cut_sound h (by simp) cert283
lemma v284 (h : RootCtx) : Valid 12 s284 := cut_sound h (by simp) cert284
lemma v285 (h : RootCtx) : Valid 12 s285 := cut_sound h (by simp) cert285
lemma v286 (h : RootCtx) : Valid 12 s286 := cut_sound h (by simp) cert286
lemma v288 (h : RootCtx) : Valid 12 s288 := cut_sound h (by simp) cert288
lemma v289 (h : RootCtx) : Valid 12 s289 := cut_sound h (by simp) cert289
lemma v290 (h : RootCtx) : Valid 12 s290 := cut_sound h (by simp) cert290
lemma v291 (h : RootCtx) : Valid 12 s291 := cut_sound h (by simp) cert291
lemma v292 (h : RootCtx) : Valid 12 s292 := cut_sound h (by simp) cert292
lemma v293 (h : RootCtx) : Valid 12 s293 := cut_sound h (by simp) cert293
lemma v294 (h : RootCtx) : Valid 12 s294 := cut_sound h (by simp) cert294
lemma v295 (h : RootCtx) : Valid 12 s295 := cut_sound h (by simp) cert295
lemma v296 (h : RootCtx) : Valid 12 s296 := cut_sound h (by simp) cert296
lemma v297 (h : RootCtx) : Valid 12 s297 := cut_sound h (by simp) cert297
lemma v298 (h : RootCtx) : Valid 12 s298 := cut_sound h (by simp) cert298
lemma v299 (h : RootCtx) : Valid 12 s299 := cut_sound h (by simp) cert299
lemma v300 (h : RootCtx) : Valid 12 s300 := cut_sound h (by simp) cert300
lemma v301 (h : RootCtx) : Valid 12 s301 := cut_sound h (by simp) cert301
lemma v302 (h : RootCtx) : Valid 12 s302 := cut_sound h (by simp) cert302
lemma v303 (h : RootCtx) : Valid 12 s303 := cut_sound h (by simp) cert303
lemma v304 (h : RootCtx) : Valid 12 s304 := cut_sound h (by simp) cert304
lemma v305 (h : RootCtx) : Valid 12 s305 := cut_sound h (by simp) cert305
lemma v306 (h : RootCtx) : Valid 12 s306 := cut_sound h (by simp) cert306
lemma v307 (h : RootCtx) : Valid 12 s307 := cut_sound h (by simp) cert307
lemma v308 (h : RootCtx) : Valid 12 s308 := cut_sound h (by simp) cert308
lemma v309 (h : RootCtx) : Valid 12 s309 := cut_sound h (by simp) cert309
lemma v310 (h : RootCtx) : Valid 12 s310 := cut_sound h (by simp) cert310
lemma v311 (h : RootCtx) : Valid 12 s311 := cut_sound h (by simp) cert311
lemma v312 (h : RootCtx) : Valid 12 s312 := cut_sound h (by simp) cert312
lemma v313 (h : RootCtx) : Valid 12 s313 := cut_sound h (by simp) cert313
lemma v314 (h : RootCtx) : Valid 12 s314 := cut_sound h (by simp) cert314
lemma v315 (h : RootCtx) : Valid 12 s315 := cut_sound h (by simp) cert315
lemma v316 (h : RootCtx) : Valid 12 s316 := cut_sound h (by simp) cert316
lemma v318 (h : RootCtx) : Valid 12 s318 := cut_sound h (by simp) cert318
lemma v319 (h : RootCtx) : Valid 12 s319 := cut_sound h (by simp) cert319
lemma v320 (h : RootCtx) : Valid 12 s320 := cut_sound h (by simp) cert320
lemma v321 (h : RootCtx) : Valid 12 s321 := cut_sound h (by simp) cert321
lemma v322 (h : RootCtx) : Valid 12 s322 := cut_sound h (by simp) cert322
lemma v323 (h : RootCtx) : Valid 12 s323 := cut_sound h (by simp) cert323
lemma v324 (h : RootCtx) : Valid 12 s324 := cut_sound h (by simp) cert324
lemma v325 (h : RootCtx) : Valid 12 s325 := cut_sound h (by simp) cert325
lemma v326 (h : RootCtx) : Valid 12 s326 := cut_sound h (by simp) cert326
lemma v327 (h : RootCtx) : Valid 12 s327 := cut_sound h (by simp) cert327
lemma v328 (h : RootCtx) : Valid 12 s328 := cut_sound h (by simp) cert328
lemma v329 (h : RootCtx) : Valid 12 s329 := cut_sound h (by simp) cert329
lemma v330 (h : RootCtx) : Valid 12 s330 := cut_sound h (by simp) cert330
lemma v331 (h : RootCtx) : Valid 12 s331 := cut_sound h (by simp) cert331
lemma v332 (h : RootCtx) : Valid 12 s332 := cut_sound h (by simp) cert332
lemma v333 (h : RootCtx) : Valid 12 s333 := cut_sound h (by simp) cert333
lemma v334 (h : RootCtx) : Valid 12 s334 := cut_sound h (by simp) cert334
lemma v335 (h : RootCtx) : Valid 12 s335 := cut_sound h (by simp) cert335
lemma v336 (h : RootCtx) : Valid 12 s336 := cut_sound h (by simp) cert336
lemma v337 (h : RootCtx) : Valid 12 s337 := cut_sound h (by simp) cert337
lemma v339 (h : RootCtx) : Valid 12 s339 := cut_sound h (by simp) cert339
lemma v340 (h : RootCtx) : Valid 12 s340 := cut_sound h (by simp) cert340
lemma v341 (h : RootCtx) : Valid 12 s341 := cut_sound h (by simp) cert341
lemma v342 (h : RootCtx) : Valid 12 s342 := cut_sound h (by simp) cert342
lemma v343 (h : RootCtx) : Valid 12 s343 := cut_sound h (by simp) cert343
lemma v344 (h : RootCtx) : Valid 12 s344 := cut_sound h (by simp) cert344
lemma v345 (h : RootCtx) : Valid 12 s345 := cut_sound h (by simp) cert345
lemma v346 (h : RootCtx) : Valid 12 s346 := cut_sound h (by simp) cert346
lemma v347 (h : RootCtx) : Valid 12 s347 := cut_sound h (by simp) cert347
lemma v348 (h : RootCtx) : Valid 12 s348 := cut_sound h (by simp) cert348
lemma v349 (h : RootCtx) : Valid 12 s349 := cut_sound h (by simp) cert349
lemma v350 (h : RootCtx) : Valid 12 s350 := cut_sound h (by simp) cert350
lemma v351 (h : RootCtx) : Valid 12 s351 := cut_sound h (by simp) cert351
lemma v352 (h : RootCtx) : Valid 12 s352 := cut_sound h (by simp) cert352
lemma v353 (h : RootCtx) : Valid 12 s353 := cut_sound h (by simp) cert353
lemma v354 (h : RootCtx) : Valid 12 s354 := cut_sound h (by simp) cert354
lemma v355 (h : RootCtx) : Valid 12 s355 := cut_sound h (by simp) cert355
lemma v356 (h : RootCtx) : Valid 12 s356 := cut_sound h (by simp) cert356
lemma v357 (h : RootCtx) : Valid 12 s357 := cut_sound h (by simp) cert357
lemma v359 (h : RootCtx) : Valid 12 s359 := cut_sound h (by simp) cert359
lemma v360 (h : RootCtx) : Valid 12 s360 := cut_sound h (by simp) cert360
lemma v361 (h : RootCtx) : Valid 12 s361 := cut_sound h (by simp) cert361
lemma v362 (h : RootCtx) : Valid 12 s362 := cut_sound h (by simp) cert362
lemma v363 (h : RootCtx) : Valid 12 s363 := cut_sound h (by simp) cert363
lemma v364 (h : RootCtx) : Valid 12 s364 := cut_sound h (by simp) cert364
lemma v365 (h : RootCtx) : Valid 12 s365 := cut_sound h (by simp) cert365
lemma v366 (h : RootCtx) : Valid 12 s366 := cut_sound h (by simp) cert366
lemma v367 (h : RootCtx) : Valid 12 s367 := cut_sound h (by simp) cert367
lemma v368 (h : RootCtx) : Valid 12 s368 := cut_sound h (by simp) cert368
lemma v369 (h : RootCtx) : Valid 12 s369 := cut_sound h (by simp) cert369
lemma v370 (h : RootCtx) : Valid 12 s370 := cut_sound h (by simp) cert370
lemma v371 (h : RootCtx) : Valid 12 s371 := cut_sound h (by simp) cert371
lemma v372 (h : RootCtx) : Valid 12 s372 := cut_sound h (by simp) cert372
lemma v373 (h : RootCtx) : Valid 12 s373 := cut_sound h (by simp) cert373
lemma v374 (h : RootCtx) : Valid 12 s374 := cut_sound h (by simp) cert374
lemma v376 (h : RootCtx) : Valid 12 s376 := cut_sound h (by simp) cert376
lemma v377 (h : RootCtx) : Valid 12 s377 := cut_sound h (by simp) cert377
lemma v378 (h : RootCtx) : Valid 12 s378 := cut_sound h (by simp) cert378
lemma v379 (h : RootCtx) : Valid 12 s379 := cut_sound h (by simp) cert379
lemma v380 (h : RootCtx) : Valid 12 s380 := cut_sound h (by simp) cert380
lemma v381 (h : RootCtx) : Valid 12 s381 := cut_sound h (by simp) cert381
lemma v382 (h : RootCtx) : Valid 12 s382 := cut_sound h (by simp) cert382
lemma v383 (h : RootCtx) : Valid 12 s383 := cut_sound h (by simp) cert383
lemma v384 (h : RootCtx) : Valid 12 s384 := cut_sound h (by simp) cert384
lemma v385 (h : RootCtx) : Valid 12 s385 := cut_sound h (by simp) cert385
lemma v386 (h : RootCtx) : Valid 12 s386 := cut_sound h (by simp) cert386
lemma v387 (h : RootCtx) : Valid 12 s387 := cut_sound h (by simp) cert387
lemma v388 (h : RootCtx) : Valid 12 s388 := cut_sound h (by simp) cert388
lemma v389 (h : RootCtx) : Valid 12 s389 := cut_sound h (by simp) cert389
lemma v390 (h : RootCtx) : Valid 12 s390 := cut_sound h (by simp) cert390
lemma v392 (h : RootCtx) : Valid 12 s392 := cut_sound h (by simp) cert392
lemma v393 (h : RootCtx) : Valid 12 s393 := cut_sound h (by simp) cert393
lemma v394 (h : RootCtx) : Valid 12 s394 := cut_sound h (by simp) cert394
lemma v395 (h : RootCtx) : Valid 12 s395 := cut_sound h (by simp) cert395
lemma v396 (h : RootCtx) : Valid 12 s396 := cut_sound h (by simp) cert396
lemma v397 (h : RootCtx) : Valid 12 s397 := cut_sound h (by simp) cert397
lemma v398 (h : RootCtx) : Valid 12 s398 := cut_sound h (by simp) cert398
lemma v399 (h : RootCtx) : Valid 12 s399 := cut_sound h (by simp) cert399
lemma v400 (h : RootCtx) : Valid 12 s400 := cut_sound h (by simp) cert400
lemma v401 (h : RootCtx) : Valid 12 s401 := cut_sound h (by simp) cert401
lemma v402 (h : RootCtx) : Valid 12 s402 := cut_sound h (by simp) cert402
lemma v403 (h : RootCtx) : Valid 12 s403 := cut_sound h (by simp) cert403
lemma v404 (h : RootCtx) : Valid 12 s404 := cut_sound h (by simp) cert404
lemma v405 (h : RootCtx) : Valid 12 s405 := cut_sound h (by simp) cert405
lemma v406 (h : RootCtx) : Valid 12 s406 := cut_sound h (by simp) cert406
lemma v407 (h : RootCtx) : Valid 12 s407 := cut_sound h (by simp) cert407
lemma v409 (h : RootCtx) : Valid 12 s409 := cut_sound h (by simp) cert409
lemma v410 (h : RootCtx) : Valid 12 s410 := cut_sound h (by simp) cert410
lemma v411 (h : RootCtx) : Valid 12 s411 := cut_sound h (by simp) cert411
lemma v412 (h : RootCtx) : Valid 12 s412 := cut_sound h (by simp) cert412
lemma v413 (h : RootCtx) : Valid 12 s413 := cut_sound h (by simp) cert413
lemma v414 (h : RootCtx) : Valid 12 s414 := cut_sound h (by simp) cert414
lemma v415 (h : RootCtx) : Valid 12 s415 := cut_sound h (by simp) cert415
lemma v416 (h : RootCtx) : Valid 12 s416 := cut_sound h (by simp) cert416
lemma v417 (h : RootCtx) : Valid 12 s417 := cut_sound h (by simp) cert417
lemma v418 (h : RootCtx) : Valid 12 s418 := cut_sound h (by simp) cert418
lemma v419 (h : RootCtx) : Valid 12 s419 := cut_sound h (by simp) cert419
lemma v420 (h : RootCtx) : Valid 12 s420 := cut_sound h (by simp) cert420
lemma v421 (h : RootCtx) : Valid 12 s421 := cut_sound h (by simp) cert421
lemma v422 (h : RootCtx) : Valid 12 s422 := cut_sound h (by simp) cert422
lemma v423 (h : RootCtx) : Valid 12 s423 := cut_sound h (by simp) cert423
lemma v425 (h : RootCtx) : Valid 12 s425 := cut_sound h (by simp) cert425
lemma v426 (h : RootCtx) : Valid 12 s426 := cut_sound h (by simp) cert426
lemma v427 (h : RootCtx) : Valid 12 s427 := cut_sound h (by simp) cert427
lemma v428 (h : RootCtx) : Valid 12 s428 := cut_sound h (by simp) cert428
lemma v429 (h : RootCtx) : Valid 12 s429 := cut_sound h (by simp) cert429
lemma v430 (h : RootCtx) : Valid 12 s430 := cut_sound h (by simp) cert430
lemma v431 (h : RootCtx) : Valid 12 s431 := cut_sound h (by simp) cert431
lemma v432 (h : RootCtx) : Valid 12 s432 := cut_sound h (by simp) cert432
lemma v433 (h : RootCtx) : Valid 12 s433 := cut_sound h (by simp) cert433
lemma v434 (h : RootCtx) : Valid 12 s434 := cut_sound h (by simp) cert434
lemma v435 (h : RootCtx) : Valid 12 s435 := cut_sound h (by simp) cert435
lemma v436 (h : RootCtx) : Valid 12 s436 := cut_sound h (by simp) cert436
lemma v437 (h : RootCtx) : Valid 12 s437 := cut_sound h (by simp) cert437
lemma v438 (h : RootCtx) : Valid 12 s438 := cut_sound h (by simp) cert438
lemma v440 (h : RootCtx) : Valid 12 s440 := cut_sound h (by simp) cert440
lemma v441 (h : RootCtx) : Valid 12 s441 := cut_sound h (by simp) cert441
lemma v442 (h : RootCtx) : Valid 12 s442 := cut_sound h (by simp) cert442
lemma v443 (h : RootCtx) : Valid 12 s443 := cut_sound h (by simp) cert443
lemma v444 (h : RootCtx) : Valid 12 s444 := cut_sound h (by simp) cert444
lemma v445 (h : RootCtx) : Valid 12 s445 := cut_sound h (by simp) cert445
lemma v446 (h : RootCtx) : Valid 12 s446 := cut_sound h (by simp) cert446
lemma v447 (h : RootCtx) : Valid 12 s447 := cut_sound h (by simp) cert447
lemma v448 (h : RootCtx) : Valid 12 s448 := cut_sound h (by simp) cert448
lemma v449 (h : RootCtx) : Valid 12 s449 := cut_sound h (by simp) cert449
lemma v450 (h : RootCtx) : Valid 12 s450 := cut_sound h (by simp) cert450
lemma v451 (h : RootCtx) : Valid 12 s451 := cut_sound h (by simp) cert451
lemma v452 (h : RootCtx) : Valid 12 s452 := cut_sound h (by simp) cert452
lemma v454 (h : RootCtx) : Valid 12 s454 := cut_sound h (by simp) cert454
lemma v455 (h : RootCtx) : Valid 12 s455 := cut_sound h (by simp) cert455
lemma v456 (h : RootCtx) : Valid 12 s456 := cut_sound h (by simp) cert456
lemma v457 (h : RootCtx) : Valid 12 s457 := cut_sound h (by simp) cert457
lemma v458 (h : RootCtx) : Valid 12 s458 := cut_sound h (by simp) cert458
lemma v459 (h : RootCtx) : Valid 12 s459 := cut_sound h (by simp) cert459
lemma v460 (h : RootCtx) : Valid 12 s460 := cut_sound h (by simp) cert460
lemma v461 (h : RootCtx) : Valid 12 s461 := cut_sound h (by simp) cert461
lemma v462 (h : RootCtx) : Valid 12 s462 := cut_sound h (by simp) cert462
lemma v463 (h : RootCtx) : Valid 12 s463 := cut_sound h (by simp) cert463
lemma v465 (h : RootCtx) : Valid 12 s465 := cut_sound h (by simp) cert465
lemma v466 (h : RootCtx) : Valid 12 s466 := cut_sound h (by simp) cert466
lemma v467 (h : RootCtx) : Valid 12 s467 := cut_sound h (by simp) cert467
lemma v468 (h : RootCtx) : Valid 12 s468 := cut_sound h (by simp) cert468
lemma v469 (h : RootCtx) : Valid 12 s469 := cut_sound h (by simp) cert469
lemma v470 (h : RootCtx) : Valid 12 s470 := cut_sound h (by simp) cert470
lemma v471 (h : RootCtx) : Valid 12 s471 := cut_sound h (by simp) cert471
lemma v472 (h : RootCtx) : Valid 12 s472 := cut_sound h (by simp) cert472
lemma v473 (h : RootCtx) : Valid 12 s473 := cut_sound h (by simp) cert473
lemma v474 (h : RootCtx) : Valid 12 s474 := cut_sound h (by simp) cert474
lemma v475 (h : RootCtx) : Valid 12 s475 := cut_sound h (by simp) cert475
lemma v476 (h : RootCtx) : Valid 12 s476 := cut_sound h (by simp) cert476
lemma v478 (h : RootCtx) : Valid 12 s478 := cut_sound h (by simp) cert478
lemma v479 (h : RootCtx) : Valid 12 s479 := cut_sound h (by simp) cert479
lemma v480 (h : RootCtx) : Valid 12 s480 := cut_sound h (by simp) cert480
lemma v481 (h : RootCtx) : Valid 12 s481 := cut_sound h (by simp) cert481
lemma v483 (h : RootCtx) : Valid 12 s483 := cut_sound h (by simp) cert483
lemma v484 (h : RootCtx) : Valid 12 s484 := cut_sound h (by simp) cert484
lemma v485 (h : RootCtx) : Valid 12 s485 := cut_sound h (by simp) cert485
lemma v486 (h : RootCtx) : Valid 12 s486 := cut_sound h (by simp) cert486
lemma v488 (h : RootCtx) : Valid 12 s488 := cut_sound h (by simp) cert488
lemma v489 (h : RootCtx) : Valid 12 s489 := cut_sound h (by simp) cert489
lemma v490 (h : RootCtx) : Valid 12 s490 := cut_sound h (by simp) cert490
lemma v491 (h : RootCtx) : Valid 12 s491 := cut_sound h (by simp) cert491
lemma v493 (h : RootCtx) : Valid 12 s493 := cut_sound h (by simp) cert493
lemma v494 (h : RootCtx) : Valid 12 s494 := cut_sound h (by simp) cert494
lemma v495 (h : RootCtx) : Valid 12 s495 := cut_sound h (by simp) cert495
lemma v496 (h : RootCtx) : Valid 12 s496 := cut_sound h (by simp) cert496
lemma v498 (h : RootCtx) : Valid 12 s498 := cut_sound h (by simp) cert498
lemma v499 (h : RootCtx) : Valid 12 s499 := cut_sound h (by simp) cert499
lemma v500 (h : RootCtx) : Valid 12 s500 := cut_sound h (by simp) cert500
lemma v501 (h : RootCtx) : Valid 12 s501 := cut_sound h (by simp) cert501
lemma v502 (h : RootCtx) : Valid 12 s502 := cut_sound h (by simp) cert502
lemma v503 (h : RootCtx) : Valid 12 s503 := cut_sound h (by simp) cert503
lemma v504 (h : RootCtx) : Valid 12 s504 := cut_sound h (by simp) cert504
lemma v505 (h : RootCtx) : Valid 12 s505 := cut_sound h (by simp) cert505
lemma v507 (h : RootCtx) : Valid 12 s507 := cut_sound h (by simp) cert507
lemma v508 (h : RootCtx) : Valid 12 s508 := cut_sound h (by simp) cert508
lemma v509 (h : RootCtx) : Valid 12 s509 := cut_sound h (by simp) cert509
lemma v510 (h : RootCtx) : Valid 12 s510 := cut_sound h (by simp) cert510
lemma v511 (h : RootCtx) : Valid 12 s511 := cut_sound h (by simp) cert511
lemma v512 (h : RootCtx) : Valid 12 s512 := cut_sound h (by simp) cert512
lemma v513 (h : RootCtx) : Valid 12 s513 := cut_sound h (by simp) cert513
lemma v514 (h : RootCtx) : Valid 12 s514 := cut_sound h (by simp) cert514
lemma v516 (h : RootCtx) : Valid 12 s516 := cut_sound h (by simp) cert516
lemma v517 (h : RootCtx) : Valid 12 s517 := cut_sound h (by simp) cert517
lemma v518 (h : RootCtx) : Valid 12 s518 := cut_sound h (by simp) cert518
lemma v519 (h : RootCtx) : Valid 12 s519 := cut_sound h (by simp) cert519
lemma v520 (h : RootCtx) : Valid 12 s520 := cut_sound h (by simp) cert520
lemma v521 (h : RootCtx) : Valid 12 s521 := cut_sound h (by simp) cert521
lemma v522 (h : RootCtx) : Valid 12 s522 := cut_sound h (by simp) cert522
lemma v523 (h : RootCtx) : Valid 12 s523 := cut_sound h (by simp) cert523
lemma v525 (h : RootCtx) : Valid 12 s525 := cut_sound h (by simp) cert525
lemma v526 (h : RootCtx) : Valid 12 s526 := cut_sound h (by simp) cert526
lemma v527 (h : RootCtx) : Valid 12 s527 := cut_sound h (by simp) cert527
lemma v528 (h : RootCtx) : Valid 12 s528 := cut_sound h (by simp) cert528
lemma v529 (h : RootCtx) : Valid 12 s529 := cut_sound h (by simp) cert529
lemma v530 (h : RootCtx) : Valid 12 s530 := cut_sound h (by simp) cert530
lemma v531 (h : RootCtx) : Valid 12 s531 := cut_sound h (by simp) cert531
lemma v532 (h : RootCtx) : Valid 12 s532 := cut_sound h (by simp) cert532
lemma v534 (h : RootCtx) : Valid 12 s534 := cut_sound h (by simp) cert534
lemma v535 (h : RootCtx) : Valid 12 s535 := cut_sound h (by simp) cert535
lemma v536 (h : RootCtx) : Valid 12 s536 := cut_sound h (by simp) cert536
lemma v537 (h : RootCtx) : Valid 12 s537 := cut_sound h (by simp) cert537
lemma v538 (h : RootCtx) : Valid 12 s538 := cut_sound h (by simp) cert538
lemma v539 (h : RootCtx) : Valid 12 s539 := cut_sound h (by simp) cert539
lemma v541 (h : RootCtx) : Valid 12 s541 := cut_sound h (by simp) cert541
lemma v542 (h : RootCtx) : Valid 12 s542 := cut_sound h (by simp) cert542
lemma v543 (h : RootCtx) : Valid 12 s543 := cut_sound h (by simp) cert543
lemma v544 (h : RootCtx) : Valid 12 s544 := cut_sound h (by simp) cert544
lemma v545 (h : RootCtx) : Valid 12 s545 := cut_sound h (by simp) cert545
lemma v546 (h : RootCtx) : Valid 12 s546 := cut_sound h (by simp) cert546
lemma v548 (h : RootCtx) : Valid 12 s548 := cut_sound h (by simp) cert548
lemma v549 (h : RootCtx) : Valid 12 s549 := cut_sound h (by simp) cert549
lemma v550 (h : RootCtx) : Valid 12 s550 := cut_sound h (by simp) cert550
lemma v551 (h : RootCtx) : Valid 12 s551 := cut_sound h (by simp) cert551
lemma v553 (h : RootCtx) : Valid 12 s553 := cut_sound h (by simp) cert553
lemma v554 (h : RootCtx) : Valid 12 s554 := cut_sound h (by simp) cert554
lemma v555 (h : RootCtx) : Valid 12 s555 := cut_sound h (by simp) cert555
lemma v556 (h : RootCtx) : Valid 12 s556 := cut_sound h (by simp) cert556
lemma v558 (h : RootCtx) : Valid 12 s558 := cut_sound h (by simp) cert558
lemma v559 (h : RootCtx) : Valid 12 s559 := cut_sound h (by simp) cert559
lemma v560 (h : RootCtx) : Valid 12 s560 := cut_sound h (by simp) cert560
lemma v561 (h : RootCtx) : Valid 12 s561 := cut_sound h (by simp) cert561
lemma v563 (h : RootCtx) : Valid 12 s563 := cut_sound h (by simp) cert563
lemma v564 (h : RootCtx) : Valid 12 s564 := cut_sound h (by simp) cert564
lemma v565 (h : RootCtx) : Valid 12 s565 := cut_sound h (by simp) cert565
lemma v566 (h : RootCtx) : Valid 12 s566 := cut_sound h (by simp) cert566
lemma v568 (h : RootCtx) : Valid 12 s568 := cut_sound h (by simp) cert568
lemma v569 (h : RootCtx) : Valid 12 s569 := cut_sound h (by simp) cert569
lemma v570 (h : RootCtx) : Valid 12 s570 := cut_sound h (by simp) cert570
lemma v571 (h : RootCtx) : Valid 12 s571 := cut_sound h (by simp) cert571
lemma v572 (h : RootCtx) : Valid 12 s572 := cut_sound h (by simp) cert572
lemma v574 (h : RootCtx) : Valid 12 s574 := cut_sound h (by simp) cert574
lemma v575 (h : RootCtx) : Valid 12 s575 := cut_sound h (by simp) cert575
lemma v576 (h : RootCtx) : Valid 12 s576 := cut_sound h (by simp) cert576
lemma v577 (h : RootCtx) : Valid 12 s577 := cut_sound h (by simp) cert577
lemma v579 (h : RootCtx) : Valid 12 s579 := cut_sound h (by simp) cert579
lemma v580 (h : RootCtx) : Valid 12 s580 := cut_sound h (by simp) cert580
lemma v581 (h : RootCtx) : Valid 12 s581 := cut_sound h (by simp) cert581
lemma v582 (h : RootCtx) : Valid 12 s582 := cut_sound h (by simp) cert582
lemma v584 (h : RootCtx) : Valid 12 s584 := cut_sound h (by simp) cert584
lemma v585 (h : RootCtx) : Valid 12 s585 := cut_sound h (by simp) cert585
lemma v586 (h : RootCtx) : Valid 12 s586 := cut_sound h (by simp) cert586
lemma v588 (h : RootCtx) : Valid 12 s588 := cut_sound h (by simp) cert588
lemma v589 (h : RootCtx) : Valid 12 s589 := cut_sound h (by simp) cert589
lemma v591 (h : RootCtx) : Valid 12 s591 := cut_sound h (by simp) cert591
lemma v592 (h : RootCtx) : Valid 12 s592 := cut_sound h (by simp) cert592
lemma v1 (h : RootCtx) : Valid 13 s1 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v2 h, v3 h, v4 h, v5 h, v6 h, v7 h, v8 h, v9 h, v10 h, v11 h, v12 h, v13 h, v14 h, v15 h, v16 h, v17 h, v18 h, v19 h, by simp⟩) cert1
lemma v20 (h : RootCtx) : Valid 13 s20 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v21 h, v22 h, v23 h, v24 h, v25 h, v26 h, v8 h, v27 h, v28 h, v29 h, v30 h, v31 h, v32 h, v33 h, v34 h, v35 h, v36 h, v37 h, by simp⟩) cert20
lemma v38 (h : RootCtx) : Valid 13 s38 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v39 h, v40 h, v41 h, v24 h, v42 h, v43 h, v44 h, v9 h, v45 h, v46 h, v47 h, v48 h, v49 h, v50 h, v51 h, v52 h, v53 h, v54 h, by simp⟩) cert38
lemma v55 (h : RootCtx) : Valid 13 s55 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v56 h, v57 h, v58 h, v5 h, v59 h, v60 h, v44 h, v27 h, v61 h, v62 h, v63 h, v64 h, v65 h, v66 h, v67 h, v68 h, v69 h, v70 h, by simp⟩) cert55
lemma v71 (h : RootCtx) : Valid 13 s71 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v72 h, v73 h, v3 h, v40 h, v26 h, v60 h, v74 h, v75 h, v15 h, v50 h, v76 h, v77 h, v78 h, v79 h, v80 h, v18 h, v53 h, v81 h, v82 h, by simp⟩) cert71
lemma v83 (h : RootCtx) : Valid 13 s83 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v84 h, v85 h, v22 h, v57 h, v7 h, v43 h, v74 h, v86 h, v87 h, v33 h, v88 h, v66 h, v89 h, v90 h, v91 h, v36 h, v69 h, v92 h, v93 h, by simp⟩) cert83
lemma v94 (h : RootCtx) : Valid 13 s94 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v72 h, v84 h, v42 h, v59 h, v8 h, v95 h, v96 h, v97 h, v98 h, v14 h, v32 h, v78 h, v89 h, v99 h, v100 h, v81 h, v92 h, v101 h, by simp⟩) cert94
lemma v102 (h : RootCtx) : Valid 13 s102 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v73 h, v85 h, v6 h, v25 h, v44 h, v95 h, v103 h, v104 h, v105 h, v49 h, v65 h, v79 h, v90 h, v106 h, v107 h, v82 h, v93 h, v108 h, by simp⟩) cert102
lemma v109 (h : RootCtx) : Valid 13 s109 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v4 h, v23 h, v41 h, v58 h, v75 h, v86 h, v96 h, v103 h, v110 h, v111 h, v16 h, v51 h, v34 h, v67 h, v112 h, by simp⟩) cert109
lemma v113 (h : RootCtx) : Valid 13 s113 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v114 h, v11 h, v62 h, v115 h, v116 h, v117 h, v110 h, v118 h, by simp⟩) cert113
lemma v119 (h : RootCtx) : Valid 13 s119 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v114 h, v29 h, v46 h, v120 h, v121 h, v122 h, v111 h, v123 h, by simp⟩) cert119
lemma v124 (h : RootCtx) : Valid 13 s124 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v122 h, v30 h, v47 h, v112 h, v81 h, v93 h, v125 h, v126 h, v127 h, v128 h, v129 h, v130 h, by simp⟩) cert124
lemma v131 (h : RootCtx) : Valid 13 s131 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v117 h, v12 h, v63 h, v132 h, v82 h, v92 h, v133 h, v134 h, v135 h, v136 h, v129 h, v137 h, by simp⟩) cert131
lemma v138 (h : RootCtx) : Valid 13 s138 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v31 h, v87 h, v51 h, v18 h, v106 h, v123 h, v70 h, v101 h, v139 h, by simp⟩) cert138
lemma v140 (h : RootCtx) : Valid 13 s140 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v64 h, v88 h, v16 h, v53 h, v99 h, v118 h, v37 h, v108 h, v139 h, by simp⟩) cert140
lemma v141 (h : RootCtx) : Valid 13 s141 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v48 h, v76 h, v34 h, v69 h, v100 h, v142 h, v19 h, v143 h, v144 h, by simp⟩) cert141
lemma v145 (h : RootCtx) : Valid 13 s145 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v13 h, v77 h, v67 h, v36 h, v107 h, v146 h, v54 h, v147 h, v144 h, by simp⟩) cert145
lemma v148 (h : RootCtx) : Valid 13 s148 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v149 h, v91 h, by simp⟩) cert148
lemma v150 (h : RootCtx) : Valid 13 s150 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v151 h, v80 h, by simp⟩) cert150
lemma v152 (h : RootCtx) : Valid 13 s152 := cut_sound h (by simp) cert152
lemma v154 (h : RootCtx) : Valid 13 s154 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v155 h, v156 h, v157 h, v158 h, v159 h, v160 h, v161 h, v162 h, v163 h, v164 h, v165 h, v166 h, v167 h, v168 h, v169 h, v170 h, v171 h, v172 h, v173 h, v174 h, v175 h, v176 h, v177 h, v178 h, v179 h, v180 h, by simp⟩) cert154
lemma v181 (h : RootCtx) : Valid 13 s181 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v182 h, v183 h, v184 h, v185 h, v186 h, v160 h, v187 h, v188 h, v189 h, v190 h, v191 h, v192 h, v193 h, v194 h, v195 h, v196 h, v197 h, v198 h, v199 h, v200 h, v201 h, v202 h, v203 h, v204 h, v205 h, v206 h, by simp⟩) cert181
lemma v207 (h : RootCtx) : Valid 13 s207 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v208 h, v156 h, v184 h, v209 h, v210 h, v211 h, v212 h, v213 h, v214 h, v215 h, v216 h, v217 h, v218 h, v219 h, v220 h, v221 h, v222 h, v223 h, v224 h, v225 h, v226 h, v227 h, v228 h, v229 h, v230 h, v231 h, by simp⟩) cert207
lemma v232 (h : RootCtx) : Valid 13 s232 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v233 h, v183 h, v157 h, v234 h, v235 h, v211 h, v236 h, v237 h, v238 h, v239 h, v240 h, v241 h, v242 h, v243 h, v244 h, v245 h, v246 h, v247 h, v248 h, v249 h, v250 h, v251 h, v252 h, v253 h, v254 h, v255 h, by simp⟩) cert232
lemma v256 (h : RootCtx) : Valid 13 s256 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v257 h, v210 h, v235 h, v258 h, v160 h, v259 h, v260 h, v261 h, v166 h, v192 h, v262 h, v263 h, v264 h, v265 h, v266 h, v267 h, v268 h, v269 h, v270 h, v271 h, v272 h, v273 h, v274 h, v275 h, v276 h, v277 h, v278 h, v279 h, v280 h, v281 h, v282 h, v283 h, v284 h, v285 h, v286 h, by simp⟩) cert256
lemma v287 (h : RootCtx) : Valid 13 s287 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v288 h, v159 h, v186 h, v289 h, v211 h, v290 h, v291 h, v292 h, v217 h, v241 h, v293 h, v294 h, v264 h, v295 h, v296 h, v297 h, v298 h, v299 h, v300 h, v301 h, v302 h, v303 h, v304 h, v305 h, v306 h, v307 h, v308 h, v309 h, v310 h, v311 h, v312 h, v313 h, v314 h, v315 h, v316 h, by simp⟩) cert287
lemma v317 (h : RootCtx) : Valid 13 s317 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v155 h, v208 h, v260 h, v190 h, v291 h, v239 h, v318 h, v173 h, v319 h, v224 h, v320 h, v267 h, v321 h, v297 h, v322 h, v323 h, v324 h, v325 h, v326 h, v327 h, v328 h, v329 h, v330 h, v331 h, v332 h, v333 h, v279 h, v334 h, v309 h, v335 h, v336 h, v337 h, by simp⟩) cert317
lemma v338 (h : RootCtx) : Valid 13 s338 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v182 h, v233 h, v164 h, v261 h, v215 h, v292 h, v339 h, v340 h, v199 h, v341 h, v248 h, v342 h, v343 h, v268 h, v298 h, v323 h, v344 h, v345 h, v346 h, v347 h, v348 h, v349 h, v350 h, v351 h, v352 h, v353 h, v354 h, v280 h, v355 h, v310 h, v356 h, v357 h, by simp⟩) cert338
lemma v358 (h : RootCtx) : Valid 13 s358 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v359 h, v360 h, v245 h, v265 h, v223 h, v319 h, v361 h, v362 h, v363 h, v364 h, v365 h, v366 h, v367 h, v368 h, v369 h, v332 h, v370 h, v371 h, v354 h, v311 h, v372 h, v373 h, v374 h, by simp⟩) cert358
lemma v375 (h : RootCtx) : Valid 13 s375 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v376 h, v360 h, v221 h, v265 h, v247 h, v340 h, v377 h, v378 h, v379 h, v380 h, v381 h, v382 h, v383 h, v384 h, v385 h, v350 h, v386 h, v387 h, v334 h, v312 h, v388 h, v389 h, v390 h, by simp⟩) cert375
lemma v391 (h : RootCtx) : Valid 13 s391 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v392 h, v393 h, v196 h, v295 h, v172 h, v320 h, v394 h, v395 h, v396 h, v397 h, v398 h, v399 h, v400 h, v401 h, v402 h, v333 h, v403 h, v404 h, v355 h, v281 h, v405 h, v406 h, v407 h, by simp⟩) cert391
lemma v408 (h : RootCtx) : Valid 13 s408 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v409 h, v393 h, v170 h, v295 h, v198 h, v341 h, v410 h, v411 h, v412 h, v413 h, v414 h, v415 h, v416 h, v417 h, v418 h, v352 h, v419 h, v420 h, v335 h, v282 h, v421 h, v422 h, v423 h, by simp⟩) cert408
lemma v424 (h : RootCtx) : Valid 13 s424 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v162 h, v237 h, v425 h, v426 h, v427 h, v428 h, v429 h, v430 h, v431 h, v432 h, v433 h, v434 h, v435 h, v436 h, v437 h, v438 h, by simp⟩) cert424
lemma v439 (h : RootCtx) : Valid 13 s439 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v188 h, v213 h, v425 h, v440 h, v441 h, v442 h, v443 h, v444 h, v445 h, v446 h, v447 h, v448 h, v449 h, v450 h, v451 h, v452 h, by simp⟩) cert439
lemma v453 (h : RootCtx) : Valid 13 s453 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v187 h, v212 h, v267 h, v298 h, v454 h, v449 h, v384 h, v401 h, v203 h, v228 h, v178 h, v253 h, v455 h, v456 h, v457 h, v458 h, v459 h, v460 h, v461 h, v462 h, v463 h, v389 h, v406 h, v286 h, v316 h, by simp⟩) cert453
lemma v464 (h : RootCtx) : Valid 13 s464 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v161 h, v236 h, v297 h, v268 h, v465 h, v435 h, v368 h, v417 h, v177 h, v252 h, v204 h, v229 h, v466 h, v467 h, v468 h, v469 h, v470 h, v471 h, v472 h, v473 h, v474 h, v373 h, v422 h, v475 h, v476 h, by simp⟩) cert464
lemma v477 (h : RootCtx) : Valid 13 s477 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v244 h, v478 h, v342 h, v433 h, v380 h, v399 h, v271 h, v418 h, v479 h, v480 h, v329 h, v303 h, v466 h, v330 h, v276 h, v481 h, by simp⟩) cert477
lemma v482 (h : RootCtx) : Valid 13 s482 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v195 h, v483 h, v343 h, v447 h, v413 h, v366 h, v301 h, v385 h, v484 h, v485 h, v329 h, v273 h, v455 h, v331 h, v306 h, v486 h, by simp⟩) cert482
lemma v487 (h : RootCtx) : Valid 13 s487 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v220 h, v488 h, v321 h, v448 h, v364 h, v415 h, v272 h, v402 h, v489 h, v490 h, v349 h, v304 h, v455 h, v351 h, v276 h, v491 h, by simp⟩) cert487
lemma v492 (h : RootCtx) : Valid 13 s492 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v169 h, v493 h, v322 h, v434 h, v397 h, v382 h, v302 h, v369 h, v494 h, v495 h, v349 h, v274 h, v466 h, v353 h, v306 h, v496 h, by simp⟩) cert492
lemma v497 (h : RootCtx) : Valid 13 s497 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v377 h, v498 h, v367 h, v332 h, v499 h, v500 h, v501 h, v502 h, v313 h, v389 h, v314 h, v503 h, v504 h, v505 h, by simp⟩) cert497
lemma v506 (h : RootCtx) : Valid 13 s506 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v410 h, v507 h, v400 h, v333 h, v508 h, v509 h, v510 h, v511 h, v283 h, v284 h, v422 h, v512 h, v513 h, v514 h, by simp⟩) cert506
lemma v515 (h : RootCtx) : Valid 13 s515 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v394 h, v516 h, v416 h, v352 h, v517 h, v518 h, v519 h, v520 h, v283 h, v406 h, v285 h, v521 h, v522 h, v523 h, by simp⟩) cert515
lemma v524 (h : RootCtx) : Valid 13 s524 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v361 h, v525 h, v383 h, v350 h, v526 h, v527 h, v528 h, v529 h, v313 h, v373 h, v315 h, v530 h, v531 h, v532 h, by simp⟩) cert524
lemma v533 (h : RootCtx) : Valid 13 s533 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v534 h, v197 h, v246 h, v535 h, v536 h, v537 h, v344 h, v538 h, v539 h, by simp⟩) cert533
lemma v540 (h : RootCtx) : Valid 13 s540 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v541 h, v171 h, v222 h, v542 h, v543 h, v544 h, v324 h, v545 h, v546 h, by simp⟩) cert540
lemma v547 (h : RootCtx) : Valid 13 s547 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v548 h, v431 h, v549 h, v550 h, v299 h, v551 h, by simp⟩) cert547
lemma v552 (h : RootCtx) : Valid 13 s552 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v553 h, v445 h, v554 h, v555 h, v269 h, v556 h, by simp⟩) cert552
lemma v557 (h : RootCtx) : Valid 13 s557 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v558 h, v446 h, v559 h, v560 h, v300 h, v561 h, by simp⟩) cert557
lemma v562 (h : RootCtx) : Valid 13 s562 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v563 h, v432 h, v564 h, v565 h, v270 h, v566 h, by simp⟩) cert562
lemma v567 (h : RootCtx) : Valid 13 s567 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v250 h, v568 h, v202 h, v230 h, v569 h, v570 h, v571 h, v572 h, by simp⟩) cert567
lemma v573 (h : RootCtx) : Valid 13 s573 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v201 h, v574 h, v251 h, v179 h, v575 h, v576 h, v577 h, v572 h, by simp⟩) cert573
lemma v578 (h : RootCtx) : Valid 13 s578 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v226 h, v579 h, v176 h, v254 h, v580 h, v581 h, v577 h, v582 h, by simp⟩) cert578
lemma v583 (h : RootCtx) : Valid 13 s583 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v175 h, v584 h, v227 h, v205 h, v585 h, v586 h, v571 h, v582 h, by simp⟩) cert583
lemma v587 (h : RootCtx) : Valid 13 s587 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v588 h, v589 h, by simp⟩) cert587
lemma v590 (h : RootCtx) : Valid 13 s590 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v591 h, v592 h, by simp⟩) cert590
lemma v593 (h : RootCtx) : Valid 13 s593 := cut_sound h (by simp) cert593
lemma v594 (h : RootCtx) : Valid 13 s594 := cut_sound h (by simp) cert594
lemma v595 (h : RootCtx) : Valid 13 s595 := cut_sound h (by simp) cert595
lemma v0 (h : RootCtx) : Valid 14 s0 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v1 h, v20 h, v38 h, v55 h, v71 h, v83 h, v94 h, v102 h, v109 h, v113 h, v119 h, v124 h, v131 h, v138 h, v140 h, v141 h, v145 h, v148 h, v150 h, v152 h, by simp⟩) cert0
lemma v153 (h : RootCtx) : Valid 14 s153 := cut_sound h (by simp only [List.forall_mem_cons]; exact ⟨v154 h, v181 h, v207 h, v232 h, v256 h, v287 h, v317 h, v338 h, v358 h, v375 h, v391 h, v408 h, v424 h, v439 h, v453 h, v464 h, v477 h, v482 h, v487 h, v492 h, v497 h, v506 h, v515 h, v524 h, v533 h, v540 h, v547 h, v552 h, v557 h, v562 h, v567 h, v573 h, v578 h, v583 h, v587 h, v590 h, v593 h, v594 h, v595 h, by simp⟩) cert153

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem concludeRoot (hI : ∀ e∈pr 0,Imp e.1 e.2) : Imp 0 15 := by
  apply initial_sound (Z:=0) (L:=15) (answer:=fun z v => !listed [s0,s153] z v) (by decide +kernel) (by decide) hI init0
  intro z v hin ctx
  have h : RootCtx := by
    unfold RootCtx
    rw [rootCtxEq.1,rootCtxEq.2.1,rootCtxEq.2.2]
    exact ctx
  have hv : ∀ s∈[s0, s153],Valid 14 s := by simp only [List.forall_mem_cons]; exact ⟨v0 h, v153 h, by simp⟩
  have hm : (z,v) ∈ [s0, s153] := listed_mem (by simpa using hin)
  have hh := hv _ hm
  simpa only [Valid,rootCtxEq.1,rootCtxEq.2.1] using hh

theorem i0 : Imp 0 15 := by
  apply concludeRoot
  intro x hx
  have h := List.all_eq_true.1 pr0 x hx
  rw [Bool.or_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem, List.contains_iff_mem] at h
  exact h.elim (fun h => h.elim (i1 x) (i2 x)) (i3 x)
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
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
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
    rcases hop with rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) go
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
lemma or03_mem : rawP.getD 0 0 ||| rawP.getD 3 0 ∈ rawL := List.mem_append_right _ (by simp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m0_full : rawL.all (fun w => Nat.beq (Nat.land w (mz 0)) w) = true := by decide +kernel
lemma raw_sub {x : ℕ} (hx : x ∈ rawL) : x &&& mz 0 = x := by
  have := List.all_eq_true.1 m0_full x hx
  rwa [Nat.beq_eq, nl] at this
theorem final (i0 : Imp 0 15) : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g∈C.gates, g.op∈({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length≤2) → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
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
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ x.inputs.length ≤ 2 := by
      intro g h
      obtain ⟨a,b⟩ := hfan g h
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at a ⊢
      exact ⟨a.imp_right Or.inl,b⟩
    have hy : gv (mz 0) rawP g = rawP.getD 0 0 ||| rawP.getD 3 0 := by
      apply Nat.eq_of_testBit_eq; intro b
      cases hb : (mz 0).testBit b with
      | false =>
        have e1 := congrArg (fun x => x.testBit b) (gv_sub (mz 0) hRP g)
        have e2 := congrArg (fun x => x.testBit b) (raw_sub or03_mem)
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
    have hsub : ∀ x ∈ rawP ++ [rawP.getD 0 0 ||| rawP.getD 3 0], x ∈ rawL := fun x hx => hx
    have hout : (ex (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 3 0])).getD out 0 = tz 0 := by
      rw [← EF_ok]
      have hs : ∀ x ∈ ex (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 3 0]), x &&& mz 0 = x :=
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
    have hsol := ex_sol (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 3 0]) (C (mz 0) (WZ 0))
      (fun x hx => Or.inl ⟨x, hsub x hx, (raw_sub (hsub x hx)).symm⟩) (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
      (fun x hx => hfan x (List.mem_cons_of_mem _ hx)) ⟨out, hout⟩
    exact i0 _ (by omega) hsol

theorem fromBound (bound : Imp 0 15) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C form count good
  obtain ⟨size,cout,first,restr⟩ := form
  have allops : ∀ g∈C.gates, g.op∈({GateOp.and,GateOp.or}:Set GateOp) ∧ g.inputs.length≤2 := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
    have gs := restr i hi
    dsimp only at gs
    rcases gs with eq | ⟨a,_,eq⟩ | ⟨a,b,_,_,_,eq|eq⟩
    · rw [eq];exact ⟨Or.inl rfl,by decide⟩
    · have z := (List.countP_eq_zero.mp count) C.gates[i] (List.getElem_mem hi)
      rw [eq] at z; contradiction
    · rw [eq];exact ⟨Or.inl rfl,by simp⟩
    · rw [eq];exact ⟨Or.inr rfl,by simp⟩

  have seed (y : Fin 9 → Bool) : (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3) := by
    cases hg : C.gates with
    | nil => simp [hg] at size
    | cons g gs =>
      have he : g=⟨.or,[0,3]⟩ := by simpa [hg] using first
      subst g
      unfold Circuit.wires
      rw [hg, List.foldl_cons, fold_keep _ _ _ (by simp)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp [GateOp.eval, List.getD_eq_getElem?_getD]
  have hs := final bound C allops seed good
  change 16 ≤ C.gates.length at hs
  omega
end PEqualNP.Outside.L_meta_2766

theorem PEqualNP.Outside.L_meta_2766 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  exact PEqualNP.Outside.L_meta_2766.fromBound PEqualNP.Outside.L_meta_2766.i0
