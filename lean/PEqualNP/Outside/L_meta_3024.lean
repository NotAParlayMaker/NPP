import Mathlib
import PEqualNP.Defs

-- The one-negation certificate is adapted from jdavies69, submission 5615.
-- The theta certificate is adapted from rzr1331, submission 6406.
-- The argument covers every circuit with the specified first two gates.

namespace PEqualNP.Outside.L_meta_3024
section
-- The derivation, search, and finite cases are from the proof of L-meta-2163.
-- The table below shares the wire values and the predicates for the finite chunks.
namespace Theta

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Part 1: derivations. Negation is free: every wire is normalised to vanish at the zero input,
-- and a binary gate becomes one of four operations.

inductive Der {α : Type} (op : Fin 4 → α → α → α) : ℕ → Set α → α → Prop
  | here {W : Set α} {y : α} : y ∈ W → Der op 0 W y
  | weak {k : ℕ} {W : Set α} {y : α} : Der op k W y → Der op (k + 1) W y
  | step {k : ℕ} {W : Set α} {y : α} (t : Fin 4) (a b : α) : a ∈ W → b ∈ W →
      Der op k (insert (op t a b) W) y → Der op (k + 1) W y

theorem Der.mono {α : Type} {op : Fin 4 → α → α → α} {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : ∀ {W' : Set α}, W ⊆ W' → Der op k W' y := by
  induction h with
  | here hy => intro W' hs; exact Der.here (hs hy)
  | weak _ ih => intro W' hs; exact Der.weak (ih hs)
  | step t a b ha hb _ ih =>
    intro W' hs
    exact Der.step t a b (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))

theorem Der.le {α : Type} {op : Fin 4 → α → α → α} {k k' : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) (hk : k ≤ k') : Der op k' W y := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Der.weak ih

theorem Der.map {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) {k : ℕ} {W : Set α} {y : α}
    (h : Der op k W y) : Der op' k (e '' W) (e y) := by
  induction h with
  | here hy => exact Der.here ⟨_, hy, rfl⟩
  | weak _ ih => exact Der.weak ih
  | step t a b ha hb _ ih =>
    refine Der.step t (e a) (e b) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ?_
    rwa [Set.image_insert_eq, he] at ih

theorem Der.elim {α β : Type} {op : Fin 4 → α → α → α} {op' : Fin 4 → β → β → β} (e : α → β)
    (he : ∀ t a b, e (op t a b) = op' t (e a) (e b)) (x : α)
    (hl : ∀ t b, op' t (e x) b = e x ∨ op' t (e x) b = b)
    (hr : ∀ t b, op' t b (e x) = e x ∨ op' t b (e x) = b)
    {k : ℕ} {W : Set α} {y : α} (h : Der op k W y) :
    ∀ U : Set α, W ⊆ insert x U → y ≠ x → e x ∈ e '' U →
      Der op k U y ∨ ∃ k', k = k' + 1 ∧ Der op' k' (e '' U) (e y) := by
  induction h with
  | here hy =>
    intro U hs hne _
    exact Or.inl (Der.here ((hs hy).resolve_left hne))
  | weak _ ih =>
    intro U hs hne hx
    rcases ih U hs hne hx with h | ⟨k', rfl, h⟩
    · exact Or.inl (Der.weak h)
    · exact Or.inr ⟨_, rfl, Der.weak h⟩
  | @step k W y t a b ha hb h ih =>
    intro U hs hne hx
    have im (w : α) (hw : w ∈ W) : e w ∈ e '' U := by
      rcases hs hw with rfl | hw
      · exact hx
      · exact ⟨w, hw, rfl⟩
    by_cases hab : a ∈ U ∧ b ∈ U
    · have hs' : insert (op t a b) W ⊆ insert x (insert (op t a b) U) := by
        rintro w (rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · rcases hs hw with rfl | hw
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hw)
      have hx' : e x ∈ e '' insert (op t a b) U := by
        obtain ⟨u, hu, h⟩ := hx; exact ⟨u, Or.inr hu, h⟩
      rcases ih _ hs' hne hx' with hd | ⟨k', hk', hd⟩
      · exact Or.inl (Der.step t a b hab.1 hab.2 hd)
      · refine Or.inr ⟨k' + 1, by rw [hk'], ?_⟩
        rw [Set.image_insert_eq, he] at hd
        exact Der.step t (e a) (e b) ⟨a, hab.1, rfl⟩ ⟨b, hab.2, rfl⟩ hd
    · have hc : e (op t a b) ∈ e '' U := by
        rw [he]
        by_cases hau : a ∈ U
        · have hbx : b = x := by
            rcases hs hb with h | h
            · exact h
            · exact absurd ⟨hau, h⟩ hab
          subst hbx
          rcases hr t (e a) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im a ha
        · have hax : a = x := by
            rcases hs ha with h | h
            · exact h
            · exact absurd h hau
          subst hax
          rcases hl t (e b) with h | h
          · rw [h]; exact hx
          · rw [h]; exact im b hb
      refine Or.inr ⟨k, rfl, (h.map e he).mono ?_⟩
      rintro _ ⟨w, rfl | hw, rfl⟩
      · exact hc
      · exact im w hw

def opB (t : Fin 4) (a b : Bool) : Bool :=
  match t with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | 3 => b && !a

def opF {Ω : Type} (t : Fin 4) (f g : Ω → Bool) : Ω → Bool := fun x => opB t (f x) (g x)

def opN (t : Fin 4) (a b : ℕ) : ℕ :=
  match t with
  | 0 => Nat.land a b
  | 1 => Nat.lor a b
  | 2 => Nat.xor a (Nat.land a b)
  | 3 => Nat.xor b (Nat.land a b)

lemma land_bit (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

lemma lor_bit (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

lemma xor_bit (x y i : ℕ) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simpa [bne] using Nat.testBit_xor x y i

lemma shr_bit (x s i : ℕ) : (Nat.shiftRight x s).testBit i = x.testBit (s + i) := by
  have := Nat.testBit_shiftRight (x := x) (i := s) (j := i)
  simpa using this

lemma opN_bit (t : Fin 4) (a b i : ℕ) :
    (opN t a b).testBit i = opB t (a.testBit i) (b.testBit i) := by
  fin_cases t <;> simp only [opN, opB, land_bit, lor_bit, xor_bit] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

lemma Der.agree {Ω : Type} {k : ℕ} {W : Set (Ω → Bool)} {y : Ω → Bool} (h : Der opF k W y)
    (p q : Ω) : (∀ w ∈ W, w p = w q) → y p = y q := by
  induction h with
  | here hy => intro hw; exact hw _ hy
  | weak _ ih => exact ih
  | step t a b ha hb _ ih =>
    intro hw
    refine ih ?_
    rintro w (rfl | hm)
    · simp only [opF, hw a ha, hw b hb]
    · exact hw w hm

-- Part 2: traces.

structure St where
  t : Fin 4
  a : ℕ
  b : ℕ

def St.val (s : St) : ℕ := opN s.t s.a s.b

def Valid (y : ℕ) : Set ℕ → List St → Prop
  | W, [] => y ∈ W
  | W, s :: l => s.a ∈ W ∧ s.b ∈ W ∧ s.val ∉ W ∧ Valid y (insert s.val W) l

def need (y : ℕ) : List St → Finset ℕ
  | [] => {y}
  | s :: l => insert s.a (insert s.b ((need y l).erase s.val))

def Useful (y : ℕ) : List St → Prop
  | [] => True
  | s :: l => s.val ∈ need y l ∧ Useful y l

def killB (m : ℕ) (s : St) : Bool := Nat.beq (Nat.land s.a m) 0 || Nat.beq (Nat.land s.b m) 0

def kills (m : ℕ) (l : List St) : ℕ := l.countP (killB m)

def Chain : ℕ → List St → Prop
  | _, [] => True
  | p, s :: l => (s.a = p ∨ s.b = p ∨ p ≤ s.val) ∧ Chain s.val l

lemma valid_of_der {k : ℕ} {W : Set ℕ} {y : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l := by
  induction h with
  | here hy => exact ⟨[], by simp, hy⟩
  | weak _ ih => obtain ⟨l, h1, h2⟩ := ih; exact ⟨l, by omega, h2⟩
  | @step k W y t a b ha hb _ ih =>
    obtain ⟨l, h1, h2⟩ := ih
    by_cases hc : opN t a b ∈ W
    · rw [Set.insert_eq_of_mem hc] at h2; exact ⟨l, by omega, h2⟩
    · exact ⟨⟨t, a, b⟩ :: l, by simp; omega, ha, hb, hc, h2⟩

lemma need_sub {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → ∀ x ∈ need y l, x ∈ W := by
  induction l with
  | nil => intro W h x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact h
  | cons s l ih =>
    intro W h x hx
    obtain ⟨ha, hb, hc, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨h1, h2⟩
    · exact ha
    · exact hb
    · exact (ih hv x h2).resolve_left h1

lemma valid_drop {y c : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y (insert c W) l →
    c ∉ need y l → Valid y W l := by
  induction l with
  | nil =>
    intro W h hc
    rw [need, Finset.mem_singleton] at hc
    exact h.resolve_left (fun e => hc e.symm)
  | cons s l ih =>
    intro W h hc
    obtain ⟨ha, hb, hf, hv⟩ := h
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hne : c ≠ s.val := fun e => hf (Or.inl e.symm)
    refine ⟨ha.resolve_left (Ne.symm h1), hb.resolve_left (Ne.symm h2), fun h => hf (Or.inr h), ?_⟩
    rw [Set.insert_comm] at hv
    exact ih hv (h3 hne)

lemma useful_of_min {y : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l →
    (∀ l', Valid y W l' → l.length ≤ l'.length) → Useful y l := by
  induction l with
  | nil => intro W _ _; trivial
  | cons s l ih =>
    intro W h hmin
    obtain ⟨ha, hb, hf, hv⟩ := h
    refine ⟨?_, ih hv fun l' hl' => ?_⟩
    · by_contra hc
      have := hmin l (valid_drop l hv hc)
      simp at this
    · have := hmin (s :: l') ⟨ha, hb, hf, hl'⟩
      simpa using this

lemma need_card {y : ℕ} (l : List St) (h : Useful y l) : (need y l).card ≤ l.length + 1 := by
  induction l with
  | nil => simp [need]
  | cons s l ih =>
    obtain ⟨h1, h2⟩ := h
    have e := Finset.card_erase_of_mem h1
    have i := ih h2
    have c1 := Finset.card_insert_le s.a (insert s.b ((need y l).erase s.val))
    have c2 := Finset.card_insert_le s.b ((need y l).erase s.val)
    have p := Finset.card_pos.mpr ⟨_, h1⟩
    rw [need, List.length_cons]
    omega

lemma need_next {y : ℕ} {s : St} {l : List St} {x : ℕ} (h : x ∈ need y l) :
    x = s.val ∨ x ∈ need y (s :: l) := by
  by_cases hx : x = s.val
  · exact Or.inl hx
  · right; rw [need]; simp [hx, h]

lemma need_agree {y i j : ℕ} (l : List St) (h : ∀ x ∈ need y l, x.testBit i = x.testBit j) :
    y.testBit i = y.testBit j := by
  induction l with
  | nil => exact h y (by simp [need])
  | cons s l ih =>
    refine ih fun x hx => ?_
    rcases need_next (s := s) hx with rfl | hx
    · rw [St.val, opN_bit, opN_bit, h s.a (by simp [need]), h s.b (by simp [need])]
    · exact h x hx

lemma kill_forced {y m x : ℕ} (hy : Nat.land y m ≠ 0) (l : List St) (hx : x ∈ need y l)
    (hm : Nat.land x m = 0) : 1 ≤ kills m l := by
  induction l with
  | nil => rw [need, Finset.mem_singleton] at hx; rw [hx] at hm; exact absurd hm hy
  | cons s l ih =>
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    have hk : killB m s = true → 1 ≤ kills m (s :: l) := fun h => by
      rw [kills, List.countP_cons_of_pos h]; omega
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact hk (by unfold killB; rw [hm]; rfl)
    · exact hk (by unfold killB; rw [hm]; exact Bool.or_true _)
    · have := ih h2
      have c : kills m l ≤ kills m (s :: l) := by
        rw [kills, kills, List.countP_cons]; omega
      omega

lemma land_op (t : Fin 4) (a b m : ℕ) :
    Nat.land (opN t a b) m = opN t (Nat.land a m) (Nat.land b m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [land_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> cases m.testBit i <;> rfl

lemma opN_zero_left (t : Fin 4) (b : ℕ) : opN t 0 b = 0 ∨ opN t 0 b = b := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t 0 b).testBit i = c (b.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t 0 b = 0 ∨ opN t 0 b = b := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key _ (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)

def swapT : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

lemma opN_swap (t : Fin 4) (a b : ℕ) : opN t a b = opN (swapT t) b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [opN_bit, opN_bit]
  fin_cases t <;> cases a.testBit i <;> cases b.testBit i <;> rfl

lemma opN_zero_right (t : Fin 4) (b : ℕ) : opN t b 0 = 0 ∨ opN t b 0 = b := by
  rw [opN_swap]; exact opN_zero_left _ _

lemma opN_self (t : Fin 4) (a : ℕ) : opN t a a = 0 ∨ opN t a a = a := by
  have key (c : Bool → Bool) (h : ∀ i, (opN t a a).testBit i = c (a.testBit i))
      (hc : c = (fun _ => false) ∨ c = id) : opN t a a = 0 ∨ opN t a a = a := by
    rcases hc with rfl | rfl
    · left; apply Nat.eq_of_testBit_eq; intro i; rw [h]; simp
    · right; apply Nat.eq_of_testBit_eq; intro i; rw [h]; rfl
  fin_cases t
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key id (fun i => by rw [opN_bit]; simp [opB]) (Or.inr rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)
  · exact key (fun _ => false) (fun i => by rw [opN_bit]; simp [opB]) (Or.inl rfl)

lemma der_masked {y m : ℕ} (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∃ n, n + kills m l = l.length ∧ Der opN n ((fun w => Nat.land w m) '' W) (Nat.land y m) := by
  induction l with
  | nil => intro W h _; exact ⟨0, by simp [kills], Der.here ⟨y, h, rfl⟩⟩
  | cons s l ih =>
    intro W h h0
    obtain ⟨ha, hb, _, hv⟩ := h
    obtain ⟨n, hn, hd⟩ := ih hv (Or.inr h0)
    have im (w : ℕ) (hw : w ∈ W) : Nat.land w m ∈ (fun w => Nat.land w m) '' W := ⟨w, hw, rfl⟩
    have z : 0 ∈ (fun w => Nat.land w m) '' W := ⟨0, h0, by simp [Nat.land]⟩
    by_cases hk : killB m s = true
    · refine ⟨n, ?_, hd.mono ?_⟩
      · rw [kills, List.countP_cons_of_pos hk, List.length_cons]
        rw [kills] at hn; omega
      · rintro _ ⟨w, rfl | hw, rfl⟩
        · show Nat.land s.val m ∈ _
          rw [St.val, land_op]
          rw [killB, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at hk
          rcases hk with h | h
          · rw [h]
            rcases opN_zero_left s.t (Nat.land s.b m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ hb
          · rw [h]
            rcases opN_zero_right s.t (Nat.land s.a m) with e | e
            · rw [e]; exact z
            · rw [e]; exact im _ ha
        · exact im w hw
    · refine ⟨n + 1, ?_, ?_⟩
      · rw [kills, List.countP_cons_of_neg hk, List.length_cons]
        rw [kills] at hn; omega
      · refine Der.step s.t _ _ (im _ ha) (im _ hb) ?_
        rw [Set.image_insert_eq] at hd
        have e : Nat.land s.val m = opN s.t (Nat.land s.a m) (Nat.land s.b m) := land_op _ _ _ _
        rw [← e]; exact hd

lemma valid_swap {y : ℕ} (s1 s2 : St) (post : List St) (h1 : s2.a ≠ s1.val) (h2 : s2.b ≠ s1.val)
    (pre : List St) : ∀ {W : Set ℕ}, Valid y W (pre ++ s1 :: s2 :: post) →
      Valid y W (pre ++ s2 :: s1 :: post) := by
  induction pre with
  | nil =>
    intro W h
    obtain ⟨ha, hb, hc, ha2, hb2, hc2, hv⟩ := h
    refine ⟨ha2.resolve_left h1, hb2.resolve_left h2, fun h => hc2 (Or.inr h), Or.inr ha, Or.inr hb,
      ?_, ?_⟩
    · rintro (e | h)
      · exact hc2 (Or.inl e.symm)
      · exact hc h
    · rw [Set.insert_comm]; exact hv
  | cons s pre ih =>
    intro W h
    obtain ⟨ha, hb, hc, hv⟩ := h
    exact ⟨ha, hb, hc, ih hv⟩

def keyN (l : List St) : ℕ := l.foldl (fun acc s => 2 * acc + s.val) 0

lemma fold_lt (l : List St) : ∀ {x x' : ℕ}, x < x' →
    l.foldl (fun acc s => 2 * acc + s.val) x < l.foldl (fun acc s => 2 * acc + s.val) x' := by
  induction l with
  | nil => intro x x' h; exact h
  | cons s l ih =>
    intro x x' h
    exact ih (show 2 * x + s.val < 2 * x' + s.val by omega)

lemma key_swap (pre post : List St) (s1 s2 : St) (h : s2.val < s1.val) :
    keyN (pre ++ s2 :: s1 :: post) < keyN (pre ++ s1 :: s2 :: post) := by
  unfold keyN
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_cons]
  exact fold_lt post (by omega)

lemma chain_of {l : List St} : ∀ (p : ℕ),
    (∀ s l', l = s :: l' → (s.a = p ∨ s.b = p ∨ p ≤ s.val)) →
    (∀ pre s1 s2 post, l = pre ++ s1 :: s2 :: post →
      (s2.a = s1.val ∨ s2.b = s1.val ∨ s1.val ≤ s2.val)) → Chain p l := by
  induction l with
  | nil => intro p _ _; trivial
  | cons s l ih =>
    intro p h1 h2
    refine ⟨h1 s l rfl, ih s.val (fun s' l' e => ?_) (fun pre s1 s2 post e => ?_)⟩
    · exact h2 [] s s' l' (by rw [e]; rfl)
    · exact h2 (s :: pre) s1 s2 post (by rw [e]; rfl)

lemma exists_min {α : Type} (S : Set α) (f : α → ℕ) (h : S.Nonempty) :
    ∃ l ∈ S, ∀ l' ∈ S, f l ≤ f l' := by
  obtain ⟨l, hl, hm⟩ := (measure f).wf.has_min S h
  exact ⟨l, hl, fun l' hl' => not_lt.mp (hm l' hl')⟩

def headV : List St → ℕ
  | [] => 0
  | s :: _ => s.val

-- a shortest trace, least by its first gate and then by its key
lemma exists_sorted {y : ℕ} {W : Set ℕ} {k : ℕ} (h : Der opN k W y) :
    ∃ l, l.length ≤ k ∧ Valid y W l ∧ Useful y l ∧ Chain 0 l ∧
      ∀ l', Valid y W l' → l'.length = l.length → headV l ≤ headV l' := by
  obtain ⟨l0, hk0, hv0⟩ := valid_of_der h
  obtain ⟨l1, hv1, hmin⟩ := exists_min {l | Valid y W l} List.length ⟨l0, hv0⟩
  obtain ⟨l2, ⟨hv2, hlen2⟩, hhead⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length} headV ⟨l1, hv1, rfl⟩
  obtain ⟨l, ⟨hv, hlen, hh⟩, hkey⟩ :=
    exists_min {l | Valid y W l ∧ l.length = l1.length ∧ headV l = headV l2} keyN ⟨l2, hv2, hlen2, rfl⟩
  refine ⟨l, ?_, hv, useful_of_min l hv (fun l' hl' => by rw [hlen]; exact hmin l' hl'), ?_, ?_⟩
  · rw [hlen]; exact (hmin l0 hv0).trans hk0
  · refine chain_of 0 (fun s l' _ => Or.inr (Or.inr (Nat.zero_le _))) ?_
    intro pre s1 s2 post e
    by_contra hc
    push Not at hc
    obtain ⟨c1, c2, c3⟩ := hc
    rw [e] at hv hlen hh hkey
    have sv := valid_swap s1 s2 post c1 c2 pre hv
    have sl : (pre ++ s2 :: s1 :: post).length = l1.length := by
      rw [← hlen]; simp
    cases pre with
    | nil =>
      have := hhead _ ⟨sv, sl⟩
      rw [← hh] at this
      change s1.val ≤ s2.val at this
      omega
    | cons p pre =>
      have := hkey _ ⟨sv, sl, by rw [← hh]; rfl⟩
      have := key_swap (p :: pre) post s1 s2 c3
      omega
  · intro l' hl' hl
    rw [hh]; exact hhead l' ⟨hl', by rw [hl, hlen]⟩

-- every trace step has distinct nonzero operands and a new nonzero value
lemma step_facts {y : ℕ} {W : Set ℕ} {s : St} {l : List St} (h : Valid y W (s :: l)) (h0 : 0 ∈ W) :
    s.a ≠ 0 ∧ s.b ≠ 0 ∧ s.a ≠ s.b ∧ s.val ≠ 0 ∧ s.val ≠ s.a ∧ s.val ≠ s.b ∧
      s.val ∉ need y (s :: l) := by
  have hn := need_sub (s :: l) h
  obtain ⟨ha, hb, hc, _⟩ := h
  refine ⟨?_, ?_, ?_, fun e => hc (e ▸ h0), fun e => hc (e ▸ ha), fun e => hc (e ▸ hb),
    fun hh => hc (hn _ hh)⟩
  · intro e
    rcases opN_zero_left s.t s.b with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact hb)
  · intro e
    rcases opN_zero_right s.t s.a with h | h
    · exact hc (by rw [St.val, e, h]; exact h0)
    · exact hc (by rw [St.val, e, h]; exact ha)
  · intro e
    rcases opN_self s.t s.a with h | h
    · exact hc (by rw [St.val, ← e, h]; exact h0)
    · exact hc (by rw [St.val, ← e, h]; exact ha)


-- Part 3: the search.

structure Wr where
  w : ℕ
  s : ℕ
  f : ℕ

def sepN (L w : ℕ) : ℕ := Nat.land (Nat.xor w (Nat.shiftRight w 143)) L

def covL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.s (covL l)

def flL : List Wr → ℕ
  | [] => 0
  | a :: l => Nat.lor a.f (flL l)

def lenL : List Wr → ℕ
  | [] => 0
  | _ :: l => Nat.succ (lenL l)

def absentL (g : ℕ) : List Wr → Bool
  | [] => true
  | x :: l => cond (Nat.beq x.w g) false (absentL g l)

def app : List Wr → List Wr → List Wr
  | [], m => m
  | a :: l, m => a :: app l m

def sub (a b : ℕ) : Bool := Nat.beq (Nat.land a b) a

def force (x : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun n _ => f (Nat.succ n)) x

lemma force_eq (x : ℕ) (f : ℕ → Bool) : force x f = f x := by cases x <;> rfl

abbrev Next := List Wr → ℕ → ℕ → ℕ → ℕ → Bool

def tryG (L : ℕ) (r : Next) (k m : ℕ) (rest : List Wr) (cr c1 c2 c3 : ℕ) (a b : Wr) (last : ℕ)
    (uses : Bool) (g fg : ℕ) : Bool :=
  cond (Nat.beq g 0) false (cond (Nat.beq g a.w) false (cond (Nat.beq g b.w) false
    (cond (cond uses true (Nat.ble last g))
      (cond (sub fg c1)
        (force (sepN L g) fun sg =>
          force (Nat.lor cr sg) fun base =>
            (cond (Nat.beq base L) (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: rest) c1 c2 c3 g) false)
              false) ||
            (cond (Nat.ble m (Nat.succ k))
              ((cond (sub a.f c1) (cond (Nat.beq (Nat.lor base a.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (sub b.f c1) (cond (Nat.beq (Nat.lor base b.s) L)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: b :: rest) c1 c2 c3 g) false) false) false) ||
               (cond (Nat.ble m k) (cond (sub a.f c1) (cond (sub b.f c1)
                  (cond (absentL g rest) (r (⟨g, sg, fg⟩ :: a :: b :: rest) c1 c2 c3 g) false) false)
                  false) false))
              false))
        false)
      false)))

def tryP (L : ℕ) (r : Next) (k m c1 c2 c3 last : ℕ) (a b : Wr) (rest : List Wr) : Bool :=
  force (Nat.lor a.f b.f) fun K =>
    cond (sub K c1)
      (force (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K))) fun d1 =>
       force (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) fun d2 =>
       force (Nat.xor c3 (Nat.land c3 K)) fun d3 =>
        cond (sub (flL rest) d1)
          (force (covL rest) fun cr =>
            force (Nat.land a.w b.w) fun ab =>
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last) ab K ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.lor a.w b.w) (Nat.land a.f b.f) ||
              (tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor a.w ab) a.f ||
              tryG L r k m rest cr d1 d2 d3 a b last (Nat.beq a.w last || Nat.beq b.w last)
                  (Nat.xor b.w ab) b.f)))
          false)
      false

def pairsB (a : Wr) : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, b :: l => (a, b, app acc l) :: pairsB a (b :: acc) l

def pairsA : List Wr → List Wr → List (Wr × Wr × List Wr)
  | _, [] => []
  | acc, a :: l => pairsB a acc l ++ pairsA (a :: acc) l

def anyP (p : Wr → Wr → List Wr → Bool) : List (Wr × Wr × List Wr) → Bool
  | [] => false
  | x :: l => p x.1 x.2.1 x.2.2 || anyP p l

def isT (y : ℕ) : List Wr → Bool
  | [a] => Nat.beq a.w y
  | _ => false

def search (L y : ℕ) : ℕ → Next
  | 0, v, _, _, _, _ => isT y v
  | k + 1, v, c1, c2, c3, last =>
    isT y v || anyP (tryP L (search L y k) k (lenL v) c1 c2 c3 last) (pairsA [] v)

-- correctness of the parts

lemma lenL_eq (v : List Wr) : lenL v = v.length := by
  induction v with
  | nil => rfl
  | cons a l ih => rw [lenL, ih]; rfl

lemma app_eq (a b : List Wr) : app a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [app, ih]; rfl

lemma absent_true {g : ℕ} {l : List Wr} (h : ∀ x ∈ l, x.w ≠ g) : absentL g l = true := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : Nat.beq x.w g = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]; exact h x (by simp)
    rw [absentL, hx]
    exact ih fun u hu => h u (by simp [hu])

lemma sub_true {a b : ℕ} (h : ∀ i, a.testBit i = true → b.testBit i = true) : sub a b = true := by
  rw [sub, Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [land_bit]
  cases ha : a.testBit i
  · rfl
  · rw [h i ha]; rfl

lemma anyP_true {p : Wr → Wr → List Wr → Bool} {l : List (Wr × Wr × List Wr)} {a b : Wr}
    {r : List Wr} (hm : (a, b, r) ∈ l) (hp : p a b r = true) : anyP p l = true := by
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    rw [anyP, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with rfl | h
    · exact Or.inl hp
    · exact Or.inr (ih h)

lemma pairsB_spec (a b : Wr) (l : List Wr) : ∀ acc : List Wr, b ∈ l →
    ∃ r, (a, b, r) ∈ pairsB a acc l ∧ (acc ++ l).Perm (b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨acc ++ l, by simp [pairsB, app_eq], List.perm_middle⟩
    · obtain ⟨r, h1, h2⟩ := ih (x :: acc) h
      exact ⟨r, by simp [pairsB, h1], List.perm_middle.trans h2⟩

lemma pairsA_spec (a b : Wr) (hab : a ≠ b) (l : List Wr) : ∀ acc : List Wr, a ∈ l → b ∈ l →
    ∃ r, ((a, b, r) ∈ pairsA acc l ∨ (b, a, r) ∈ pairsA acc l) ∧ (acc ++ l).Perm (a :: b :: r) := by
  induction l with
  | nil => intro acc h; simp at h
  | cons x l ih =>
    intro acc ha hb
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with e | hb'
      · exact absurd e.symm hab
      · obtain ⟨r, h1, h2⟩ := pairsB_spec a b l acc hb'
        exact ⟨r, Or.inl (by rw [pairsA]; exact List.mem_append_left _ h1),
          List.perm_middle.trans (h2.cons a)⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, h1, h2⟩ := pairsB_spec b a l acc ha'
        exact ⟨r, Or.inr (by rw [pairsA]; exact List.mem_append_left _ h1),
          (List.perm_middle.trans (h2.cons b)).trans (List.Perm.swap a b r)⟩
      · obtain ⟨r, h1, h2⟩ := ih (x :: acc) ha' hb'
        refine ⟨r, ?_, List.perm_middle.trans h2⟩
        rcases h1 with h | h
        · exact Or.inl (by rw [pairsA]; exact List.mem_append_right _ h)
        · exact Or.inr (by rw [pairsA]; exact List.mem_append_right _ h)

structure Rep (L H : ℕ) (mask : ℕ → ℕ) (v : List Wr) (S : Finset ℕ) : Prop where
  nd : (v.map Wr.w).Nodup
  mem : ∀ x, x ∈ S ↔ ∃ u ∈ v, u.w = x
  sep : ∀ u ∈ v, u.s = sepN L u.w
  fl : ∀ u ∈ v, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0

def Bud (H : ℕ) (mask : ℕ → ℕ) (c1 c2 c3 : ℕ) (l : List St) : Prop :=
  ∀ h < H, kills (mask h) l ≤ 3 ∧ (1 ≤ kills (mask h) l → c1.testBit h = true) ∧
    (2 ≤ kills (mask h) l → c2.testBit h = true) ∧ (3 ≤ kills (mask h) l → c3.testBit h = true)

lemma cov_bit (l : List Wr) (i : ℕ) : (covL l).testBit i = l.any fun a => a.s.testBit i := by
  induction l with
  | nil => simp [covL]
  | cons a l ih => rw [covL, lor_bit, ih, List.any_cons]

lemma fl_bit (l : List Wr) (i : ℕ) : (flL l).testBit i = l.any fun a => a.f.testBit i := by
  induction l with
  | nil => simp [flL]
  | cons a l ih => rw [flL, lor_bit, ih, List.any_cons]

lemma sepN_bit (L w i : ℕ) :
    (sepN L w).testBit i = ((w.testBit i != w.testBit (143 + i)) && L.testBit i) := by
  rw [sepN, land_bit, xor_bit, shr_bit]

lemma rep_cov {L H y : ℕ} {mask : ℕ → ℕ}
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) {v : List Wr} {l : List St}
    (hr : Rep L H mask v (need y l)) : covL v = L := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [cov_bit]
  cases hi : L.testBit i
  · rw [List.any_eq_false]
    intro u hu
    rw [hr.sep u hu, sepN_bit, hi]; simp
  · rw [List.any_eq_true]
    by_contra hc
    push Not at hc
    refine hL i hi (need_agree l fun x hx => ?_)
    obtain ⟨u, hu, rfl⟩ := (hr.mem x).mp hx
    have := hc u hu
    rw [hr.sep u hu, sepN_bit, hi] at this
    cases h1 : u.w.testBit i <;> cases h2 : u.w.testBit (143 + i) <;> simp_all

lemma rep_len {L H : ℕ} {mask : ℕ → ℕ} {v : List Wr} {S : Finset ℕ} (hr : Rep L H mask v S) :
    v.length = S.card := by
  have e : S = (v.map Wr.w).toFinset := by
    ext x; rw [hr.mem, List.mem_toFinset, List.mem_map]
  rw [e, List.toFinset_card_of_nodup hr.nd, List.length_map]

lemma flag_forced {H y : ℕ} {mask : ℕ → ℕ} (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    {l : List St} {d1 d2 d3 : ℕ} (hb : Bud H mask d1 d2 d3 l) {f x : ℕ} (hx : x ∈ need y l)
    (hf : ∀ h, f.testBit h = true → h < H ∧ Nat.land x (mask h) = 0) : sub f d1 = true := by
  refine sub_true fun h hh => ?_
  obtain ⟨h1, h2⟩ := hf h hh
  exact (hb h h1).2.1 (kill_forced (hy h h1) l hx h2)

lemma tryG_true {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {v rest : List Wr} {a b : Wr} {l : List St} {g fg last d1 d2 d3 m : ℕ} {uses : Bool}
    (hm : m = v.length) (hv : Rep L H mask v (insert a.w (insert b.w ((need y l).erase g))))
    (hp : v.Perm (a :: b :: rest)) (hg : g ∈ need y l) (hg0 : g ≠ 0) (hab : a.w ≠ b.w)
    (hgS : g ∉ insert a.w (insert b.w ((need y l).erase g)))
    (hfg : ∀ h, fg.testBit h = true → h < H ∧ Nat.land g (mask h) = 0)
    (hcard : (need y l).card ≤ k + 1) (hord : uses = true ∨ last ≤ g)
    (hb : Bud H mask d1 d2 d3 l)
    (hr : ∀ v', Rep L H mask v' (need y l) → r v' d1 d2 d3 g = true) :
    tryG L r k m rest (covL rest) d1 d2 d3 a b last uses g fg = true := by
  have hga : g ≠ a.w := fun e => hgS (by simp [e])
  have hgb : g ≠ b.w := fun e => hgS (by simp [e])
  have nd2 : ((a :: b :: rest).map Wr.w).Nodup := (hp.map Wr.w).nodup_iff.mp hv.nd
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at nd2
  obtain ⟨⟨_, har⟩, hbr, hrr⟩ := nd2
  have memr (x : ℕ) : x ∈ rest.map Wr.w ↔ x ∈ need y l ∧ x ≠ g ∧ x ≠ a.w ∧ x ≠ b.w := by
    have h1 : (x ∈ insert a.w (insert b.w ((need y l).erase g))) ↔ ∃ u ∈ a :: b :: rest, u.w = x := by
      rw [hv.mem]; exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hp.mem_iff.mp hu, e⟩, fun ⟨u, hu, e⟩ => ⟨u, hp.mem_iff.mpr hu, e⟩⟩
    rw [List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h2 := h1.mpr ⟨u, by simp [hu], rfl⟩
      have n1 : u.w ≠ a.w := fun e => har (e ▸ List.mem_map_of_mem hu)
      have n2 : u.w ≠ b.w := fun e => hbr (e ▸ List.mem_map_of_mem hu)
      simp only [Finset.mem_insert, Finset.mem_erase] at h2
      rcases h2 with h | h | ⟨h3, h4⟩
      · exact absurd h n1
      · exact absurd h n2
      · exact ⟨h4, h3, n1, n2⟩
    · rintro ⟨h2, h3, h4, h5⟩
      obtain ⟨u, hu, e⟩ := h1.mp (by simp [h2, h3])
      simp only [List.mem_cons] at hu
      rcases hu with rfl | rfl | hu
      · exact absurd e.symm h4
      · exact absurd e.symm h5
      · exact ⟨u, hu, e⟩
  have hgr : g ∉ rest.map Wr.w := fun h => ((memr g).mp h).2.1 rfl
  have sepr : ∀ u ∈ rest, u.s = sepN L u.w := fun u hu => hv.sep u (hp.mem_iff.mpr (by simp [hu]))
  have flr : ∀ u ∈ rest, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0 :=
    fun u hu => hv.fl u (hp.mem_iff.mpr (by simp [hu]))
  have sepa := hv.sep a (hp.mem_iff.mpr (by simp))
  have sepb := hv.sep b (hp.mem_iff.mpr (by simp))
  have fla := hv.fl a (hp.mem_iff.mpr (by simp))
  have flb := hv.fl b (hp.mem_iff.mpr (by simp))
  have len : v.length = rest.length + 2 := by rw [hp.length_eq]; simp
  have b1 : Nat.beq g 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hg0
  have b2 : Nat.beq g a.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hga
  have b3 : Nat.beq g b.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hgb
  have b4 : (cond uses true (Nat.ble last g)) = true := by
    rcases hord with h | h
    · rw [h]; rfl
    · cases uses
      · exact Nat.ble_eq.mpr h
      · rfl
  have b5 : sub fg d1 = true := flag_forced hy hb hg hfg
  have b6 : absentL g rest = true :=
    absent_true fun x hx e => hgr (e ▸ List.mem_map_of_mem hx)
  set G : Wr := ⟨g, sepN L g, fg⟩ with hG
  unfold tryG
  rw [b1, b2, b3, b4, b5, force_eq, force_eq, b6]
  simp only [cond_false, cond_true]
  by_cases hA : a.w ∈ need y l <;> by_cases hB : b.w ∈ need y l
  · have R : Rep L H mask (G :: a :: b :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hga, hgb, hgr⟩, ⟨hab, har⟩, hbr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact ⟨a, by simp, e2.symm⟩
          by_cases e3 : x = b.w
          · exact ⟨b, by simp, e3.symm⟩
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | rfl | hu
          · exact hg
          · exact hA
          · exact hB
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | rfl | hu
        · rfl
        · exact sepa
        · exact sepb
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | rfl | hu
        · exact hfg
        · exact fla
        · exact flb
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have c2 : Nat.ble m k = true := by rw [Nat.ble_eq]; omega
    rw [c1, c2, flag_forced hy hb hA fla, flag_forced hy hb hB flb, hr _ R]
    simp
  · have R : Rep L H mask (G :: a :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hga, hgr⟩, har, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact ⟨a, by simp, e2.symm⟩
          by_cases e3 : x = b.w
          · exact absurd (e3 ▸ hx) hB
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | hu
          · exact hg
          · exact hA
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · rfl
        · exact sepa
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · exact hfg
        · exact fla
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have cv : Nat.beq (Nat.lor (Nat.lor (covL rest) (sepN L g)) a.s) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> cases a.s.testBit i <;> rfl
    rw [c1, flag_forced hy hb hA fla, cv, hr _ R]
    simp
  · have R : Rep L H mask (G :: b :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨hgb, hgr⟩, hbr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact absurd (e2 ▸ hx) hA
          by_cases e3 : x = b.w
          · exact ⟨b, by simp, e3.symm⟩
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | rfl | hu
          · exact hg
          · exact hB
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · rfl
        · exact sepb
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | rfl | hu
        · exact hfg
        · exact flb
        · exact flr u hu
    have hl := rep_len R
    simp only [List.length_cons] at hl
    have c1 : Nat.ble m (Nat.succ k) = true := by rw [Nat.ble_eq]; omega
    have cv : Nat.beq (Nat.lor (Nat.lor (covL rest) (sepN L g)) b.s) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> cases b.s.testBit i <;> rfl
    rw [c1, flag_forced hy hb hB flb, cv, hr _ R]
    simp
  · have R : Rep L H mask (G :: rest) (need y l) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨hgr, hrr⟩
      · intro x
        constructor
        · intro hx
          by_cases e1 : x = g
          · exact ⟨G, by simp, e1.symm⟩
          by_cases e2 : x = a.w
          · exact absurd (e2 ▸ hx) hA
          by_cases e3 : x = b.w
          · exact absurd (e3 ▸ hx) hB
          obtain ⟨u, hu, e⟩ := List.mem_map.mp ((memr x).mpr ⟨hx, e1, e2, e3⟩)
          exact ⟨u, by simp [hu], e⟩
        · rintro ⟨u, hu, rfl⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact hg
          · exact ((memr _).mp (List.mem_map_of_mem hu)).1
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · rfl
        · exact sepr u hu
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact hfg
        · exact flr u hu
    have cv : Nat.beq (Nat.lor (covL rest) (sepN L g)) L = true := by
      rw [Nat.beq_eq]
      refine Eq.trans ?_ (rep_cov hL R)
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [covL, lor_bit, hG]
      cases (covL rest).testBit i <;> cases (sepN L g).testBit i <;> rfl
    rw [cv, hr _ R]
    simp

lemma kills_cons (m : ℕ) (s : St) (l : List St) :
    kills m (s :: l) = kills m l + if killB m s = true then 1 else 0 := by
  rw [kills, kills, List.countP_cons]

lemma bud_next {H c1 c2 c3 K : ℕ} {mask : ℕ → ℕ} {s : St} {l : List St}
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hK : ∀ h, K.testBit h = true → h < H ∧ killB (mask h) s = true) :
    sub K c1 = true ∧ Bud H mask (Nat.lor c2 (Nat.xor c1 (Nat.land c1 K)))
      (Nat.lor c3 (Nat.xor c2 (Nat.land c2 K))) (Nat.xor c3 (Nat.land c3 K)) l := by
  constructor
  · refine sub_true fun h hh => ?_
    obtain ⟨h1, h2⟩ := hK h hh
    refine (hb h h1).2.1 ?_
    rw [kills_cons, if_pos h2]; omega
  · intro h hh
    obtain ⟨b0, b1, b2, b3⟩ := hb h hh
    rw [kills_cons] at b0 b1 b2 b3
    simp only [lor_bit, xor_bit, land_bit]
    cases hk : K.testBit h
    · refine ⟨by split_ifs at b0 <;> omega, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
      · rw [b1 (by omega)]; simp
      · rw [b2 (by omega)]; simp
      · rw [b3 (by omega)]; simp
    · rw [if_pos (hK h hk).2] at b0 b1 b2 b3
      refine ⟨by omega, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
      · rw [b2 (by omega)]; simp
      · rw [b3 (by omega)]; simp
      · omega

lemma tryP_true {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {v rest : List Wr} {a b : Wr} {s : St} {l : List St} {last c1 c2 c3 m : ℕ} (t : Fin 4)
    (ht : opN t a.w b.w = s.val) (hm : m = v.length)
    (hv : Rep L H mask v (insert a.w (insert b.w ((need y l).erase s.val))))
    (hp : v.Perm (a :: b :: rest)) (hg : s.val ∈ need y l) (hg0 : s.val ≠ 0) (hab : a.w ≠ b.w)
    (hgS : s.val ∉ insert a.w (insert b.w ((need y l).erase s.val)))
    (hcard : (need y l).card ≤ k + 1) (hord : a.w = last ∨ b.w = last ∨ last ≤ s.val)
    (hkill : ∀ m, Nat.land a.w m = 0 ∨ Nat.land b.w m = 0 → killB m s = true)
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hr : ∀ v' d1 d2 d3, Rep L H mask v' (need y l) → Bud H mask d1 d2 d3 l →
      r v' d1 d2 d3 s.val = true) :
    tryP L r k m c1 c2 c3 last a b rest = true := by
  have fla := hv.fl a (hp.mem_iff.mpr (by simp))
  have flb := hv.fl b (hp.mem_iff.mpr (by simp))
  have hK : ∀ h, (Nat.lor a.f b.f).testBit h = true → h < H ∧ killB (mask h) s = true := by
    intro h hh
    rw [lor_bit, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨(fla h hh).1, hkill _ (Or.inl (fla h hh).2)⟩
    · exact ⟨(flb h hh).1, hkill _ (Or.inr (flb h hh).2)⟩
  obtain ⟨b1, hb'⟩ := bud_next hb hK
  have b2 : sub (flL rest) (Nat.lor c2 (Nat.xor c1 (Nat.land c1 (Nat.lor a.f b.f)))) = true := by
    refine sub_true fun h hh => ?_
    rw [fl_bit, List.any_eq_true] at hh
    obtain ⟨u, hu, hf⟩ := hh
    have uv := hp.mem_iff.mpr (show u ∈ a :: b :: rest by simp [hu])
    obtain ⟨h1, h2⟩ := hv.fl u uv h hf
    refine (hb' h h1).2.1 (kill_forced (hy h h1) l ?_ h2)
    have hS := (hv.mem u.w).mpr ⟨u, uv, rfl⟩
    have nd2 : ((a :: b :: rest).map Wr.w).Nodup := (hp.map Wr.w).nodup_iff.mp hv.nd
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at nd2
    obtain ⟨⟨_, har⟩, hbr, _⟩ := nd2
    simp only [Finset.mem_insert, Finset.mem_erase] at hS
    rcases hS with e | e | ⟨_, e⟩
    · exact absurd (e ▸ List.mem_map_of_mem hu) har
    · exact absurd (e ▸ List.mem_map_of_mem hu) hbr
    · exact e
  have hord' : (Nat.beq a.w last || Nat.beq b.w last) = true ∨ last ≤ s.val := by
    rcases hord with h | h | h
    · left; rw [h, Nat.beq_refl]; rfl
    · left; rw [h, Nat.beq_refl]; exact Bool.or_true _
    · exact Or.inr h
  have G (fg : ℕ) (hfg : ∀ h, fg.testBit h = true → h < H ∧ Nat.land s.val (mask h) = 0) :=
    tryG_true (m := m) (last := last) (uses := Nat.beq a.w last || Nat.beq b.w last) (fg := fg)
      hy hL hm hv hp hg hg0 hab hgS hfg hcard hord' hb' (fun v' hv' => hr v' _ _ _ hv' hb')
  have z (c x : ℕ) : Nat.land (opN t a.w b.w) c = opN t (Nat.land a.w c) (Nat.land b.w c) :=
    land_op t _ _ c
  unfold tryP
  rw [force_eq, b1]
  simp only [cond_true, force_eq]
  rw [b2]
  simp only [cond_true]
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
  fin_cases t
  · left
    have e : Nat.land a.w b.w = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [lor_bit, Bool.or_eq_true] at hh
    rw [← ht]
    refine ⟨(hK h (by rw [lor_bit, Bool.or_eq_true]; exact hh)).1, ?_⟩
    rw [z _ 0]
    rcases hh with hh | hh
    · rw [(fla h hh).2]
      rcases opN_zero_left 0 (Nat.land b.w (mask h)) with e | e
      · exact e
      · apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
    · rw [(flb h hh).2]
      apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; left
    have e : Nat.lor a.w b.w = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [land_bit, Bool.and_eq_true] at hh
    rw [← ht]
    refine ⟨(fla h hh.1).1, ?_⟩
    rw [z _ 0, (fla h hh.1).2, (flb h hh.2).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; right; left
    have e : Nat.xor a.w (Nat.land a.w b.w) = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [← ht]
    refine ⟨(fla h hh).1, ?_⟩
    rw [z _ 0, (fla h hh).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]
  · right; right; right
    have e : Nat.xor b.w (Nat.land a.w b.w) = s.val := ht
    rw [e]
    refine G _ fun h hh => ?_
    rw [← ht]
    refine ⟨(flb h hh).1, ?_⟩
    rw [z _ 0, (flb h hh).2]
    apply Nat.eq_of_testBit_eq; intro i; rw [opN_bit]; simp [opB]

lemma level {L H y k : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    {r : Next} {W : Set ℕ} {v : List Wr} {s : St} {l : List St} {last c1 c2 c3 : ℕ}
    (hV : Valid y W (s :: l)) (h0 : 0 ∈ W) (hU : Useful y (s :: l)) (hk : (s :: l).length ≤ k + 1)
    (hC : Chain last (s :: l)) (hv : Rep L H mask v (need y (s :: l)))
    (hb : Bud H mask c1 c2 c3 (s :: l))
    (hr : ∀ v' d1 d2 d3, Rep L H mask v' (need y l) → Bud H mask d1 d2 d3 l →
      r v' d1 d2 d3 s.val = true) :
    anyP (tryP L r k (lenL v) c1 c2 c3 last) (pairsA [] v) = true := by
  obtain ⟨fa, fb, fab, fv, _, _, fS⟩ := step_facts hV h0
  obtain ⟨ua, hua, ea⟩ := (hv.mem s.a).mp (by simp [need])
  obtain ⟨ub, hub, eb⟩ := (hv.mem s.b).mp (by simp [need])
  have hne : ua ≠ ub := fun e => fab (by rw [← ea, ← eb, e])
  obtain ⟨rest, hmem, hperm⟩ := pairsA_spec ua ub hne v [] hua hub
  have hcard : (need y l).card ≤ k + 1 := by
    have := need_card l hU.2
    simp only [List.length_cons] at hk
    omega
  have hg := hU.1
  have eN : need y (s :: l) = insert s.a (insert s.b ((need y l).erase s.val)) := rfl
  rcases hmem with hm | hm
  · refine anyP_true hm (tryP_true hy hL s.t (by rw [ea, eb]; rfl) (lenL_eq v) ?_ hperm hg fv
      (by rw [ea, eb]; exact fab) ?_ hcard ?_ ?_ hb hr)
    · rw [ea, eb]; exact hv
    · rw [ea, eb]; exact fS
    · rw [ea, eb]; exact hC.1
    · intro m h
      rw [ea, eb] at h
      unfold killB
      rcases h with h | h
      · rw [h]; rfl
      · rw [h]; exact Bool.or_true _
  · have hv2 : Rep L H mask v (insert ub.w (insert ua.w ((need y l).erase s.val))) := by
      rw [ea, eb, Finset.insert_comm]; exact hv
    refine anyP_true hm (tryP_true hy hL (swapT s.t) ?_ (lenL_eq v) hv2
      (hperm.trans (List.Perm.swap ub ua rest)) hg fv (by rw [ea, eb]; exact fab.symm) ?_ hcard ?_ ?_
      hb hr)
    · rw [ea, eb, ← opN_swap]; rfl
    · rw [ea, eb, Finset.insert_comm]; exact fS
    · rw [ea, eb]
      rcases hC.1 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · intro m h
      rw [ea, eb] at h
      unfold killB
      rcases h with h | h
      · rw [h]; exact Bool.or_true _
      · rw [h]; rfl

lemma isT_true {L H y : ℕ} {mask : ℕ → ℕ} {v : List Wr} (hv : Rep L H mask v (need y [])) :
    isT y v = true := by
  have hl := rep_len hv
  rw [need, Finset.card_singleton] at hl
  obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hl
  have : u.w ∈ need y [] := (hv.mem u.w).mpr ⟨u, by simp, rfl⟩
  rw [need, Finset.mem_singleton] at this
  rw [isT, this, Nat.beq_refl]

theorem search_complete {L H y : ℕ} {mask : ℕ → ℕ}
    (hy : ∀ h < H, Nat.land y (mask h) ≠ 0)
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) (k : ℕ) :
    ∀ (l : List St) (W : Set ℕ) (v : List Wr) (last c1 c2 c3 : ℕ), Valid y W l → 0 ∈ W →
      Useful y l → l.length ≤ k → Chain last l → Rep L H mask v (need y l) →
      Bud H mask c1 c2 c3 l → search L y k v c1 c2 c3 last = true := by
  induction k with
  | zero =>
    intro l W v last c1 c2 c3 hV h0 hU hk hC hv hb
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact isT_true hv
  | succ k ih =>
    intro l W v last c1 c2 c3 hV h0 hU hk hC hv hb
    rw [search, Bool.or_eq_true]
    cases l with
    | nil => exact Or.inl (isT_true hv)
    | cons s l =>
      refine Or.inr (level hy hL hV h0 hU hk hC hv hb fun v' d1 d2 d3 hv' hb' => ?_)
      exact ih l _ v' s.val d1 d2 d3 hV.2.2.2 (Or.inr h0) hU.2 (by simpa using hk) hC.2 hv' hb'


-- Part 4: from derivations to the search, and the theta graph.

lemma need_ne_zero {y : ℕ} (hy : y ≠ 0) (l : List St) : ∀ {W : Set ℕ}, Valid y W l → 0 ∈ W →
    ∀ x ∈ need y l, x ≠ 0 := by
  induction l with
  | nil => intro W _ _ x hx; rw [need, Finset.mem_singleton] at hx; rw [hx]; exact hy
  | cons s l ih =>
    intro W h h0 x hx
    obtain ⟨fa, fb, _⟩ := step_facts h h0
    rw [need, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | rfl | ⟨_, h2⟩
    · exact fa
    · exact fb
    · exact ih h.2.2.2 (Or.inr h0) x h2

def neededB (L : ℕ) (ws : List Wr) : Bool :=
  ws.all fun u => !(Nat.beq (covL (ws.filter fun x => !(Nat.beq x.w u.w))) L)

lemma root_rep {L H y : ℕ} {mask : ℕ → ℕ}
    (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i)) (hy : y ≠ 0)
    {ws : List Wr} (hnd : (ws.map Wr.w).Nodup) (hs : ∀ u ∈ ws, u.s = sepN L u.w)
    (hf : ∀ u ∈ ws, ∀ h, u.f.testBit h = true → h < H ∧ Nat.land u.w (mask h) = 0)
    (hn : neededB L ws = true) {W : Set ℕ} {l : List St} (hV : Valid y W l) (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x) : Rep L H mask ws (need y l) := by
  have hsub : ∀ x ∈ need y l, ∃ u ∈ ws, u.w = x := fun x hx =>
    (hW x (need_sub l hV x hx)).resolve_left (need_ne_zero hy l hV h0 x hx)
  refine ⟨hnd, fun x => ⟨hsub x, ?_⟩, hs, hf⟩
  rintro ⟨u, hu, rfl⟩
  by_contra hc
  have hc1 := List.all_eq_true.mp hn u hu
  have hc2 : covL (ws.filter fun x => !(Nat.beq x.w u.w)) = L := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [cov_bit]
    cases hi : L.testBit i
    · rw [List.any_eq_false]
      intro q hq
      rw [hs q (List.mem_of_mem_filter hq), sepN_bit, hi]; simp
    · rw [List.any_eq_true]
      by_contra hd
      push Not at hd
      refine hL i hi (need_agree l fun x hx => ?_)
      obtain ⟨q, hq, rfl⟩ := hsub x hx
      have hne : q.w ≠ u.w := fun e => hc (e ▸ hx)
      have hq' : q ∈ ws.filter fun x => !(Nat.beq x.w u.w) := by
        rw [List.mem_filter]
        refine ⟨hq, ?_⟩
        have : Nat.beq q.w u.w = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hne
        rw [this]; rfl
      have := hd q hq'
      rw [hs q hq, sepN_bit, hi] at this
      cases h1 : q.w.testBit i <;> cases h2 : q.w.testBit (143 + i) <;> simp_all
  rw [hc2, Nat.beq_refl] at hc1
  exact Bool.false_ne_true hc1

-- no derivation when the plain search fails
theorem refute {L y K : ℕ} (hL : ∀ i, L.testBit i = true → y.testBit i ≠ y.testBit (143 + i))
    (hy : y ≠ 0) {ws : List Wr} (hnd : (ws.map Wr.w).Nodup) (hs : ∀ u ∈ ws, u.s = sepN L u.w)
    (hf : ∀ u ∈ ws, u.f = 0) (hn : neededB L ws = true)
    (hsearch : search L y K ws 0 0 0 0 = false) {W : Set ℕ} (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x) : ¬ Der opN K W y := by
  intro h
  obtain ⟨l, hk, hV, hU, hC, _⟩ := exists_sorted h
  have hrep : Rep L 0 (fun _ => 0) ws (need y l) :=
    root_rep hL hy hnd hs (fun u hu h hh => by rw [hf u hu] at hh; simp at hh) hn hV h0 hW
  have := search_complete (H := 0) (mask := fun _ => 0) (fun h hh => by omega) hL K l W ws 0 0 0 0
    hV h0 hU hk hC hrep (fun h hh => by omega)
  rw [hsearch] at this
  exact Bool.false_ne_true this

lemma anyP_append (p : Wr → Wr → List Wr → Bool) (a b : List (Wr × Wr × List Wr)) :
    anyP p (a ++ b) = (anyP p a || anyP p b) := by
  induction a with
  | nil => rfl
  | cons x l ih => rw [List.cons_append, anyP, anyP, ih, Bool.or_assoc]

lemma anyP_chunks (p : Wr → Wr → List Wr → Bool) (m : ℕ) (n : ℕ) :
    ∀ l : List (Wr × Wr × List Wr), l.length ≤ m * n →
      (∀ i < n, anyP p ((l.drop (m * i)).take m) = false) → anyP p l = false := by
  induction n with
  | zero =>
    intro l hl _
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    rw [this]; rfl
  | succ n ih =>
    intro l hl h
    rw [← List.take_append_drop m l, anyP_append]
    have h1 := h 0 (by omega)
    rw [Nat.mul_zero, List.drop_zero] at h1
    rw [h1, Bool.false_or]
    refine ih _ (by rw [List.length_drop, Nat.mul_succ] at *; omega) fun i hi => ?_
    have := h (i + 1) (by omega)
    rw [List.drop_drop, show m + m * i = m * (i + 1) by ring]
    exact this

structure Kid where
  v : List Wr
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  g : ℕ

def eqL : List Wr → List Wr → Bool
  | [], [] => true
  | a :: l, b :: m => Nat.beq a.w b.w && (Nat.beq a.s b.s && (Nat.beq a.f b.f && eqL l m))
  | _, _ => false

lemma eqL_eq (a : List Wr) : ∀ b, eqL a b = true → a = b := by
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons => simp [eqL] at h
  | cons x l ih =>
    intro b h
    cases b with
    | nil => simp [eqL] at h
    | cons y m =>
      rw [eqL, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq,
        Nat.beq_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      rw [ih m h4]
      cases x; cases y
      simp only at h1 h2 h3
      rw [h1, h2, h3]

def isKid (v : List Wr) (c1 c2 c3 g : ℕ) : List Kid → Bool
  | [] => false
  | q :: l => (Nat.beq q.g g && (Nat.beq q.c1 c1 && (Nat.beq q.c2 c2 && (Nat.beq q.c3 c3 &&
      eqL q.v v)))) || isKid v c1 c2 c3 g l

lemma isKid_mem {v : List Wr} {c1 c2 c3 g : ℕ} (ks : List Kid)
    (h : isKid v c1 c2 c3 g ks = true) : ⟨v, c1, c2, c3, g⟩ ∈ ks := by
  induction ks with
  | nil => simp [isKid] at h
  | cons q l ih =>
    rw [isKid, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have := eqL_eq _ _ h5
      cases q
      simp only at h1 h2 h3 h4 this
      subst h1 h2 h3 h4 this
      simp
    · exact List.mem_cons_of_mem _ (ih h)

def memN (g : ℕ) : List ℕ → Bool
  | [] => false
  | x :: l => Nat.beq x g || memN g l

def rootNext (al : List ℕ) (ks : List Kid) : Next := fun v c1 c2 c3 g =>
  cond (memN g al) (!(isKid v c1 c2 c3 g ks)) false

-- row permutations

def Bdd (N x : ℕ) : Prop := ∀ i, N ≤ i → x.testBit i = false

lemma bdd_op {N : ℕ} (t : Fin 4) {a b : ℕ} (ha : Bdd N a) (hb : Bdd N b) : Bdd N (opN t a b) := by
  intro i hi
  rw [opN_bit, ha i hi, hb i hi]
  fin_cases t <;> rfl

def sIdx (T : ℕ) (i : ℕ) : ℕ :=
  cond (Nat.blt i 143) (Nat.land (Nat.shiftRight T (8 * i)) 255)
    (143 + Nat.land (Nat.shiftRight T (8 * (i - 143))) 255)

def sg (N T : ℕ) (w : ℕ) : ℕ := Nat.ofBits fun i : Fin N => w.testBit (sIdx T i.val)

lemma sg_bit (N T w i : ℕ) (hi : i < N) : (sg N T w).testBit i = w.testBit (sIdx T i) := by
  rw [sg, Nat.testBit_ofBits_lt _ _ hi]

lemma sg_bdd (N T w : ℕ) : Bdd N (sg N T w) := fun i hi => by rw [sg, Nat.testBit_ofBits_ge _ _ hi]

lemma sg_op (N T : ℕ) (t : Fin 4) (a b : ℕ) : sg N T (opN t a b) = opN t (sg N T a) (sg N T b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, opN_bit, opN_bit, sg_bit _ _ _ _ hi, sg_bit _ _ _ _ hi]
  · rw [sg_bdd _ _ _ i (by omega), bdd_op t (sg_bdd N T a) (sg_bdd N T b) i (by omega)]

lemma sg_sg {N : ℕ} (T : ℕ) (hT : ∀ i < N, sIdx T i < N ∧ sIdx T (sIdx T i) = i) {w : ℕ} (hw : Bdd N w) :
    sg N T (sg N T w) = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, sg_bit _ _ _ _ (hT i hi).1, (hT i hi).2]
  · rw [sg_bdd _ _ _ i (by omega), hw i (by omega)]

def mapSt (N T : ℕ) (s : St) : St := ⟨s.t, sg N T s.a, sg N T s.b⟩

lemma mapSt_val (N T : ℕ) (s : St) : (mapSt N T s).val = sg N T s.val := (sg_op N T _ _ _).symm

lemma valid_map {N : ℕ} (T : ℕ) (hT : ∀ i < N, sIdx T i < N ∧ sIdx T (sIdx T i) = i) {y : ℕ}
    (l : List St) : ∀ {W : Set ℕ}, (∀ x ∈ W, Bdd N x) → Valid y W l →
      Valid (sg N T y) (sg N T '' W) (l.map (mapSt N T)) := by
  induction l with
  | nil => intro W _ h; exact ⟨y, h, rfl⟩
  | cons s l ih =>
    intro W hb h
    obtain ⟨ha, hb', hc, hv⟩ := h
    have bv : Bdd N s.val := bdd_op s.t (hb _ ha) (hb _ hb')
    refine ⟨⟨s.a, ha, rfl⟩, ⟨s.b, hb', rfl⟩, ?_, ?_⟩
    · rw [mapSt_val]
      rintro ⟨x, hx, e⟩
      have := congrArg (sg N T) e
      rw [sg_sg T hT (hb x hx), sg_sg T hT bv] at this
      exact hc (this ▸ hx)
    · rw [mapSt_val, ← Set.image_insert_eq]
      refine ih ?_ hv
      rintro x (rfl | hx)
      · exact bv
      · exact hb x hx

lemma sg_eq {N T x x' : ℕ} (hx' : Bdd N x') (h : ∀ i < N, x'.testBit i = x.testBit (sIdx T i)) :
    sg N T x = x' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · rw [sg_bit _ _ _ _ hi, h i hi]
  · rw [sg_bdd _ _ _ i (by omega), hx' i (by omega)]

lemma bdd_of_lt {N x : ℕ} (h : x < 2 ^ N) : Bdd N x := fun i hi =>
  Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))


-- Part 5: data of the theta graph and the searches.

def LO : ℕ := 0x7fffffffffffffffffffffffffffffffffff

def ipL : List ℕ := [0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f]

def ip (i : Fin 7) : ℕ := ipL.getD i.val 0

def maskL : List ℕ := [0x78f1e3c78f1e3c58a850404fffffffffffffffffffff01fc00000000000ffffffffffff, 0x39f3e7cf9f3e7cfa75ffffffad9022fffffffffffff80fe0000003ffffff000000ffffff, 0xe1c3870e1c38707fe005fffd26fff802ffffffffc07ffe03f8ffc001fff001fff000fff, 0x1ab56ad5ab56ad58fe2ff2bf87f0ffa5faaf80fe03ffffffffb1fc1fe03f0fe0ff03f00f, 0x3a74e9d3a74e9d3b7f7afbfb18f38f8e78faff01fffff01ffff6fce1e7c031e70f1cf1f0, 0x274e9d3a74e9d3af9fd33d63fb7fdd5a9d59fffe03f80fffffdf3f2678c7f6eb30253233, 0x35ebd7af5ebd7affa7ffadcdffbf71ffd7750001fc07ffffffff4fde1b1bff74c3d80cc0]

def mask (h : ℕ) : ℕ := maskL.getD h 0

def root : List Wr := [⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩, ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩]

def pm (p : Fin 3) (i : Fin 7) : Fin 7 :=
  match p with
  | 0 => ![3, 6, 2, 0, 5, 4, 1] i
  | 1 => ![4, 6, 2, 5, 0, 3, 1] i
  | 2 => ![5, 1, 2, 4, 3, 0, 6] i

def Tn (p : Fin 3) : ℕ :=
  match p with
  | 0 => 0x5d585a5b595c57726d6f706e716c6b666869676a65645f616260635e87828485838681807b7d7e7c7f7a797476777578738e898b8c8a8d884515123a3736082309212005044746494856171614132e2f2c2d3938533c3b5251240b0a2207063f403d3e110e0f10270c0d354f324d4c02031a1b1c1d00014443554241542b28292a252634334e5031304b4a1e1f1819
  | 1 => 0x6c6d6f706e717257585a5b595c5d7a7b7d7e7c7f805e5f616260636488898b8c8a8d8e65666869676a6b73747677757879818284858386871115103503023223091d1c0100434416172b484941422e2f292a3334240a0b1e1f533b3c5030313f400e0f453d3e12270c0d3a4f081a1b36374d4c2021040546475513142856542c2d252638394e220607181952514b4a
  | 2 => 0x81868584838287888d8c8b8a898e656a696867666b73787776757479575c5b5a59585d7a7f7e7d7c7b805e636261605f646c71706f6e6d722b5528241e1f224f4e1a1b1819161743441146471314403f0f0e0a0b35333403023a38390806072f2e2a29562d2c542726255323501d1c515221204c4d4a4b48491541421045123e3d0d0c3b3c09323031010037360504

def allowed : List ℕ := [0x3ffffc000000000000000000, 0x1fc07000000000ffe000000000, 0xfe00009031e183f000000000000, 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc]

def L0 : ℕ := 0xf1e3c78f003c00000000000ffffffffffff
def Y0 : ℕ := 0x7ffffffff01fc00000000000ffffffffffff
def ws0 : List Wr := [⟨0x60c183060c183058a000000526fdd00000000000007f01fc00000000000ffffff000000, 0xc1830603000c000000000005b2045000000, 0⟩, ⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060c603003000000000000a4c000005000, 0⟩, ⟨0x50a142850a1428500800400780f005a05507f01fc000000000000000000f01f00fc0ff0, 0x5141450a002800000000000000100480550, 0⟩, ⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xb082c58b002c00000000000000010000005, 0⟩, ⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x1023808e00040000000000000148a900880, 0⟩, ⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0xb1610584001000000000000000a2027a22a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub0 : search L0 Y0 7 ws0 0 0 0 0 = false := by decide +kernel

def L1 : ℕ := 0x73e7cf980e60000003ffffff000000ffffff
def Y1 : ℕ := 0x7ffffff80fe0000003ffffff000000ffffff
def ws1 : List Wr := [⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe0000003ffffff000000000000, 0x70e1c38000600000010a0809000000000000, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f80000000003ffe000000000fff000, 0x63c78c800c6000000000a000000000005000, 0⟩, ⟨0x2142850a142850a201d00d402800005a05507f01fc000000000003e01fc0000000fc0ff0, 0x3184c6100840000000400540000000480550, 0⟩, ⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3e00c180e00000002141036000000000005, 0⟩, ⟨0x18b162c58b162c50602cc29c048022a562a60001fc000000000000d98738000000dacdcc, 0x316309880620000000800200000000900880, 0⟩, ⟨0x8102040810204005000523200000200288afffe03f8000000000021e4e400000027f33f, 0x63c64318020000000021408000000027a22a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub1 : search L1 Y1 6 ws1 0 0 0 0 = false := by decide +kernel

def L2 : ℕ := 0x1c387001c3800e0ffc001fff001fff000fff
def Y2 : ℕ := 0x7ffffc07ffe03f8ffc001fff001fff000fff
def ws2 : List Wr := [⟨0x81020408102040274005bfb000000000000000000000fe03f8ffc001fff000000000000, 0x102040010180060b14000809000000000000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18300101800804e8000000000045000000, 0⟩, ⟨0x40810204081020700000d40500f000005507f01fc000000000e00001fc0001f00000ff0, 0x141050008100040000000540000100000550, 0⟩, ⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x82820008280040000001036000010000005, 0⟩, ⟨0x8102040810204006000429c0000228022a60001fc07f0000000c00007380014cf000dcc, 0x10203000c20008000000020000148a000880, 0⟩, ⟨0xa142850a14285005800523200408e00288afffe000000000000b00004e4000b3c00033f, 0x810500142800a0000000080000a2000022a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub2 : search L2 Y2 7 ws2 0 0 0 0 = false := by decide +kernel

def L3 : ℕ := 0x6a01ab56ad5ab1fc1fe03f0fe0ff03f00f
def Y3 : ℕ := 0xfe03ffffffffb1fc1fe03f0fe0ff03f00f
def ws3 : List Wr := [⟨0x183060c183060c18742af2bb000000000000000000000fe03fb1fc1fe03f000000000000, 0x60018300ac0281140a0009000000000000, 0⟩, ⟨0x2040810204081008a0000000260dd00000000000007f01fffb1fc0000000fe0ff000000, 0x80023108c58b0e80000000b2045000000, 0⟩, ⟨0x10a142850a142858002fa00005900025d000000003f8001fc030001fe0000fe00003f000, 0x4200a2142510800000a00004c000005000, 0⟩, ⟨0x810204081020408005000487007021820500fe00000fe00001001e003f0e00f003000f, 0x6800081680408000140036000010000005, 0⟩, ⟨0x18b162c58b162c50602cc29c048022a562a600000007f0000020c01980380900cf02c00c, 0x620188462c58800000000000008a000000, 0⟩, ⟨0xa142850a14285005800523200408e00288a80fe03f800000000b001e02400803c03f00f, 0x42010942850a000001400000002003a00a, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub3 : search L3 Y3 7 ws3 0 0 0 0 = false := by decide +kernel

def L4 : ℕ := 0x7401d3a7401d3a76fce1e7c031e70f1cf1f0
def Y4 : ℕ := 0x7f01fffff01ffff6fce1e7c031e70f1cf1f0
def ws4 : List Wr := [⟨0x3870e1c3870e1c3a757afbfb0000000000000000000000003ff6fce1e7c0000000000000, 0x7001c387001c020214000000000000000000, 0⟩, ⟨0x2040810204081010a00000010638d00000000000007f01ffff6fc00000031e70f000000, 0x4001027001c3874e8000000112005000000, 0⟩, ⟨0x3060c183060c1838017aa0000890000e5000000003f8001fc07000e1e00031e0001cf000, 0x600180a6000530000000a00020c000005000, 0⟩, ⟨0x2040810204081023015009401803000a00507f01fc000000004600e007c03007001c01f0, 0x3400d2040010200000400540000100080150, 0⟩, ⟨0x183060c183060c106028c2980080028460a20001fc07f0000020c0c1870001040f18c1c0, 0x30011184400c18000080020000040a100080, 0⟩, ⟨0xa142850a14285005800523200408e00288aff0003f800000000b021e4c000830c04f130, 0x6000530140050a000021408000020004a020, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub4 : search L4 Y4 7 ws4 0 0 0 0 = false := by decide +kernel

def L5 : ℕ := 0x4e9c027009d3a75f3f2678c7f6eb30253233
def Y5 : ℕ := 0x7ffe03f80fffffdf3f2678c7f6eb30253233
def ws5 : List Wr := [⟨0x204081020408102a15523963000000000000000000000fe03fdf3f2678c7000000000000, 0x4080020001d0070b15020801000000000000, 0⟩, ⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc1800600190a15428000000522000000000, 0⟩, ⟨0x2142850a142850a801d320002910005a9000000003f8001fc05003266000f6e000253000, 0x428400600843210000002000a4c000001000, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05507f0000000000004e032018c0f00b00240230, 0x49402500952a50000000040000100000010, 0⟩, ⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xa8800500882850002041006000010000001, 0⟩, ⟨0x2040810204081001800102200408c000808fffe03f800000000302060c4008b30253233, 0x4a9402500081020000204080000a20252222, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub5 : search L5 Y5 7 ws5 0 0 0 0 = false := by decide +kernel

def L6 : ℕ := 0x1ac06bd7af5ff4fde1b1bff74c3d80cc0
def Y6 : ℕ := 0x1fc07ffffffff4fde1b1bff74c3d80cc0
def ws6 : List Wr := [⟨0x3060c183060c183a257aa9c9000000000000000000000fe03fff4fde1b1b000000000000, 0x180060178058b050a0809000000000000, 0⟩, ⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x20063118f1f4480000005b2041000000, 0⟩, ⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x18c063c62318000000000a44000000000, 0⟩, ⟨0x254a952a54a952a701d00d40780f005a05500001fc000000004e03c01b00f01400d80cc0, 0x8404a952a50000400100000000480440, 0⟩, ⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0x2c00bc02c58002141012000000000000, 0⟩, ⟨0x10a142850a142850202c808c048020a542240001fc07f000002040d803180914c3d80cc0, 0x12804a428508000800200001482900880, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sub6 : search L6 Y6 6 ws6 0 0 0 0 = false := by decide +kernel

def signal0 : Wr := ⟨0x3ffffc000000000000000000, 0x3ffffc000000000000000000, 3⟩
def signal1 : Wr := ⟨0x3870e1c3870e1c3a757afbfb000000000000000000000fe03fffffffffff000000000000, 0x70e1c38701fc078b150a0809000000000000, 1⟩
def signal2 : Wr := ⟨0x60c183060c183058a000000526fdd00000000000007f01ffffffc000000ffffff000000, 0xc183067319cf9f4e80000005b2045000000, 2⟩
def signal3 : Wr := ⟨0x31e3c78f1e3c78f801ffa0002d90007fd000000003f8001fc07003ffe000ffe000fff000, 0x63c78ce63c6731800000a000a4c000005000, 4⟩
def signal4 : Wr := ⟨0x254a952a54a952a701d00d40780f005a05507f01fc000000004e03e01fc0f01f00fc0ff0, 0x3594d654a952a50000400540000100480550, 8⟩
def signal5 : Wr := ⟨0x58b162c58b162c480850404e70c7071870500fe00000fe00009031e183fce18f0e30e0f, 0xbe82c58be82c58002141036000010000005, 16⟩
def signal6 : Wr := ⟨0x18b162c58b162c50602cc29c048022a562a60001fc07f0000020c0d987380914cfdacdcc, 0x3163398ce62c58800080020000148a900880, 32⟩
def signal7 : Wr := ⟨0xa142850a14285005800523200408e00288afffe03f800000000b021e4e4008b3c27f33f, 0x6bd6535942850a0000214080000a2027a22a, 64⟩
def signal8 : Wr := ⟨0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000, 0x3060fe0307f0180010a0000a4c000005000, 4⟩
def signal9 : Wr := ⟨0xfe00009031e183f000000000000, 0xfe00009031e183f000000000000, 17⟩
def signal10 : Wr := ⟨0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f, 0xbe82c58b162c589010a0809000010000005, 16⟩
def signal11 : Wr := ⟨0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc, 0x103f80fe02040800008000800148a900880, 32⟩
def signal12 : Wr := ⟨0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f, 0x7bf613d84081020010000000000a2027a22a, 64⟩
def signal13 : Wr := ⟨0x1fc07000000000ffe000000000, 0x1fc07000000000ffe000000000, 6⟩
def signal14 : Wr := ⟨0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000, 0x6fdfbc810de40804e800a000000045005000, 0⟩
def signal15 : Wr := ⟨0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000, 0xc18306731833984e8000000a4c045000000, 2⟩
def signal16 : Wr := ⟨0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000, 0x810204081020400000000004a0050000000, 18⟩
def signal17 : Wr := ⟨0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f, 0xfe03c7f0e1c3874ea141036112005000005, 0⟩
def signal18 : Wr := ⟨0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f, 0x3f80c183f80c180021410364a0040000005, 16⟩
def signal19 : Wr := ⟨0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000, 0xc183060c19cf9d42800000052348a000000, 2⟩
def signal20 : Wr := ⟨0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000, 0x408102040810200a0000000000a24000000, 66⟩
def signal21 : Wr := ⟨0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f, 0x63c6731e3398f1f4482140805b204127a22a, 0⟩
def signal22 : Wr := ⟨0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000, 0x8102047711dfbf4480000005b2a61000000, 2⟩
def signal23 : Wr := ⟨0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000, 0x3060c183060c18002140000840000000000, 20⟩
def signal24 : Wr := ⟨0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f, 0x6b29aca6b28535800000b03620c010005005, 0⟩
def signal25 : Wr := ⟨0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f, 0x8ee20408ee2040000001036840010000005, 16⟩
def signal26 : Wr := ⟨0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000, 0x63c78f1e3c67318000214000a4400027a000, 4⟩
def signal27 : Wr := ⟨0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00, 0xa142850a142850002001000000000400400, 24⟩
def signal28 : Wr := ⟨0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff, 0x3468d25cb692e58000540576000110080155, 0⟩
def signal29 : Wr := ⟨0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc, 0x4f613d84f7efd800000004000018a000010, 0⟩
def signal30 : Wr := ⟨0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c, 0x10204081020408000100030001080800804, 48⟩
def signal31 : Wr := ⟨0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf, 0x3b8911dc488edd800284120600041a100081, 0⟩
def signal32 : Wr := ⟨0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203, 0xaea2850aea2850002041006001090800801, 16⟩
def signal33 : Wr := ⟨0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f, 0x60c07f01fc07cf800235509200020004a020, 0⟩
def signal34 : Wr := ⟨0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00, 0xb162c58be82c5800214101200082023020a, 16⟩

def kv0 : List Wr := [signal0, signal1, signal2, signal3, signal4, signal5, signal6, signal7]
def kv1 : List Wr := [signal8, signal1, signal3, signal2, signal4, signal5, signal6, signal7]
def kv2 : List Wr := [signal9, signal1, signal5, signal4, signal3, signal2, signal6, signal7]
def kv3 : List Wr := [signal10, signal1, signal5, signal4, signal3, signal2, signal6, signal7]
def kv4 : List Wr := [signal11, signal1, signal6, signal5, signal4, signal3, signal2, signal7]
def kv5 : List Wr := [signal12, signal1, signal7, signal6, signal5, signal4, signal3, signal2]
def kv6 : List Wr := [signal13, signal2, signal3, signal1, signal4, signal5, signal6, signal7]
def kv7 : List Wr := [signal14, signal2, signal3, signal1, signal4, signal5, signal6, signal7]
def kv8 : List Wr := [signal15, signal2, signal3, signal1, signal4, signal5, signal6, signal7]
def kv9 : List Wr := [signal16, signal2, signal5, signal4, signal3, signal1, signal6, signal7]
def kv10 : List Wr := [signal17, signal2, signal5, signal4, signal3, signal1, signal6, signal7]
def kv11 : List Wr := [signal18, signal2, signal5, signal4, signal3, signal1, signal6, signal7]
def kv12 : List Wr := [signal19, signal2, signal6, signal5, signal4, signal3, signal1, signal7]
def kv13 : List Wr := [signal20, signal2, signal7, signal6, signal5, signal4, signal3, signal1]
def kv14 : List Wr := [signal21, signal2, signal7, signal6, signal5, signal4, signal3, signal1]
def kv15 : List Wr := [signal22, signal2, signal7, signal6, signal5, signal4, signal3, signal1]
def kv16 : List Wr := [signal23, signal3, signal5, signal4, signal2, signal1, signal6, signal7]
def kv17 : List Wr := [signal24, signal3, signal5, signal4, signal2, signal1, signal6, signal7]
def kv18 : List Wr := [signal25, signal3, signal5, signal4, signal2, signal1, signal6, signal7]
def kv19 : List Wr := [signal26, signal3, signal7, signal6, signal5, signal4, signal2, signal1]
def kv20 : List Wr := [signal27, signal4, signal5, signal3, signal2, signal1, signal6, signal7]
def kv21 : List Wr := [signal28, signal4, signal5, signal3, signal2, signal1, signal6, signal7]
def kv22 : List Wr := [signal29, signal4, signal6, signal5, signal3, signal2, signal1, signal7]
def kv23 : List Wr := [signal30, signal5, signal6, signal4, signal3, signal2, signal1, signal7]
def kv24 : List Wr := [signal31, signal5, signal6, signal4, signal3, signal2, signal1, signal7]
def kv25 : List Wr := [signal32, signal5, signal6, signal4, signal3, signal2, signal1, signal7]
def kv26 : List Wr := [signal33, signal5, signal7, signal6, signal4, signal3, signal2, signal1]
def kv27 : List Wr := [signal34, signal5, signal7, signal6, signal4, signal3, signal2, signal1]

def kids : List Kid := [
  ⟨kv0, 127, 126, 64, 0x3ffffc000000000000000000⟩,
  ⟨kv1, 127, 122, 66, 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000⟩,
  ⟨kv2, 127, 110, 66, 0xfe00009031e183f000000000000⟩,
  ⟨kv3, 127, 110, 66, 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f⟩,
  ⟨kv4, 127, 94, 66, 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc⟩,
  ⟨kv5, 127, 126, 2, 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f⟩,
  ⟨kv6, 127, 123, 64, 0x1fc07000000000ffe000000000⟩,
  ⟨kv7, 127, 123, 64, 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000⟩,
  ⟨kv8, 127, 123, 64, 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000⟩,
  ⟨kv9, 127, 111, 64, 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000⟩,
  ⟨kv10, 127, 111, 64, 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f⟩,
  ⟨kv11, 127, 111, 64, 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f⟩,
  ⟨kv12, 127, 95, 64, 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000⟩,
  ⟨kv13, 127, 127, 0, 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000⟩,
  ⟨kv14, 127, 127, 0, 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f⟩,
  ⟨kv15, 127, 127, 0, 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000⟩,
  ⟨kv16, 127, 107, 66, 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000⟩,
  ⟨kv17, 127, 107, 66, 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f⟩,
  ⟨kv18, 127, 107, 66, 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f⟩,
  ⟨kv19, 127, 123, 2, 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000⟩,
  ⟨kv20, 127, 103, 66, 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00⟩,
  ⟨kv21, 127, 103, 66, 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff⟩,
  ⟨kv22, 127, 87, 66, 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc⟩,
  ⟨kv23, 127, 79, 66, 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c⟩,
  ⟨kv24, 127, 79, 66, 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf⟩,
  ⟨kv25, 127, 79, 66, 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203⟩,
  ⟨kv26, 127, 111, 2, 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f⟩,
  ⟨kv27, 127, 111, 2, 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00⟩]

abbrev slice5 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (((pairsA [] kv5).drop (6 * index)).take 6) = false

abbrev slice7 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (((pairsA [] kv7).drop (1 * index)).take 1) = false

abbrev slice8 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (((pairsA [] kv8).drop (5 * index)).take 5) = false

abbrev slice10 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (((pairsA [] kv10).drop (1 * index)).take 1) = false

abbrev slice12 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (((pairsA [] kv12).drop (5 * index)).take 5) = false

abbrev slice13 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (((pairsA [] kv13).drop (1 * index)).take 1) = false

abbrev slice14 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (((pairsA [] kv14).drop (1 * index)).take 1) = false

abbrev slice15 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (((pairsA [] kv15).drop (1 * index)).take 1) = false

abbrev slice17 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (((pairsA [] kv17).drop (1 * index)).take 1) = false

abbrev slice21 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (((pairsA [] kv21).drop (1 * index)).take 1) = false

abbrev slice22 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (((pairsA [] kv22).drop (1 * index)).take 1) = false

abbrev slice24 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (((pairsA [] kv24).drop (1 * index)).take 1) = false

abbrev slice26 (index : ℕ) : Prop :=
  anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (((pairsA [] kv26).drop (1 * index)).take 1) = false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootSearch : anyP (tryP LO (rootNext allowed kids) 9 (lenL root) 127 127 66 0) (pairsA [] root) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid0 : search LO LO 9 kv0 127 126 64 0x3ffffc000000000000000000 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid1 : search LO LO 9 kv1 127 122 66 0x183060c183060c0008500002d90007fd000000003f8001fc00000000000ffe000fff000 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid2 : search LO LO 9 kv2 127 110 66 0xfe00009031e183f000000000000 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid3 : search LO LO 9 kv3 127 110 66 0x58b162c58b162c480850404e70c7071870500fe00000000000000000000ce18f0e30e0f = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid4 : search LO LO 9 kv4 127 94 66 0x8102040810204000040004048022a562a60001fc07f0000000000000000914cfdacdcc = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5group0 : slice5 0 ∧ slice5 1 ∧ slice5 2 ∧ slice5 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid5group4 : slice5 4 :=
  by decide +kernel

theorem kid5 : search LO LO 9 kv5 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f = false := by
  have h1 : isT LO kv5 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv5) 127 126 2 0x2040810204081000800000000408e00288afffe03f80000000000000000008b3c27f33f) (pairsA [] kv5) = false := by
    refine anyP_chunks _ 6 5 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid5group0.1
    · exact kid5group0.2.1
    · exact kid5group0.2.2.1
    · exact kid5group0.2.2.2
    · exact kid5group4
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid6 : search LO LO 9 kv6 127 123 64 0x1fc07000000000ffe000000000 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7group0 : slice7 0 ∧ slice7 1 ∧ slice7 2 ∧ slice7 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7group4 : slice7 4 ∧ slice7 5 ∧ slice7 6 ∧ slice7 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7group8 : slice7 8 ∧ slice7 9 ∧ slice7 10 ∧ slice7 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7group12 : slice7 12 ∧ slice7 13 ∧ slice7 14 ∧ slice7 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7group16 : slice7 16 ∧ slice7 17 ∧ slice7 18 ∧ slice7 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7group20 : slice7 20 ∧ slice7 21 ∧ slice7 22 ∧ slice7 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid7group24 : slice7 24 ∧ slice7 25 ∧ slice7 26 ∧ slice7 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid7 : search LO LO 9 kv7 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000 = false := by
  have h1 : isT LO kv7 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv7) 127 123 64 0x37efdfbf7efdfbfd8bffa0007fffdd7fd000000003fff01fffffffffe000fffffffff000) (pairsA [] kv7) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid7group0.1
    · exact kid7group0.2.1
    · exact kid7group0.2.2.1
    · exact kid7group0.2.2.2
    · exact kid7group4.1
    · exact kid7group4.2.1
    · exact kid7group4.2.2.1
    · exact kid7group4.2.2.2
    · exact kid7group8.1
    · exact kid7group8.2.1
    · exact kid7group8.2.2.1
    · exact kid7group8.2.2.2
    · exact kid7group12.1
    · exact kid7group12.2.1
    · exact kid7group12.2.2.1
    · exact kid7group12.2.2.2
    · exact kid7group16.1
    · exact kid7group16.2.1
    · exact kid7group16.2.2.1
    · exact kid7group16.2.2.2
    · exact kid7group20.1
    · exact kid7group20.2.1
    · exact kid7group20.2.2.1
    · exact kid7group20.2.2.2
    · exact kid7group24.1
    · exact kid7group24.2.1
    · exact kid7group24.2.2.1
    · exact kid7group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8group0 : slice8 0 ∧ slice8 1 ∧ slice8 2 ∧ slice8 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid8group4 : slice8 4 ∧ slice8 5 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem kid8 : search LO LO 9 kv8 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000 = false := by
  have h1 : isT LO kv8 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv8) 127 123 64 0x60c183060c183058a000000526fdd00000000000007f0003f8ffc000000001fff000000) (pairsA [] kv8) = false := by
    refine anyP_chunks _ 5 6 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid8group0.1
    · exact kid8group0.2.1
    · exact kid8group0.2.2.1
    · exact kid8group0.2.2.2
    · exact kid8group4.1
    · exact kid8group4.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid9 : search LO LO 9 kv9 127 111 64 0x40810204081020480000000420c50000000000000000000000900000000ce18f0000000 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10group0 : slice10 0 ∧ slice10 1 ∧ slice10 2 ∧ slice10 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10group4 : slice10 4 ∧ slice10 5 ∧ slice10 6 ∧ slice10 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10group8 : slice10 8 ∧ slice10 9 ∧ slice10 10 ∧ slice10 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10group12 : slice10 12 ∧ slice10 13 ∧ slice10 14 ∧ slice10 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10group16 : slice10 16 ∧ slice10 17 ∧ slice10 18 ∧ slice10 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10group20 : slice10 20 ∧ slice10 21 ∧ slice10 22 ∧ slice10 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid10group24 : slice10 24 ∧ slice10 25 ∧ slice10 26 ∧ slice10 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid10 : search LO LO 9 kv10 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f = false := by
  have h1 : isT LO kv10 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv10) 127 111 64 0x78f1e3c78f1e3c58a850404f76ffd71870500fe0007ffffffffff1e183fffffffe30e0f) (pairsA [] kv10) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid10group0.1
    · exact kid10group0.2.1
    · exact kid10group0.2.2.1
    · exact kid10group0.2.2.2
    · exact kid10group4.1
    · exact kid10group4.2.1
    · exact kid10group4.2.2.1
    · exact kid10group4.2.2.2
    · exact kid10group8.1
    · exact kid10group8.2.1
    · exact kid10group8.2.2.1
    · exact kid10group8.2.2.2
    · exact kid10group12.1
    · exact kid10group12.2.1
    · exact kid10group12.2.2.1
    · exact kid10group12.2.2.2
    · exact kid10group16.1
    · exact kid10group16.2.1
    · exact kid10group16.2.2.1
    · exact kid10group16.2.2.2
    · exact kid10group20.1
    · exact kid10group20.2.1
    · exact kid10group20.2.2.1
    · exact kid10group20.2.2.2
    · exact kid10group24.1
    · exact kid10group24.2.1
    · exact kid10group24.2.2.1
    · exact kid10group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid11 : search LO LO 9 kv11 127 111 64 0x183060c183060c000850404a5002071870500fe00000fe00000031e183f000000e30e0f = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12group0 : slice12 0 ∧ slice12 1 ∧ slice12 2 ∧ slice12 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid12group4 : slice12 4 ∧ slice12 5 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem kid12 : search LO LO 9 kv12 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000 = false := by
  have h1 : isT LO kv12 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv12) 127 95 64 0x60c183060c183058a000000526fdd00000000000000001fffdf3c000000f6eb30000000) (pairsA [] kv12) = false := by
    refine anyP_chunks _ 5 6 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid12group0.1
    · exact kid12group0.2.1
    · exact kid12group0.2.2.1
    · exact kid12group0.2.2.2
    · exact kid12group4.1
    · exact kid12group4.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13group0 : slice13 0 ∧ slice13 1 ∧ slice13 2 ∧ slice13 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13group4 : slice13 4 ∧ slice13 5 ∧ slice13 6 ∧ slice13 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13group8 : slice13 8 ∧ slice13 9 ∧ slice13 10 ∧ slice13 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13group12 : slice13 12 ∧ slice13 13 ∧ slice13 14 ∧ slice13 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13group16 : slice13 16 ∧ slice13 17 ∧ slice13 18 ∧ slice13 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13group20 : slice13 20 ∧ slice13 21 ∧ slice13 22 ∧ slice13 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid13group24 : slice13 24 ∧ slice13 25 ∧ slice13 26 ∧ slice13 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid13 : search LO LO 9 kv13 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000 = false := by
  have h1 : isT LO kv13 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv13) 127 127 0 0x2040810204081000800000000408c0000000000000000000000b0000000008b3c000000) (pairsA [] kv13) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid13group0.1
    · exact kid13group0.2.1
    · exact kid13group0.2.2.1
    · exact kid13group0.2.2.2
    · exact kid13group4.1
    · exact kid13group4.2.1
    · exact kid13group4.2.2.1
    · exact kid13group4.2.2.2
    · exact kid13group8.1
    · exact kid13group8.2.1
    · exact kid13group8.2.2.1
    · exact kid13group8.2.2.2
    · exact kid13group12.1
    · exact kid13group12.2.1
    · exact kid13group12.2.2.1
    · exact kid13group12.2.2.2
    · exact kid13group16.1
    · exact kid13group16.2.1
    · exact kid13group16.2.2.1
    · exact kid13group16.2.2.2
    · exact kid13group20.1
    · exact kid13group20.2.1
    · exact kid13group20.2.2.1
    · exact kid13group20.2.2.2
    · exact kid13group24.1
    · exact kid13group24.2.1
    · exact kid13group24.2.2.1
    · exact kid13group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14group0 : slice14 0 ∧ slice14 1 ∧ slice14 2 ∧ slice14 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14group4 : slice14 4 ∧ slice14 5 ∧ slice14 6 ∧ slice14 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14group8 : slice14 8 ∧ slice14 9 ∧ slice14 10 ∧ slice14 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14group12 : slice14 12 ∧ slice14 13 ∧ slice14 14 ∧ slice14 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14group16 : slice14 16 ∧ slice14 17 ∧ slice14 18 ∧ slice14 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14group20 : slice14 20 ∧ slice14 21 ∧ slice14 22 ∧ slice14 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid14group24 : slice14 24 ∧ slice14 25 ∧ slice14 26 ∧ slice14 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid14 : search LO LO 9 kv14 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f = false := by
  have h1 : isT LO kv14 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv14) 127 127 0 0xe1c3870e1c38705da005232526fdf00288afffe03fff01ffffffc21e4e4ffffff27f33f) (pairsA [] kv14) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid14group0.1
    · exact kid14group0.2.1
    · exact kid14group0.2.2.1
    · exact kid14group0.2.2.2
    · exact kid14group4.1
    · exact kid14group4.2.1
    · exact kid14group4.2.2.1
    · exact kid14group4.2.2.2
    · exact kid14group8.1
    · exact kid14group8.2.1
    · exact kid14group8.2.2.1
    · exact kid14group8.2.2.2
    · exact kid14group12.1
    · exact kid14group12.2.1
    · exact kid14group12.2.2.1
    · exact kid14group12.2.2.2
    · exact kid14group16.1
    · exact kid14group16.2.1
    · exact kid14group16.2.2.1
    · exact kid14group16.2.2.2
    · exact kid14group20.1
    · exact kid14group20.2.1
    · exact kid14group20.2.2.1
    · exact kid14group20.2.2.2
    · exact kid14group24.1
    · exact kid14group24.2.1
    · exact kid14group24.2.2.1
    · exact kid14group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15group0 : slice15 0 ∧ slice15 1 ∧ slice15 2 ∧ slice15 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15group4 : slice15 4 ∧ slice15 5 ∧ slice15 6 ∧ slice15 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15group8 : slice15 8 ∧ slice15 9 ∧ slice15 10 ∧ slice15 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15group12 : slice15 12 ∧ slice15 13 ∧ slice15 14 ∧ slice15 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15group16 : slice15 16 ∧ slice15 17 ∧ slice15 18 ∧ slice15 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15group20 : slice15 20 ∧ slice15 21 ∧ slice15 22 ∧ slice15 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid15group24 : slice15 24 ∧ slice15 25 ∧ slice15 26 ∧ slice15 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid15 : search LO LO 9 kv15 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000 = false := by
  have h1 : isT LO kv15 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv15) 127 127 0 0x40810204081020582000000522f5100000000000007f01fffff4c000000ff74c3000000) (pairsA [] kv15) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid15group0.1
    · exact kid15group0.2.1
    · exact kid15group0.2.2.1
    · exact kid15group0.2.2.2
    · exact kid15group4.1
    · exact kid15group4.2.1
    · exact kid15group4.2.2.1
    · exact kid15group4.2.2.2
    · exact kid15group8.1
    · exact kid15group8.2.1
    · exact kid15group8.2.2.1
    · exact kid15group8.2.2.2
    · exact kid15group12.1
    · exact kid15group12.2.1
    · exact kid15group12.2.2.1
    · exact kid15group12.2.2.2
    · exact kid15group16.1
    · exact kid15group16.2.1
    · exact kid15group16.2.2.1
    · exact kid15group16.2.2.2
    · exact kid15group20.1
    · exact kid15group20.2.1
    · exact kid15group20.2.2.1
    · exact kid15group20.2.2.2
    · exact kid15group24.1
    · exact kid15group24.2.1
    · exact kid15group24.2.2.1
    · exact kid15group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid16 : search LO LO 9 kv16 127 107 66 0x183060c183060c0008500002500007180000000000000000000031e0000ce0000e30000 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17group0 : slice17 0 ∧ slice17 1 ∧ slice17 2 ∧ slice17 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17group4 : slice17 4 ∧ slice17 5 ∧ slice17 6 ∧ slice17 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17group8 : slice17 8 ∧ slice17 9 ∧ slice17 10 ∧ slice17 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17group12 : slice17 12 ∧ slice17 13 ∧ slice17 14 ∧ slice17 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17group16 : slice17 16 ∧ slice17 17 ∧ slice17 18 ∧ slice17 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17group20 : slice17 20 ∧ slice17 21 ∧ slice17 22 ∧ slice17 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid17group24 : slice17 24 ∧ slice17 25 ∧ slice17 26 ∧ slice17 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid17 : search LO LO 9 kv17 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f = false := by
  have h1 : isT LO kv17 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv17) 127 107 66 0x35ebd7af5ebd7afc81ffa404ef9c707fd70500fe03f80fffc07903fff83ffff8f0fffe0f) (pairsA [] kv17) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid17group0.1
    · exact kid17group0.2.1
    · exact kid17group0.2.2.1
    · exact kid17group0.2.2.2
    · exact kid17group4.1
    · exact kid17group4.2.1
    · exact kid17group4.2.2.1
    · exact kid17group4.2.2.2
    · exact kid17group8.1
    · exact kid17group8.2.1
    · exact kid17group8.2.2.1
    · exact kid17group8.2.2.2
    · exact kid17group12.1
    · exact kid17group12.2.1
    · exact kid17group12.2.2.1
    · exact kid17group12.2.2.2
    · exact kid17group16.1
    · exact kid17group16.2.1
    · exact kid17group16.2.2.1
    · exact kid17group16.2.2.2
    · exact kid17group20.1
    · exact kid17group20.2.1
    · exact kid17group20.2.2.1
    · exact kid17group20.2.2.2
    · exact kid17group24.1
    · exact kid17group24.2.1
    · exact kid17group24.2.2.1
    · exact kid17group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid18 : search LO LO 9 kv18 127 107 66 0x40810204081020480000404c20c7000070500fe00000fe000090000183f0018f0000e0f = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid19 : search LO LO 9 kv19 127 123 2 0x31e3c78f1e3c78f801ffa0002d90007fd00000000000001fc07003de0000ff6000d80000 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid20 : search LO LO 9 kv20 127 103 66 0x50a142850a1428400800400600c00500500000000000000000803001800c01800e00e00 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21group0 : slice21 0 ∧ slice21 1 ∧ slice21 2 ∧ slice21 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21group4 : slice21 4 ∧ slice21 5 ∧ slice21 6 ∧ slice21 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21group8 : slice21 8 ∧ slice21 9 ∧ slice21 10 ∧ slice21 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21group12 : slice21 12 ∧ slice21 13 ∧ slice21 14 ∧ slice21 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21group16 : slice21 16 ∧ slice21 17 ∧ slice21 18 ∧ slice21 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21group20 : slice21 20 ∧ slice21 21 ∧ slice21 22 ∧ slice21 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid21group24 : slice21 24 ∧ slice21 25 ∧ slice21 26 ∧ slice21 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid21 : search LO LO 9 kv21 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff = false := by
  have h1 : isT LO kv21 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv21) 127 103 66 0x25cb972e5cb972e781d50d44ff0f707b87557ffffc000fe0004f03fe1ffffe1ff0ff0fff) (pairsA [] kv21) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid21group0.1
    · exact kid21group0.2.1
    · exact kid21group0.2.2.1
    · exact kid21group0.2.2.2
    · exact kid21group4.1
    · exact kid21group4.2.1
    · exact kid21group4.2.2.1
    · exact kid21group4.2.2.2
    · exact kid21group8.1
    · exact kid21group8.2.1
    · exact kid21group8.2.2.1
    · exact kid21group8.2.2.2
    · exact kid21group12.1
    · exact kid21group12.2.1
    · exact kid21group12.2.2.1
    · exact kid21group12.2.2.2
    · exact kid21group16.1
    · exact kid21group16.2.1
    · exact kid21group16.2.2.1
    · exact kid21group16.2.2.2
    · exact kid21group20.1
    · exact kid21group20.2.1
    · exact kid21group20.2.2.1
    · exact kid21group20.2.2.2
    · exact kid21group24.1
    · exact kid21group24.2.1
    · exact kid21group24.2.2.1
    · exact kid21group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22group0 : slice22 0 ∧ slice22 1 ∧ slice22 2 ∧ slice22 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22group4 : slice22 4 ∧ slice22 5 ∧ slice22 6 ∧ slice22 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22group8 : slice22 8 ∧ slice22 9 ∧ slice22 10 ∧ slice22 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22group12 : slice22 12 ∧ slice22 13 ∧ slice22 14 ∧ slice22 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22group16 : slice22 16 ∧ slice22 17 ∧ slice22 18 ∧ slice22 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22group20 : slice22 20 ∧ slice22 21 ∧ slice22 22 ∧ slice22 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid22group24 : slice22 24 ∧ slice22 25 ∧ slice22 26 ∧ slice22 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid22 : search LO LO 9 kv22 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc = false := by
  have h1 : isT LO kv22 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv22) 127 87 66 0x3dfbf7efdfbf7ef761fccfdc7c8f22ff67f67f01fc07f000006ec3f99ff8f91fcffecffc) (pairsA [] kv22) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid22group0.1
    · exact kid22group0.2.1
    · exact kid22group0.2.2.1
    · exact kid22group0.2.2.2
    · exact kid22group4.1
    · exact kid22group4.2.1
    · exact kid22group4.2.2.1
    · exact kid22group4.2.2.2
    · exact kid22group8.1
    · exact kid22group8.2.1
    · exact kid22group8.2.2.1
    · exact kid22group8.2.2.2
    · exact kid22group12.1
    · exact kid22group12.2.1
    · exact kid22group12.2.2.1
    · exact kid22group12.2.2.2
    · exact kid22group16.1
    · exact kid22group16.2.1
    · exact kid22group16.2.2.1
    · exact kid22group16.2.2.2
    · exact kid22group20.1
    · exact kid22group20.2.1
    · exact kid22group20.2.2.1
    · exact kid22group20.2.2.2
    · exact kid22group24.1
    · exact kid22group24.2.1
    · exact kid22group24.2.2.1
    · exact kid22group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid23 : search LO LO 9 kv23 127 79 66 0x81020408102040000400040400202102040000000000000000001800380810c0c20c0c = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24group0 : slice24 0 ∧ slice24 1 ∧ slice24 2 ∧ slice24 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24group4 : slice24 4 ∧ slice24 5 ∧ slice24 6 ∧ slice24 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24group8 : slice24 8 ∧ slice24 9 ∧ slice24 10 ∧ slice24 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24group12 : slice24 12 ∧ slice24 13 ∧ slice24 14 ∧ slice24 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24group16 : slice24 16 ∧ slice24 17 ∧ slice24 18 ∧ slice24 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24group20 : slice24 20 ∧ slice24 21 ∧ slice24 22 ∧ slice24 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid24group24 : slice24 24 ∧ slice24 25 ∧ slice24 26 ∧ slice24 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid24 : search LO LO 9 kv24 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf = false := by
  have h1 : isT LO kv24 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv24) 127 79 66 0x1dbb76eddbb76ed4e0adc69ce78c72f5e7a700fffc07ffe00029c3df9f3fcf1cfffbcfcf) (pairsA [] kv24) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid24group0.1
    · exact kid24group0.2.1
    · exact kid24group0.2.2.1
    · exact kid24group0.2.2.2
    · exact kid24group4.1
    · exact kid24group4.2.1
    · exact kid24group4.2.2.1
    · exact kid24group4.2.2.2
    · exact kid24group8.1
    · exact kid24group8.2.1
    · exact kid24group8.2.2.1
    · exact kid24group8.2.2.2
    · exact kid24group12.1
    · exact kid24group12.2.1
    · exact kid24group12.2.2.1
    · exact kid24group12.2.2.2
    · exact kid24group16.1
    · exact kid24group16.2.1
    · exact kid24group16.2.2.1
    · exact kid24group16.2.2.2
    · exact kid24group20.1
    · exact kid24group20.2.1
    · exact kid24group20.2.2.1
    · exact kid24group20.2.2.2
    · exact kid24group24.1
    · exact kid24group24.2.1
    · exact kid24group24.2.2.1
    · exact kid24group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid25 : search LO LO 9 kv25 127 79 66 0x50a142850a1428480810400e30c5050850100fe00000fe0000903061807c60830210203 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26group0 : slice26 0 ∧ slice26 1 ∧ slice26 2 ∧ slice26 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26group4 : slice26 4 ∧ slice26 5 ∧ slice26 6 ∧ slice26 7 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26group8 : slice26 8 ∧ slice26 9 ∧ slice26 10 ∧ slice26 11 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26group12 : slice26 12 ∧ slice26 13 ∧ slice26 14 ∧ slice26 15 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26group16 : slice26 16 ∧ slice26 17 ∧ slice26 18 ∧ slice26 19 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26group20 : slice26 20 ∧ slice26 21 ∧ slice26 22 ∧ slice26 23 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid26group24 : slice26 24 ∧ slice26 25 ∧ slice26 26 ∧ slice26 27 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem kid26 : search LO LO 9 kv26 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f = false := by
  have h1 : isT LO kv26 = false := by decide +kernel
  have h2 : anyP (tryP LO (search LO LO 8) 8 (lenL kv26) 127 111 2 0xf9f3e7cf9f3e7c4d8855636e74cfe71af8ffffe03f80fe00009b33ffcffce9bfce7ff3f) (pairsA [] kv26) = false := by
    refine anyP_chunks _ 1 28 _ (by decide +kernel) fun i hi => ?_
    interval_cases i
    · exact kid26group0.1
    · exact kid26group0.2.1
    · exact kid26group0.2.2.1
    · exact kid26group0.2.2.2
    · exact kid26group4.1
    · exact kid26group4.2.1
    · exact kid26group4.2.2.1
    · exact kid26group4.2.2.2
    · exact kid26group8.1
    · exact kid26group8.2.1
    · exact kid26group8.2.2.1
    · exact kid26group8.2.2.2
    · exact kid26group12.1
    · exact kid26group12.2.1
    · exact kid26group12.2.2.1
    · exact kid26group12.2.2.2
    · exact kid26group16.1
    · exact kid26group16.2.1
    · exact kid26group16.2.2.1
    · exact kid26group16.2.2.2
    · exact kid26group20.1
    · exact kid26group20.2.1
    · exact kid26group20.2.2.1
    · exact kid26group20.2.2.2
    · exact kid26group24.1
    · exact kid26group24.2.1
    · exact kid26group24.2.2.1
    · exact kid26group24.2.2.2
  rw [search, h1, h2]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kid27 : search LO LO 9 kv27 127 111 2 0x58b162c58b162c480850404e70c70718705000000000fe00009031e181bce10c0c00c00 = false := by decide +kernel

theorem kids_false : ∀ q ∈ kids, search LO LO 9 q.v q.c1 q.c2 q.c3 q.g = false := by
  intro q hq
  simp only [kids, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kid0
  · exact kid1
  · exact kid2
  · exact kid3
  · exact kid4
  · exact kid5
  · exact kid6
  · exact kid7
  · exact kid8
  · exact kid9
  · exact kid10
  · exact kid11
  · exact kid12
  · exact kid13
  · exact kid14
  · exact kid15
  · exact kid16
  · exact kid17
  · exact kid18
  · exact kid19
  · exact kid20
  · exact kid21
  · exact kid22
  · exact kid23
  · exact kid24
  · exact kid25
  · exact kid26
  · exact kid27


-- Part 6: the theta graph needs eleven binary gates, negations free.

def okL (L y : ℕ) : Bool :=
  Nat.blt L (2 ^ 143) && (List.range 143).all fun i => !(L.testBit i) || (y.testBit i != y.testBit (143 + i))

lemma okL_spec {L y : ℕ} (h : okL L y = true) (i : ℕ) (hi : L.testBit i = true) :
    y.testBit i ≠ y.testBit (143 + i) := by
  rw [okL, Bool.and_eq_true] at h
  have hlt : i < 143 := by
    by_contra hc
    have h1 : L < 2 ^ 143 := by simpa [Nat.blt_eq] using h.1
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (not_lt.mp hc)))
    rw [this] at hi
    exact Bool.false_ne_true hi
  have h2 := List.all_eq_true.mp h.2 i (List.mem_range.mpr hlt)
  rw [hi] at h2
  simpa using h2

def W0 : Set ℕ := {x | x = 0 ∨ ∃ i : Fin 7, x = ip i}

def LB (h : ℕ) : ℕ := [8, 7, 8, 8, 8, 8, 7].getD h 0

lemma subW (h : ℕ) (ws : List Wr)
    (hc : ∀ i : Fin 7, Nat.land (ip i) (mask h) = 0 ∨ ∃ u ∈ ws, u.w = Nat.land (ip i) (mask h))
    {W : Set ℕ} (hW : ∀ x ∈ W, x = 0 ∨ ∃ i : Fin 7, x = Nat.land (ip i) (mask h)) :
    ∀ x ∈ W, x = 0 ∨ ∃ u ∈ ws, u.w = x := by
  intro x hx
  rcases hW x hx with e | ⟨i, e⟩
  · exact Or.inl e
  · rw [e]; exact hc i

theorem subBound (h : ℕ) (hh : h < 7) {W : Set ℕ} (h0 : 0 ∈ W)
    (hW : ∀ x ∈ W, x = 0 ∨ ∃ i : Fin 7, x = Nat.land (ip i) (mask h)) :
    ¬ Der opN (LB h - 1) W (Nat.land LO (mask h)) := by
  interval_cases h
  · exact refute (L := L0) (y := Y0) (ws := ws0) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub0 h0
      (subW 0 ws0 (by decide +kernel) hW)
  · exact refute (L := L1) (y := Y1) (ws := ws1) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub1 h0
      (subW 1 ws1 (by decide +kernel) hW)
  · exact refute (L := L2) (y := Y2) (ws := ws2) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub2 h0
      (subW 2 ws2 (by decide +kernel) hW)
  · exact refute (L := L3) (y := Y3) (ws := ws3) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub3 h0
      (subW 3 ws3 (by decide +kernel) hW)
  · exact refute (L := L4) (y := Y4) (ws := ws4) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub4 h0
      (subW 4 ws4 (by decide +kernel) hW)
  · exact refute (L := L5) (y := Y5) (ws := ws5) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub5 h0
      (subW 5 ws5 (by decide +kernel) hW)
  · exact refute (L := L6) (y := Y6) (ws := ws6) (okL_spec (by decide +kernel)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sub6 h0
      (subW 6 ws6 (by decide +kernel) hW)

lemma root_ip : ∀ i : Fin 7, ∃ u ∈ root, u.w = ip i := by decide +kernel

lemma ip_root : ∀ u ∈ root, ∃ i : Fin 7, u.w = ip i := by decide +kernel

lemma ip_lt : ∀ i : Fin 7, ip i < 2 ^ 286 := by decide +kernel

lemma LO_lt : LO < 2 ^ 286 := by decide +kernel

lemma Tn_inv : ∀ p : Fin 3, ∀ i : Fin 286,
    sIdx (Tn p) i.val < 286 ∧ sIdx (Tn p) (sIdx (Tn p) i.val) = i.val := by decide +kernel

lemma Tn_ip : ∀ p : Fin 3, ∀ i : Fin 7, ∀ r : Fin 286,
    (ip (pm p i)).testBit r.val = (ip i).testBit (sIdx (Tn p) r.val) := by decide +kernel

lemma Tn_LO : ∀ p : Fin 3, ∀ r : Fin 286,
    LO.testBit r.val = LO.testBit (sIdx (Tn p) r.val) := by decide +kernel

lemma pm_inv : ∀ p : Fin 3, ∀ i : Fin 7, pm p (pm p i) = i := by decide

lemma allowed_spec : ∀ t : Fin 4, ∀ i j : Fin 7, i ≠ j →
    (∀ p : Fin 3, opN t (ip i) (ip j) ≤ opN t (ip (pm p i)) (ip (pm p j))) →
    memN (opN t (ip i) (ip j)) allowed = true := by decide +kernel

lemma sg_ip (p : Fin 3) (i : Fin 7) : sg 286 (Tn p) (ip i) = ip (pm p i) :=
  sg_eq (bdd_of_lt (ip_lt _)) fun r hr => Tn_ip p i ⟨r, hr⟩

lemma sg_LO (p : Fin 3) : sg 286 (Tn p) LO = LO :=
  sg_eq (bdd_of_lt LO_lt) fun r hr => Tn_LO p ⟨r, hr⟩

lemma sg_zero (N T : ℕ) : sg N T 0 = 0 :=
  sg_eq (fun i _ => Nat.zero_testBit i) fun r _ => by rw [Nat.zero_testBit, Nat.zero_testBit]

lemma sg_W0 (p : Fin 3) : sg 286 (Tn p) '' W0 = W0 := by
  ext x
  constructor
  · rintro ⟨w, rfl | ⟨i, rfl⟩, rfl⟩
    · exact Or.inl (sg_zero _ _)
    · exact Or.inr ⟨pm p i, sg_ip p i⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, Or.inl rfl, sg_zero _ _⟩
    · exact ⟨ip (pm p i), Or.inr ⟨pm p i, rfl⟩, by rw [sg_ip, pm_inv]⟩

lemma bdd_W0 : ∀ x ∈ W0, Bdd 286 x := by
  rintro x (rfl | ⟨i, rfl⟩)
  · exact fun i _ => Nat.zero_testBit i
  · exact bdd_of_lt (ip_lt i)

theorem theta : ¬ Der opN 10 W0 LO := by
  intro h
  obtain ⟨l, hk, hV, hU, hC, hmin⟩ := exists_sorted h
  have h0 : (0 : ℕ) ∈ W0 := Or.inl rfl
  have hLO : LO ≠ 0 := by decide +kernel
  have hL : ∀ i, LO.testBit i = true → LO.testBit i ≠ LO.testBit (143 + i) :=
    fun i hi => okL_spec (L := LO) (y := LO) (by decide +kernel) i hi
  have caps : ∀ h < 7, kills (mask h) l + LB h ≤ 10 := by
    intro h hh
    obtain ⟨n, hn, hd⟩ := der_masked (m := mask h) l hV h0
    by_contra hc
    have hLB : 1 ≤ LB h := by interval_cases h <;> decide
    refine subBound h hh (W := (fun w => Nat.land w (mask h)) '' W0) ⟨0, h0, by simp [Nat.land]⟩ ?_
      (hd.le (by omega))
    rintro _ ⟨w, rfl | ⟨i, rfl⟩, rfl⟩
    · left; show Nat.land 0 (mask h) = 0; simp [Nat.land]
    · exact Or.inr ⟨i, rfl⟩
  have hy : ∀ h < 7, Nat.land LO (mask h) ≠ 0 := by
    intro h hh
    have key : ∀ h : Fin 7, Nat.land LO (mask h.val) ≠ 0 := by decide +kernel
    exact key ⟨h, hh⟩
  have hfl : ∀ u ∈ root, ∀ h, u.f.testBit h = true → h < 7 ∧ Nat.land u.w (mask h) = 0 := by
    have k1 : ∀ u ∈ root, u.f < 2 ^ 7 := by decide +kernel
    have k2 : ∀ u ∈ root, ∀ h : Fin 7, u.f.testBit h.val = true → Nat.land u.w (mask h.val) = 0 := by
      decide +kernel
    intro u hu h hb
    have hlt : h < 7 := by
      by_contra hc
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (k1 u hu)
        (Nat.pow_le_pow_right (by omega) (not_lt.mp hc)))
      rw [this] at hb
      exact Bool.false_ne_true hb
    exact ⟨hlt, k2 u hu ⟨h, hlt⟩ hb⟩
  have hrep : Rep LO 7 mask root (need LO l) := by
    refine root_rep hL hLO (by decide +kernel) (by decide +kernel) hfl (by decide +kernel) hV h0 ?_
    rintro x (rfl | ⟨i, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (root_ip i)
  have hbud : Bud 7 mask 127 127 66 l := by
    intro h hh
    have c := caps h hh
    interval_cases h <;> simp only [LB, List.getD_cons_zero, List.getD_cons_succ] at c <;>
      refine ⟨by omega, fun _ => by decide, fun _ => by decide, fun h3 => ?_⟩ <;>
      first | (exfalso; omega) | decide
  cases l with
  | nil =>
    have e : ∀ i : Fin 7, LO ≠ ip i := by decide +kernel
    rcases hV with h | ⟨i, h⟩
    · exact hLO h
    · exact e i h
  | cons s l =>
    have al : memN s.val allowed = true := by
      obtain ⟨fa, fb, fab, _⟩ := step_facts hV h0
      rcases hV.1 with e | ⟨i, ei⟩
      · exact absurd e fa
      rcases hV.2.1 with e | ⟨j, ej⟩
      · exact absurd e fb
      have hs : s.val = opN s.t (ip i) (ip j) := by rw [St.val, ei, ej]
      rw [hs]
      refine allowed_spec s.t i j (fun e => fab (by rw [ei, ej, e])) fun p => ?_
      have vm := valid_map (Tn p) (fun i hi => Tn_inv p ⟨i, hi⟩) (s :: l) bdd_W0 hV
      rw [sg_LO, sg_W0] at vm
      have := hmin _ vm (by simp)
      change s.val ≤ (mapSt 286 (Tn p) s).val at this
      rw [mapSt_val, hs, sg_op, sg_ip, sg_ip] at this
      exact this
    have := level (k := 9) (r := rootNext allowed kids) hy hL hV h0 hU (by simpa using hk) hC hrep hbud ?_
    · rw [rootSearch] at this
      exact Bool.false_ne_true this
    · intro v' d1 d2 d3 hv' hb'
      show cond (memN s.val allowed) (!(isKid v' d1 d2 d3 s.val kids)) false = true
      rw [al, cond_true]
      cases hkid : isKid v' d1 d2 d3 s.val kids
      · rfl
      · have hm := kids_false _ (isKid_mem kids hkid)
        have hs := search_complete hy hL 9 l _ v' s.val d1 d2 d3 hV.2.2.2 (Or.inr h0) hU.2
          (by simp only [List.length_cons] at hk; omega) hC.2 hv' hb'
        simp only at hm
        rw [hm] at hs
        exact absurd hs Bool.false_ne_true

-- Part 7: circuits.

abbrev Om := Fin 9 → Bool

def zr : Om := fun _ => false

def nrm (F : Om → Bool) : Om → Bool := fun x => F x != F zr

def bc (gs : List Gate) : ℕ := gs.countP fun g => !(g.op.eval [false])

def nc (gs : List Gate) : ℕ := gs.countP fun g => g.op.eval [false]

def runG (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def OkG (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i = w.length
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right h]
    by_cases h1 : i < w.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · have h2 : (w ++ [b]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h2,
        List.getElem?_eq_none (by omega : w.length ≤ i)]

lemma nrm_const (c : Bool) : nrm (fun _ => c) = fun _ => false := by
  funext x; simp [nrm]

lemma nrm_not (F : Om → Bool) : nrm (fun x => !(F x)) = nrm F := by
  funext x; simp only [nrm]; cases F x <;> cases F zr <;> rfl

lemma nrm_bin (c : Bool) (F G : Om → Bool) : ∃ t : Fin 4,
    nrm (fun x => if c then (F x || G x) else (F x && G x)) = opF t (nrm F) (nrm G) := by
  cases hc : c <;> cases hF : F zr <;> cases hG : G zr
  · exact ⟨0, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨2, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨3, by funext x; simp [nrm, opF, opB, hF, hG]; cases F x <;> cases G x <;> rfl⟩
  · exact ⟨1, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨1, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨3, by funext x; simp [nrm, opF, opB, hF, hG]; cases F x <;> cases G x <;> rfl⟩
  · exact ⟨2, by funext x; simp [nrm, opF, opB, hF, hG]⟩
  · exact ⟨0, by funext x; simp [nrm, opF, opB, hF, hG]⟩

lemma circ (gs : List Gate) : ∀ (w : Om → List Bool) (m : ℕ) (U : Set (Om → Bool)),
    (∀ x, (w x).length = m) → (fun _ => false) ∈ U →
    (∀ i, nrm (fun x => (w x).getD i false) ∈ U) → (∀ g ∈ gs, OkG g) →
    ∀ o, Der opF (bc gs) U (nrm fun x => (runG gs (w x)).getD o false) := by
  induction gs with
  | nil => intro w m U _ _ hU _ o; exact Der.here (hU o)
  | cons g gs ih =>
    intro w m U hl h0 hU hg o
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    have hgs : ∀ g' ∈ gs, OkG g' := fun g' h => hg g' (by simp [h])
    let v : Om → Bool := fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
    let w' : Om → List Bool := fun x => w x ++ [v x]
    have hl' : ∀ x, (w' x).length = m + 1 := fun x => by simp [w', hl]
    have hw' (U' : Set (Om → Bool)) (hs : U ⊆ U') (hv : nrm v ∈ U') :
        ∀ i, nrm (fun x => (w' x).getD i false) ∈ U' := by
      intro i
      by_cases hi : i = m
      · have e : (fun x => (w' x).getD i false) = v := by
          funext x; simp only [w']; rw [getD_snoc, ite_eq_left (by rw [hl, hi])]
        rw [e]; exact hv
      · have e : (fun x => (w' x).getD i false) = fun x => (w x).getD i false := by
          funext x; simp only [w']; rw [getD_snoc, ite_eq_right (by rw [hl]; exact hi)]
        rw [e]; exact hs (hU i)
    have fin0 (hv : nrm v ∈ U) : Der opF (bc gs) U (nrm fun x => (runG (g :: gs) (w x)).getD o false) :=
      ih w' (m + 1) U hl' h0 (hw' U (fun _ h => h) hv) hgs o
    have bcle : bc gs ≤ bc (g :: gs) := by
      rw [bc, bc, List.countP_cons]; omega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have bin (c : Bool) (hb : bc (g :: gs) = bc gs + 1)
        (hev : ∀ l : List Bool, g.op.eval l = if c then l.any id else l.all id) :
        Der opF (bc (g :: gs)) U (nrm fun x => (runG (g :: gs) (w x)).getD o false) := by
      rcases hi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨q, r⟩⟩⟩
      · refine (fin0 ?_).le bcle
        have e : v = fun _ => !c := by
          funext x; simp only [v, hi, hev]; cases c <;> rfl
        rw [e, nrm_const]; exact h0
      · refine (fin0 ?_).le bcle
        have e : v = fun x => (w x).getD i false := by
          funext x; simp only [v, hi, hev]; cases c <;> simp
        rw [e]; exact hU i
      · obtain ⟨t, ht⟩ := nrm_bin c (fun x => (w x).getD i false) (fun x => (w x).getD j false)
        have e : v = fun x => if c then ((w x).getD i false || (w x).getD j false)
            else ((w x).getD i false && (w x).getD j false) := by
          funext x; simp only [v, hi, hev]; cases c <;> simp
        have ev : nrm v = opF t (nrm fun x => (w x).getD i false) (nrm fun x => (w x).getD j false) := by
          rw [e]; exact ht
        rw [hb]
        refine Der.step t _ _ (hU i) (hU j) ?_
        refine ih w' (m + 1) _ hl' (Or.inr h0) (hw' _ (Set.subset_insert _ _) ?_) hgs o
        rw [ev]; exact Or.inl rfl
      · rw [hi] at hlen; simp at hlen
    rcases hop with h | h | h
    · refine bin false ?_ (fun l => by rw [h]; rfl)
      rw [bc, bc, List.countP_cons, h]; rfl
    · refine bin true ?_ (fun l => by rw [h]; rfl)
      rw [bc, bc, List.countP_cons, h]; rfl
    · refine (fin0 ?_).le bcle
      rcases hi : g.inputs with _ | ⟨i, r⟩
      · have e : v = fun _ => true := by funext x; simp only [v, hi, h]; rfl
        rw [e, nrm_const]; exact h0
      · have e : v = fun x => !((w x).getD i false) := by funext x; simp only [v, hi, h]; rfl
        rw [e, nrm_not]; exact hU i

def fG : Om → Bool := fun x =>
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def pin (j : Fin 9) (F : Om → Bool) : Om → Bool := fun x => F (Function.update x j false)

def rowTab (j : Fin 9) : ℕ := [0, ip 0, ip 1, ip 2, 0, ip 3, ip 4, ip 5, ip 6].getD j.val 0

def row (r : Fin 286) : Om := fun j => (rowTab j).testBit r.val

def encF (F : Om → Bool) : ℕ := Nat.ofBits fun r : Fin 286 => F (row r)

lemma encF_bit (F : Om → Bool) (i : ℕ) (hi : i < 286) : (encF F).testBit i = F (row ⟨i, hi⟩) := by
  rw [encF, Nat.testBit_ofBits_lt _ _ hi]

lemma encF_bdd (F : Om → Bool) : Bdd 286 (encF F) := fun i hi => by
  rw [encF, Nat.testBit_ofBits_ge _ _ hi]

lemma encF_op (t : Fin 4) (F G : Om → Bool) : encF (opF t F G) = opN t (encF F) (encF G) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 286
  · rw [opN_bit, encF_bit _ _ hi, encF_bit _ _ hi, encF_bit _ _ hi]; rfl
  · rw [encF_bdd _ i (by omega), bdd_op t (encF_bdd F) (encF_bdd G) i (by omega)]

lemma encF_eq {F : Om → Bool} {x : ℕ} (hx : Bdd 286 x) (h : ∀ r : Fin 286, F (row r) = x.testBit r.val) :
    encF F = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 286
  · rw [encF_bit _ _ hi]; exact h ⟨i, hi⟩
  · rw [encF_bdd _ i (by omega), hx i (by omega)]

lemma fG_rows : ∀ r : Fin 286, pin 4 (pin 0 fG) (row r) = LO.testBit r.val := by decide +kernel

lemma opF_false_left (t : Fin 4) (F : Om → Bool) :
    opF t (fun _ => false) F = (fun _ => false) ∨ opF t (fun _ => false) F = F := by
  fin_cases t
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]

lemma opF_false_right (t : Fin 4) (F : Om → Bool) :
    opF t F (fun _ => false) = (fun _ => false) ∨ opF t F (fun _ => false) = F := by
  fin_cases t
  · left; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · right; funext x; simp [opF, opB]
  · left; funext x; simp [opF, opB]

def pt (l : List (Fin 9)) : Om := fun j => l.contains j

theorem noDer (b : Fin 9) (hb : b = 2 ∨ b = 3) :
    ¬ Der opF 12 {F : Om → Bool | F = (fun _ => false) ∨ (∃ i : Fin 9, F = fun x => x i) ∨
      F = fun x => x 0 || x b} fG := by
  intro h
  have hb0 : b ≠ 0 := by rcases hb with rfl | rfl <;> decide
  have e0 : pin 0 (fun x : Om => x 0) = fun _ => false := by funext x; simp [pin]
  have e0z : pin 0 (fun _ : Om => false) = fun _ => false := rfl
  have e0i (i : Fin 9) (hi : i ≠ 0) : pin 0 (fun x : Om => x i) = fun x => x i := by
    funext x; simp [pin, Function.update_of_ne hi]
  have e0g : pin 0 (fun x : Om => x 0 || x b) = fun x => x b := by
    funext x; simp [pin, Function.update_of_ne hb0]
  have hE := h.elim (op' := opF) (pin 0) (fun _ _ _ => rfl) (fun x => x 0)
    (fun t F => by rw [e0]; exact opF_false_left t F) (fun t F => by rw [e0]; exact opF_false_right t F)
    {F : Om → Bool | F = (fun _ => false) ∨ (∃ i : Fin 9, i ≠ 0 ∧ F = fun x => x i) ∨
      F = fun x => x 0 || x b}
    (by
      rintro F (rfl | ⟨i, rfl⟩ | rfl)
      · exact Or.inr (Or.inl rfl)
      · by_cases hi : i = 0
        · subst hi; exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr rfl)))
    (by
      intro e
      have := congrFun e (pt [0])
      revert this; decide)
    ⟨fun _ => false, Or.inl rfl, by rw [e0]; rfl⟩
  rcases hE with h | ⟨k', hk', h⟩
  · have := h.agree (pt [0, b, 5]) (pt [b, 5]) (by
      rintro F (rfl | ⟨i, hi, rfl⟩ | rfl)
      · rfl
      · revert hi; rcases hb with rfl | rfl <;> revert i <;> decide
      · rcases hb with rfl | rfl <;> decide)
    revert this; rcases hb with rfl | rfl <;> decide
  · have hk : k' = 11 := by omega
    subst hk
    have e4 : pin 4 (fun x : Om => x 4) = fun _ => false := by funext x; simp [pin]
    have e4i (i : Fin 9) (hi : i ≠ 4) : pin 4 (fun x : Om => x i) = fun x => x i := by
      funext x; simp [pin, Function.update_of_ne hi]
    have hE := h.elim (op' := opF) (pin 4) (fun _ _ _ => rfl) (fun x => x 4)
      (fun t F => by rw [e4]; exact opF_false_left t F)
      (fun t F => by rw [e4]; exact opF_false_right t F)
      {F : Om → Bool | F = (fun _ => false) ∨ ∃ i : Fin 9, i ≠ 0 ∧ i ≠ 4 ∧ F = fun x => x i}
      (by
        rintro _ ⟨F, hF, rfl⟩
        rcases hF with rfl | ⟨i, hi, rfl⟩ | rfl
        · exact Or.inr (Or.inl rfl)
        · rw [e0i i hi]
          by_cases h4 : i = 4
          · subst h4; exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨i, hi, h4, rfl⟩)
        · rw [e0g]
          exact Or.inr (Or.inr ⟨b, hb0, by rcases hb with rfl | rfl <;> decide, rfl⟩))
      (by
        intro e
        have := congrFun e (pt [4])
        revert this; decide)
      ⟨fun _ => false, Or.inl rfl, by rw [e4]; rfl⟩
    rcases hE with h | ⟨k', hk', h⟩
    · have := h.agree (pt [3, 4]) (pt [3]) (by
        rintro F (rfl | ⟨i, h1, h2, rfl⟩)
        · rfl
        · revert h1 h2; revert i; decide)
      revert this; decide
    · have hk : k' = 10 := by omega
      subst hk
      have hN := h.map (op' := opN) encF encF_op
      rw [encF_eq (bdd_of_lt LO_lt) fG_rows] at hN
      refine theta (hN.mono ?_)
      rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
      rcases hF with rfl | ⟨i, h1, h2, rfl⟩
      · left
        exact encF_eq (fun i _ => Nat.zero_testBit i) fun r => by rw [Nat.zero_testBit]; rfl
      · right
        rw [e4i i h2]
        have hr : ∀ i : Fin 9, i ≠ 0 → i ≠ 4 → ∃ j : Fin 7, rowTab i = ip j := by decide +kernel
        obtain ⟨j, hj⟩ := hr i h1 h2
        exact ⟨j, encF_eq (bdd_of_lt (ip_lt j)) fun r => by show (rowTab i).testBit _ = _; rw [hj]⟩

lemma ofFn_getD (n : ℕ) (y : Fin n → Bool) (i : ℕ) :
    (List.ofFn y).getD i false = if h : i < n then y ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dif_pos h]; simp [List.getD_eq_getElem?_getD, h]
  · rw [dif_neg h]; simp [List.getD_eq_getElem?_getD, h]

lemma two_count {α : Type} (p : α → Bool) (l : List α) (i j : ℕ) (hij : i < j) (hj : j < l.length)
    (h1 : p (l[i]'(by omega)) = true) (h2 : p l[j] = true) : 2 ≤ l.countP p := by
  rw [← List.take_append_drop j l, List.countP_append]
  have a1 : 1 ≤ (l.take j).countP p := by
    rw [Nat.succ_le_iff, List.countP_pos_iff]
    refine ⟨l[i]'(by omega), ?_, h1⟩
    rw [List.mem_take_iff_getElem]
    exact ⟨i, by omega, rfl⟩
  have a2 : 1 ≤ (l.drop j).countP p := by
    rw [Nat.succ_le_iff, List.countP_pos_iff]
    refine ⟨l[j], ?_, h2⟩
    rw [List.mem_drop_iff_getElem]
    exact ⟨0, by omega, by simp⟩
  omega

-- at most fifteen gates, first gate x0 or xb, at least two negations: impossible
theorem no15 (b : Fin 9) (hb : b = 2 ∨ b = 3) (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ 15)
    (hw : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y b))
    (hn : 2 ≤ nc C.gates) (hf : circuitFun 9 C = fG) : False := by
  obtain ⟨gates, out⟩ := C
  cases gates with
  | nil => simp [nc] at hn
  | cons g gs =>
    have hlen : gs.length ≤ 14 := by
      have : (Circuit.mk (g :: gs) out).size = gs.length + 1 := rfl
      omega
    have hg0 := hC g (by simp)
    have hfirst (x : Om) : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x b) := by
      have h := hw x
      change (runG gs (List.ofFn x ++ [_])).getD 9 false = _ at h
      have keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
          (runG gs w).getD i false = w.getD i false := by
        intro gs
        induction gs with
        | nil => intro w i _; rfl
        | cons q gs ih =>
          intro w i hi
          change (runG gs (w ++ [_])).getD i false = _
          rw [ih _ i (by simp; omega), getD_snoc, ite_eq_right (by omega)]
      rw [keep _ _ _ (by simp), getD_snoc, ite_eq_left (by simp)] at h
      exact h
    have hnot : g.op.eval [false] = false := by
      rcases hg0.1 with h | h | h
      · rw [h]; rfl
      · rw [h]; rfl
      · exfalso
        have := hfirst zr
        rw [h] at this
        have hz : ∀ i, (List.ofFn zr).getD i false = false := by
          intro i
          rw [ofFn_getD]
          split_ifs <;> rfl
        rcases hi : g.inputs with _ | ⟨i, r⟩
        · rw [hi] at this; revert this; simp [GateOp.eval, zr]
        · rw [hi] at this
          simp only [List.map_cons, hz] at this
          revert this; simp [GateOp.eval, zr]
    have hnc : nc (g :: gs) = nc gs := by
      rw [nc, nc, List.countP_cons, hnot]; rfl
    have hn' : 2 ≤ nc gs := by rw [← hnc]; exact hn
    have hsum : gs.length = nc gs + bc gs := by
      have := List.length_eq_countP_add_countP (fun g : Gate => g.op.eval [false]) (l := gs)
      rw [this, nc, bc]
      congr 1
    let U : Set (Om → Bool) := {F | F = (fun _ => false) ∨ (∃ i : Fin 9, F = fun x => x i) ∨
      F = fun x => x 0 || x b}
    have hD : Der opF (bc gs) U (nrm fun x => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) := by
      refine circ gs (fun x => List.ofFn x ++ [x 0 || x b]) 10 U (fun x => by simp) (Or.inl rfl) ?_
        (fun q hq => hC q (by simp [hq])) out
      intro i
      by_cases h9 : i = 9
      · right; right
        funext x
        simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_left h9]
        simp [zr]
      · by_cases hi : i < 9
        · right; left
          refine ⟨⟨i, hi⟩, ?_⟩
          funext x
          simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_right h9, ofFn_getD, dif_pos hi]
          simp [zr]
        · left
          funext x
          simp only [nrm, getD_snoc, List.length_ofFn, ite_eq_right h9, ofFn_getD, dif_neg hi]
          rfl
    have he : (nrm fun x => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) = fG := by
      have e : (fun x : Om => (runG gs (List.ofFn x ++ [x 0 || x b])).getD out false) = fG := by
        rw [← hf]
        funext x
        rw [← hfirst x]
        rfl
      rw [e]
      funext x
      have : fG zr = false := by decide
      simp [nrm, this]
    rw [he] at hD
    exact noDer b hb (hD.le (by omega))

lemma nc_two {gates : List Gate} (i j : Fin gates.length) (hij : i ≠ j)
    (hi : (gates.get i).op = GateOp.not) (hj : (gates.get j).op = GateOp.not) : 2 ≤ nc gates := by
  have pi : (gates[i.val]'i.isLt).op.eval [false] = true := by
    have : (gates[i.val]'i.isLt).op = GateOp.not := hi
    rw [this]; rfl
  have pj : (gates[j.val]'j.isLt).op.eval [false] = true := by
    have : (gates[j.val]'j.isLt).op = GateOp.not := hj
    rw [this]; rfl
  rcases lt_or_gt_of_ne (fun e => hij (Fin.ext e) : i.val ≠ j.val) with h | h
  · exact two_count _ gates i.val j.val h j.isLt pi pj
  · exact two_count _ gates j.val i.val h i.isLt pj pi

end Theta
end
end PEqualNP.Outside.L_meta_3024

namespace PEqualNP.Outside.L_meta_3024
section
-- Search certificate adapted from jdavies69, project pull request 5615.
namespace OneNot

-- Encode the live nonconstant signals in a suffix with separate binary and negation budgets.
abbrev Word := BitVec 512

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def top : Word := BitVec.allOnes 512
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proper (a : Word) : Prop := a ≠ 0 ∧ a ≠ top
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance (a : Word) : Decidable (proper a) := by unfold proper; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def combine (disj : Bool) (a b : Word) : Word := if disj then a ||| b else a &&& b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma laws (a : Word) :
    combine true a 0 = a ∧ combine false a 0 = 0 ∧
    combine true a top = top ∧ combine false a top = a ∧
    combine true a a = a ∧ combine false a a = a := by
  exact ⟨by simp [combine], by simp [combine], BitVec.or_allOnes, BitVec.and_allOnes,
    BitVec.or_self, BitVec.and_self⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma comm (d : Bool) (a b : Word) : combine d a b = combine d b a := by
  cases d <;> simp [combine, BitVec.and_comm, BitVec.or_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive Live (target : Word) : ℕ → ℕ → Finset Word → Prop
  | done : Live target 0 0 {target}
  | unary {b t U a} (ha : proper a) (fresh : ~~~a ∉ insert a U)
      (tail : Live target b t (insert (~~~a) U)) : Live target b (t+1) (insert a U)
  | binary {b t U a c d} (ha : proper a) (hc : proper c) (ne : a ≠ c)
      (fresh : combine d a c ∉ insert a (insert c U))
      (tail : Live target b t (insert (combine d a c) U)) :
      Live target (b+1) t (insert a (insert c U))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Live.good {target : Word} (valid : proper target) {b t S} (h : Live target b t S) :
    ∀ a ∈ S, proper a := by
  induction h with
  | done => simpa using valid
  | unary ha hf ht ih =>
    intro a h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ha
    · exact ih _ (Finset.mem_insert_of_mem h)
  | binary ha hc _ _ ht ih =>
    intro a h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ha
    rcases Finset.mem_insert.mp h with rfl | h
    · exact hc
    · exact ih _ (Finset.mem_insert_of_mem h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Feasible (target : Word) (b t : ℕ) (S : Finset Word) : Prop :=
  ∃ i ≤ b, ∃ j ≤ t, ∃ T ⊆ S, Live target i j T

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma weaken {x b t S b' t' S'} (h : Feasible x b t S)
    (hb : b ≤ b') (ht : t ≤ t') (hs : S ⊆ S') : Feasible x b' t' S' := by
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  exact ⟨i,hi.trans hb,j,hj.trans ht,T,hT.trans hs,hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma ignore {x z b t S} (hx : proper x) (h : Feasible x b t (insert z S))
    (hz : z ∈ S ∨ ¬ proper z) : Feasible x b t S := by
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  refine ⟨i,hi,j,hj,T,?_,hL⟩
  intro a ha
  rcases Finset.mem_insert.mp (hT ha) with rfl | h
  · exact hz.resolve_right fun hnot => hnot (hL.good hx _ ha)
  · exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unary_pull {x a b t S} (hx : proper x) (ha : a ∈ S)
    (h : Feasible x b t (insert (~~~a) S)) : Feasible x b (t+1) S := by
  by_cases bad : ~~~a ∈ S ∨ ¬ proper (~~~a)
  · exact weaken (ignore hx h bad) le_rfl (by omega) (by rfl)
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  by_cases hm : ~~~a ∈ T
  · let U := T.erase (~~~a)
    have inS : U ⊆ S := by
      intro y hy; obtain ⟨hne,hyT⟩ := Finset.mem_erase.mp hy
      exact (Finset.mem_insert.mp (hT hyT)).resolve_left hne
    have p : proper a := by
      by_contra nh
      unfold proper at nh
      push Not at nh
      by_cases za : a = 0
      · subst a; exact bad (Or.inr (by simp [proper,top]))
      · have zt := nh za
        subst a; exact bad (Or.inr (by simp [proper,top]))
    refine ⟨i,hi,j+1,by omega,insert a U,Finset.insert_subset ha inS,Live.unary p ?_ ?_⟩
    · intro h'
      exact bad (Or.inl ((Finset.insert_subset ha inS) h'))
    · simpa [U, Finset.insert_erase hm] using hL
  · exact ⟨i,hi,j,by omega,T,fun y hy => (Finset.mem_insert.mp (hT hy)).resolve_left (by
      rintro rfl; exact hm hy), hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma binary_pull {x a c b t S} (hx : proper x) (d : Bool) (ha : a ∈ S) (hc : c ∈ S)
    (h : Feasible x b t (insert (combine d a c) S)) : Feasible x (b+1) t S := by
  let z := combine d a c
  by_cases redundant : z ∈ S ∨ ¬ proper z
  · exact weaken (ignore hx h redundant) (by omega) le_rfl (by rfl)
  have simple {a c : Word} (haS : a ∈ S) (hcS : c ∈ S) (hz : ¬ (combine d a c ∈ S ∨ ¬ proper (combine d a c))) :
      proper a := by
    constructor
    · rintro rfl
      rw [comm] at hz
      cases d
      · rw [(laws c).2.1] at hz
        exact hz (Or.inr fun h => h.1 rfl)
      · rw [(laws c).1] at hz
        exact hz (Or.inl hcS)
    · rintro rfl
      rw [comm] at hz
      cases d
      · rw [(laws c).2.2.2.1] at hz
        exact hz (Or.inl hcS)
      · rw [(laws c).2.2.1] at hz
        exact hz (Or.inr fun h => h.2 rfl)
  have pa := simple ha hc redundant
  have pc := simple hc ha (by rwa [comm])
  have unequal : a ≠ c := by
    rintro rfl; apply redundant; left; cases d <;> simpa [z,combine] using ha
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  by_cases hm : z ∈ T
  · let U := T.erase z
    have inS : U ⊆ S := by
      intro y hy; obtain ⟨hne,hyT⟩ := Finset.mem_erase.mp hy
      exact (Finset.mem_insert.mp (hT hyT)).resolve_left hne
    have subset := Finset.insert_subset ha (Finset.insert_subset hc inS)
    refine ⟨i+1,by omega,j,hj,insert a (insert c U),subset,Live.binary (d := d) pa pc unequal ?_ ?_⟩
    · intro hz
      exact redundant (Or.inl (subset hz))
    · simpa [U,z, Finset.insert_erase hm] using hL
  · exact ⟨i,by omega,j,hj,T,fun y hy => (Finset.mem_insert.mp (hT hy)).resolve_left (by
      rintro rfl; exact hm hy), hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Projection where
  q : Word → Word
  neg (a) : q (~~~a) = ~~~(q a)
  bin (d a c) : q (combine d a c) = combine d (q a) (q c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def constants (P : Projection) (S : Finset Word) : ℕ :=
  (S.filter fun w => ¬ proper (P.q w)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def charge (P : Projection) (w : Word) : ℕ := if proper (P.q w) then 0 else 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c_insert {P : Projection} (w : Word) (S : Finset Word) :
    constants P (insert w S) ≤ constants P S + charge P w := by
  by_cases h : proper (P.q w)
  · simp [constants, charge, Finset.filter_insert, h]
  · simpa [constants, charge, Finset.filter_insert, h] using
      Finset.card_insert_le w (S.filter fun v => ¬proper (P.q v))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c_fresh {P : Projection} (w : Word) (S : Finset Word) (hw : w ∉ S) :
    constants P (insert w S) = constants P S + charge P w := by
  by_cases h : proper (P.q w)
  · simp [constants, charge, Finset.filter_insert, h]
  · simp [constants, charge, Finset.filter_insert, h,
      Finset.card_insert_of_notMem (by simp [Finset.mem_filter,hw] :
        w ∉ S.filter fun v => ¬proper (P.q v))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma neg_proper_iff (w : Word) : proper (~~~w) ↔ proper w := by
  have aux (z : Word) : proper (~~~z) → proper z := by
    rintro h
    constructor <;> rintro rfl <;> simp [proper, top] at h
  exact ⟨aux _, fun h => aux (~~~w) (by simpa only [BitVec.not_not] using h)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma const_cases {w : Word} (h : ¬proper w) : w = 0 ∨ w = top := by
  by_cases z : w = 0
  · exact Or.inl z
  · exact Or.inr <| by by_contra ho; exact h ⟨z,ho⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma idle_of_const {a c : Word} (d : Bool) (h : ¬proper a ∨ ¬proper c) :
    combine d a c = a ∨ combine d a c = c ∨ ¬proper (combine d a c) := by
  have aux (a c : Word) (h : ¬proper c) :
      combine d a c = a ∨ ¬proper (combine d a c) := by
    rcases const_cases h with rfl | rfl <;> cases d
    · exact Or.inr fun h => h.1 (laws a).2.1
    · exact Or.inl (laws a).1
    · exact Or.inl (laws a).2.2.2.1
    · exact Or.inr fun h => h.2 (laws a).2.2.1
  rcases h with h | h
  · rw [comm]; exact Or.inr (aux c a h)
  · exact (aux a c h).imp_right Or.inr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma const_bin {a c : Word} (d : Bool) (ha : ¬proper a) (hc : ¬proper c) :
    ¬proper (combine d a c) := by
  rcases idle_of_const d (Or.inl ha : ¬proper a ∨ ¬proper c) with e|e|h
  · rwa [e]
  · rwa [e]
  · exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem project_live (P : Projection) {x : Word} (hx : proper (P.q x)) {b t S}
    (h : Live x b t S) :
    ∃ n, n + constants P S ≤ b ∧ Feasible (P.q x) n t (S.image P.q) := by
  induction h with
  | done =>
    refine ⟨0, by simp [constants,hx], 0, le_rfl,0,le_rfl,{P.q x}, by simp, .done⟩
  | @unary b t U a _ fresh tail ih =>
    obtain ⟨n,hn,h⟩ := ih
    have f : ~~~a ∉ U := fun he => fresh (Finset.mem_insert_of_mem he)
    have eq := c_fresh (P := P) (~~~a) U f
    have le := c_insert (P := P) a U
    have ng : charge P (~~~a) = charge P a := by simp [charge,P.neg,neg_proper_iff]
    refine ⟨n, by omega, ?_⟩
    rw [Finset.image_insert]
    rw [Finset.image_insert,P.neg] at h
    apply unary_pull hx (Finset.mem_insert_self ..)
    apply weaken h le_rfl le_rfl
    exact Finset.insert_subset_insert _ (Finset.subset_insert ..)
  | @binary b t U a c d _ _ _ fresh tail ih =>
    let z := combine d a c
    let A := insert (P.q a) (insert (P.q c) (U.image P.q))
    obtain ⟨n,hn,h⟩ := ih
    have f : z ∉ U := fun he => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he))
    have ez := c_fresh (P := P) z U f
    have ec := c_insert (P := P) c U
    have ea := c_insert (P := P) a (insert c U)
    change n + constants P (insert z U) ≤ b at hn
    have hq : P.q z = combine d (P.q a) (P.q c) := P.bin ..
    have htail : Feasible (P.q x) n t (insert (P.q z) A) := by
      rw [Finset.image_insert] at h
      apply weaken h le_rfl le_rfl
      exact Finset.insert_subset_insert _ ((Finset.subset_insert ..).trans (Finset.subset_insert ..))
    rw [Finset.image_insert,Finset.image_insert]
    change ∃ n, _ ∧ Feasible _ n t A
    have ma : P.q a ∈ A := Finset.mem_insert_self ..
    have mc : P.q c ∈ A := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    by_cases pc : proper (P.q c) <;> by_cases pa : proper (P.q a)
    · have aa : charge P a = 0 := by simp [charge,pa]
      have ac : charge P c = 0 := by simp [charge,pc]
      refine ⟨n+1, by omega, binary_pull hx d ma mc ?_⟩
      rwa [←hq]
    all_goals
      have idle : P.q z ∈ A ∨ ¬proper (P.q z) := by
        rw [hq]
        rcases idle_of_const d (by tauto : ¬proper (P.q a) ∨ ¬proper (P.q c)) with ha|hc|hn
        · exact Or.inl (by rwa [ha])
        · exact Or.inl (by rwa [hc])
        · exact Or.inr hn
      refine ⟨n, ?_, ignore hx htail idle⟩
    · have aa : charge P a = 1 := by simp [charge,pa]
      have ac : charge P c = 0 := by simp [charge,pc]
      omega
    · have aa : charge P a = 0 := by simp [charge,pa]
      have ac : charge P c = 1 := by simp [charge,pc]
      omega
    · have aa : charge P a = 1 := by simp [charge,pa]
      have ac : charge P c = 1 := by simp [charge,pc]
      have az : charge P z = 1 := by simp [charge,hq,const_bin d pa pc]
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bit (a : Word) (i : Fin 512) : Bool := a[i.val]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tab (f : Fin 512 → Bool) : Word :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tab_bit (f : Fin 512 → Bool) (i : Fin 512) : bit (tab f) i = f i := by
  unfold bit tab
  rw [← BitVec.getLsbD_eq_getElem]
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceQ (f : Fin 512 → Fin 512) : Projection where
  q a := tab (fun i => bit a (f i))
  neg a := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    change bit (tab _) ⟨i, hi⟩ = (~~~(tab _))[i]
    rw [tab_bit,BitVec.getElem_not]
    change bit (~~~a) _ = !bit (tab _) ⟨i,hi⟩
    rw [tab_bit]; exact BitVec.getElem_not _
  bin d a c := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    cases d <;> change bit (tab _) ⟨i,hi⟩ = _ <;> rw [tab_bit]
    · change _ = (tab _ &&& tab _)[i]
      rw [BitVec.getElem_and]
      change _ = (bit (tab _) ⟨i,hi⟩ && bit (tab _) ⟨i,hi⟩)
      rw [tab_bit,tab_bit]; exact BitVec.getElem_and _
    · change _ = (tab _ ||| tab _)[i]
      rw [BitVec.getElem_or]
      change _ = (bit (tab _) ⟨i,hi⟩ || bit (tab _) ⟨i,hi⟩)
      rw [tab_bit,tab_bit]; exact BitVec.getElem_or _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q_bit (f : Fin 512 → Fin 512) (w : Word) (i : Fin 512) :
    bit ((faceQ f).q w) i = bit w (f i) := tab_bit _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def available (P : Projection) (S R : Finset Word) : Finset Word := S.image P.q ∪ R

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Guard (P : Projection) (x : Word) (S R : Finset Word) (t lo spent : ℕ) : Prop :=
  proper (P.q x) ∧ ∀ b, Feasible (P.q x) b t (available P S R) → lo ≤ b + spent

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma guard_bound {P x b t S R lo spent} (g : Guard P x S R t lo spent)
    (h : Live x b t S) : lo + constants P S ≤ b + spent := by
  obtain ⟨n,hn,hf⟩ := project_live P g.1 h
  have hb := g.2 n <| weaken hf le_rfl le_rfl Finset.subset_union_left
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma avail_child {P : Projection} {S T R : Finset Word} {z : Word}
    (h : T ⊆ insert z S) : available P T R ⊆ insert (P.q z) (available P S R) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hi|hr
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_insert.mp (h ha) with rfl|hs
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs))
  · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hr)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cost (P : Projection) (S R : Finset Word) (z : Word) : ℕ :=
  if P.q z ∈ available P S R ∨ ¬ proper (P.q z) then 0 else 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma guard_binary {P x S T R t lo spent a c d} (g : Guard P x S R t lo spent)
    (ha : a ∈ S) (hc : c ∈ S) (hT : T ⊆ insert (combine d a c) S) :
    Guard P x T R t lo (spent + cost P S R (combine d a c)) := by
  refine ⟨g.1,?_⟩
  intro b h
  let z := combine d a c
  let A := available P S R
  have h' := weaken h le_rfl le_rfl (avail_child hT)
  change Feasible _ _ _ (insert (P.q z) A) at h'
  change lo ≤ b+(spent+cost P S R z)
  unfold cost
  split_ifs with free
  · simpa using g.2 b (ignore g.1 h' free)
  · have ma : P.q a ∈ A := Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
    have mc : P.q c ∈ A := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
    have hq : P.q z = combine d (P.q a) (P.q c) := P.bin ..
    rw [hq] at h'
    have hB := g.2 _ (binary_pull g.1 d ma mc h')
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma guard_unary {P x S T R t lo spent a} (g : Guard P x S R (t+1) lo spent)
    (ha : a ∈ S) (hT : T ⊆ insert (~~~a) S) :
    Guard P x T R t lo spent := by
  refine ⟨g.1,?_⟩
  intro b h
  have h' := weaken h le_rfl le_rfl (avail_child hT)
  rw [P.neg] at h'
  exact g.2 b (unary_pull g.1 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)) h')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma count_live {x b t S} (h : Live x b t S) : S.card ≤ b+1 := by
  induction h with
  | done => simp
  | @unary b t U a _ fresh tail ih =>
    have hn : ~~~a ∉ U := fun he => fresh (Finset.mem_insert_of_mem he)
    rw [Finset.card_insert_of_notMem hn] at ih
    exact (Finset.card_insert_le ..).trans ih
  | @binary b t U a c d _ _ _ fresh tail ih =>
    have hn : combine d a c ∉ U := fun he => fresh
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he))
    rw [Finset.card_insert_of_notMem hn] at ih
    have hc := Finset.card_insert_le c U
    have ha := Finset.card_insert_le a (insert c U)
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def distinguishes (t : ℕ) (w : Word) (i j : Fin 512) : Prop :=
  if t = 0 then bit w i = true ∧ bit w j = false else bit w i ≠ bit w j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma distinguish_bit {a c : Word} {d : Bool} {t : ℕ} {i j : Fin 512}
    (h : distinguishes t (combine d a c) i j) :
    distinguishes t a i j ∨ distinguishes t c i j := by
  have eq (k : Fin 512) : bit (combine d a c) k =
      if d then (bit a k || bit c k) else (bit a k && bit c k) := by
    cases d <;> simp [bit,combine]
  cases d <;> by_cases ht : t=0 <;>
    simp only [distinguishes,ht,eq,ite_true,ite_false,Bool.false_eq_true] at h ⊢ <;>
    cases e1 : bit a i <;> cases e2 : bit a j <;> cases e3 : bit c i <;> cases e4 : bit c j <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma distinguish_old {a : Word} {t : ℕ} {i j : Fin 512} (h : distinguishes t a i j) :
    distinguishes (t+1) a i j := by
  simp only [distinguishes,Nat.succ_ne_zero,ite_false]
  by_cases ht : t=0
  · simp only [distinguishes,ht,ite_true] at h
    simp [h.1,h.2]
  · simpa [distinguishes,ht] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma distinguishes_live {x b t S} (h : Live x b t S) {i j : Fin 512}
    (hi : bit x i = true) (hj : bit x j = false) : ∃ a ∈ S, distinguishes t a i j := by
  induction h with
  | done => exact ⟨x,by simp,by simp [distinguishes,hi,hj]⟩
  | unary _ _ tail ih =>
    obtain ⟨a,ha,hm⟩ := ih
    rcases Finset.mem_insert.mp ha with rfl | hw
    · refine ⟨_,Finset.mem_insert_self ..,?_⟩
      have h := distinguish_old hm
      simpa [distinguishes,bit] using h
    · exact ⟨_,Finset.mem_insert_of_mem hw,distinguish_old hm⟩
  | binary _ _ _ _ tail ih =>
    obtain ⟨a,ha,hm⟩ := ih
    rcases Finset.mem_insert.mp ha with rfl | hw
    · rcases distinguish_bit hm with hl|hr
      · exact ⟨_,Finset.mem_insert_self ..,hl⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),hr⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw),hm⟩

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gv (w : List Word) (g : Gate) : Word :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => xs.foldr (combine false) top
  | .or => xs.foldr (combine true) 0
  | .not => ~~~(xs.headD 0)
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def execute (gs : List Gate) (w : List Word) : List Word :=
  gs.foldl (fun l g => l ++ [gv l g]) w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pool (w : List Word) : Finset Word := insert 0 (insert top w.toFinset)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma read_mem (w : List Word) (i : Nat) : w.getD i 0 ∈ pool w := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : w[i]? with
  | none => exact Finset.mem_insert_self ..
  | some a =>
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (List.mem_toFinset.mpr (List.mem_of_getElem? hi)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def negative (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gate_pull {x b t w} (hx : proper x) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : Feasible x b t (insert (gv w g) (pool w))) :
    Feasible x (b + (if negative g then 0 else 1))
      (t + (if negative g then 1 else 0)) (pool w) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  obtain ⟨ops,hi⟩ := hg
  have zero' : 0 ∈ pool w := Finset.mem_insert_self ..
  have top' : top ∈ pool w := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  have idle (z : Word) (hz : z ∈ pool w) (h : Feasible x b t (insert z (pool w))) :
      Feasible x (b+1) t (pool w) := by
    exact weaken (ignore hx h (Or.inl hz)) (by omega) le_rfl (by rfl)
  cases ins with
  | nil =>
    rcases ops with rfl | rfl | rfl
    · exact idle top top' h
    · exact idle 0 zero' h
    · exact unary_pull hx zero' h
  | cons a ins =>
    cases ins with
    | nil =>
      rcases ops with rfl | rfl | rfl
      · exact idle _ (read_mem _ a) (by simpa only [gv,List.map_cons,List.map_nil,
          List.foldr_cons,List.foldr_nil,(laws _).2.2.2.1] using h)
      · exact idle _ (read_mem _ a) (by simpa only [gv,List.map_cons,List.map_nil,
          List.foldr_cons,List.foldr_nil,(laws _).1] using h)
      · exact unary_pull hx (read_mem _ a) h
    | cons c is =>
      cases is with
      | cons i ss => simp at hi
      | nil =>
        rcases ops with rfl | rfl | rfl
        · exact binary_pull (t := t) hx false (read_mem _ a) (read_mem _ c) (by
            simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
              (laws _).2.2.2.1] using h)
        · exact binary_pull (t := t) hx true (read_mem _ a) (read_mem _ c) (by
            simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
              (laws _).1] using h)
        · exact unary_pull hx (read_mem _ a) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma extract {x} (hx : proper x) (gs : List Gate) (w : List Word)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hout : x ∈ execute gs w) :
    Feasible x (gs.filter (fun g => !negative g)).length (gs.filter negative).length (pool w) := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0,le_rfl,0,le_rfl,{x},Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hout))),.done⟩
  | cons g gs ih =>
    have h := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    have e : pool (w ++ [gv w g]) = insert (gv w g) (pool w) := by
      ext a; simp [pool]; tauto
    rw [e] at h
    have m := gate_pull hx g (legal g (by simp)) h
    cases n : negative g <;> simpa [List.filter_cons,n] using m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bit_zero (i) : bit 0 i = false := by simp [bit]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bit_top (i) : bit top i = true := by
  change (BitVec.allOnes 512)[i.val] = true
  exact BitVec.getElem_allOnes ..
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bit_not (w : Word) (i) : bit (~~~w) i = !bit w i := BitVec.getElem_not _
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bit_bin (d : Bool) (a b : Word) (i) : bit (combine d a b) i =
    if d then bit a i || bit b i else bit a i && bit b i := by
  cases d <;> simp [bit,combine]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma read_bit (w : List Word) (j : Nat) (i : Fin 512) :
    (w.map (fun a => bit a i)).getD j false = bit (w.getD j 0) i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma run_bit (g : Gate) (w : List Word) (i : Fin 512)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit (gv w g) i = g.op.eval (g.inputs.map fun j => (w.map (fun a => bit a i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [read_bit]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_top _
    | cons a l ih =>
      change bit (combine false _ _) i = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit (w.getD a 0) i && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit (combine true _ _) i = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit (w.getD a 0) i || x) ih
  · cases l with
    | nil => exact (bit_not (0 : Word) i).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_not _ _
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma execute_bits (gs : List Gate) (w : List Word) (i : Fin 512)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (fun a => bit a i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (fun a => bit a i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit g w i (hg g (by simp))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma foldl_append_getD {α : Type} (f : List α → Gate → α) (gs : List Gate)
    (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (l ++ [f l g]).length := by simp; omega
    rw [ih (l ++ [f l g]) hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def inputColumn0 : Word := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def inputColumn1 : Word := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def inputColumn2 : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def inputColumn3 : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def inputColumn4 : Word := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def inputColumn5 : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def inputColumn6 : Word := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def inputColumn7 : Word := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
def inputColumn8 : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def raw : List Word := [inputColumn0, inputColumn1, inputColumn2, inputColumn3, inputColumn4, inputColumn5, inputColumn6, inputColumn7, inputColumn8]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def target : Word := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def testRow (i : Fin 512) (j : Fin 9) := i.val.testBit j.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawRow (i : Fin 512) : raw.map (fun a => bit a i) = List.ofFn (testRow i) := by
  have ok : ∀ r : Fin 512, raw.map (fun a => bit a r) = List.ofFn (testRow r) := by decide +kernel
  exact ok i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma targetRow (i : Fin 512) : bit target i = edgeF (testRow i) := by
  have ok : ∀ r : Fin 512, bit target r = edgeF (testRow r) := by decide +kernel
  exact ok i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma targetProper : proper target := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma target_mem (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = edgeF y) :
    target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have e : w.getD C.output 0 = target := by
    apply BitVec.eq_of_getElem_eq
    intro r hr
    change bit (w.getD C.output 0) ⟨r,hr⟩ = bit target ⟨r,hr⟩
    rw [targetRow, ←read_bit]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ (fun g hg => (hf g hg).1),rawRow]
    exact he _
  have h := read_mem w C.output
  rw [e] at h
  simpa only [pool,Finset.mem_insert,List.mem_toFinset, targetProper.1,targetProper.2,
    false_or] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def extra : Word := combine true (raw.getD 0 0) (raw.getD 2 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def start : List Word := raw ++ [extra]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma extraRow (r : Fin 512) : bit extra r = (testRow r 0 || testRow r 2) := by
  have ok : ∀ i : Fin 512, bit extra i = (testRow i 0 || testRow i 2) := by decide +kernel
  exact ok r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma first_value {g : Gate} {gs : List Gate}
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (first : ∀ y : Fin 9 → Bool,
      ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) :
    gv raw g = extra := by
  apply BitVec.eq_of_getElem_eq
  intro r hr
  let i : Fin 512 := ⟨r,hr⟩
  change bit (gv raw g) i = bit extra i
  rw [extraRow, run_bit g raw i hg,rawRow]
  have h := first (testRow i)
  simp only [Circuit.wires,List.foldl_cons] at h
  rw [foldl_append_getD _ gs _ 9 (by simp) false] at h
  simpa [List.getD_eq_getElem?_getD] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma uniqueNegCount (gs : List Gate)
    (h : ∃! i : Fin gs.length, negative (gs.get i) = true) :
    (gs.filter negative).length = 1 := by
  induction gs with
  | nil => obtain ⟨i, _⟩ := h; exact Fin.elim0 i
  | cons g gs ih =>
    obtain ⟨i, hi, only⟩ := h
    by_cases hg : negative g = true
    · have hone : (0 : Fin (g :: gs).length) = i := only 0 hg
      have nil : gs.filter negative = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha hn
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
        have hs : negative ((g :: gs).get j.succ) = true := by
          change negative (gs.get j) = true
          rwa [hj]
        have eq := (only j.succ hs).trans hone.symm
        exact (Fin.succ_ne_zero j) eq
      simp [hg,nil]
    · have htail : ∃! j : Fin gs.length, negative (gs.get j) = true := by
        cases i using Fin.cases with
        | zero => exact (hg hi).elim
        | succ j =>
          refine ⟨j, hi, ?_⟩
          intro k hk
          exact Fin.succ_injective _ (only k.succ hk)
      simpa [hg] using ih htail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma first_nonneg {g : Gate} {gs : List Gate}
    (hfirst : ∀ y : Fin 9 → Bool,
      ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) :
    negative g = false := by
  cases hop : g.op <;> simp only [negative,hop]
  let x : Fin 9 → Bool := fun _ => false
  have z (j : ℕ) : (List.ofFn x).getD j false = false := by
    by_cases hj : j < 9
    · have hh : j < (List.ofFn x).length := by simpa only [List.length_ofFn] using hj
      rw [List.getD_eq_getElem _ _ hh,List.getElem_ofFn]
    · have hn : (List.ofFn x).length ≤ j := by simpa using Nat.le_of_not_gt hj
      exact List.getD_eq_default _ _ hn
  have h := hfirst x
  simp only [Circuit.wires, List.foldl_cons] at h
  have hl : 9 < (List.ofFn x ++ [g.op.eval (g.inputs.map fun j =>
      (List.ofFn x).getD j false)]).length := by simp
  rw [foldl_append_getD _ gs _ 9 hl false] at h
  have heq : (List.ofFn x ++ [g.op.eval (g.inputs.map fun j =>
      (List.ofFn x).getD j false)]).getD 9 false =
      g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false) := by
    simp [List.getD_eq_getElem?_getD]
  rw [heq,hop] at h
  cases he : g.inputs with
  | nil => simp [he,GateOp.eval,x] at h
  | cons a as =>
    simp only [he, List.map_cons, GateOp.eval, List.headD_cons, z] at h
    exact Bool.noConfusion h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma neg_iff (g : Gate) : negative g = true ↔ g.op = GateOp.not := by
  cases g with
  | mk op xs => cases op <;> simp [negative]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma starts {C : Circuit} (hsize : C.size ≤ 15) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hn : ∃! i : Fin C.gates.length, (C.gates.get i).op = GateOp.not)
    (hw9 : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2))
    (he : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = edgeF y) :
    Feasible target 13 1 start.toFinset := by
  obtain ⟨i,hi,only⟩ := hn
  have hn1 := uniqueNegCount C.gates ⟨i,(neg_iff _).2 hi,fun j hj => only j ((neg_iff _).1 hj)⟩
  cases hgs : C.gates with
  | nil => simp [hgs] at hn1
  | cons g gs =>
    have hlen : gs.length ≤ 14 := by
      change C.gates.length ≤ 15 at hsize; rw [hgs] at hsize; simp at hsize; omega
    have hh : ∀ y : Fin 9 → Bool,
        ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2) := by
      intro y; simpa only [Circuit.wires,hgs] using hw9 y
    have hneg := first_nonneg hh
    rw [hgs] at hn1
    simp only [List.filter_cons, hneg, Bool.false_eq_true, ↓reduceIte] at hn1
    have counts := List.length_eq_length_filter_add (l:=gs) negative
    change gs.length = (gs.filter negative).length + (gs.filter (fun g => !negative g)).length at counts
    have hv := first_value (hf g (by rw [hgs]; simp)).1 hh
    have hm := target_mem C hf he
    rw [hgs] at hm
    change target ∈ execute gs (raw ++ [gv raw g]) at hm
    rw [hv] at hm
    have h := extract targetProper gs start (fun a ha => hf a (by rw [hgs]; simp [ha])) hm
    have h' := weaken h (show (gs.filter (fun g => !negative g)).length ≤ 13 by omega)
      (show (gs.filter negative).length ≤ 1 by omega) (by rfl)
    exact ignore targetProper (ignore targetProper h' (Or.inr fun q => q.1 rfl))
      (Or.inr fun q => q.2 rfl)

-- Prune live suffixes with paired truth-table rows and induced graph lower bounds.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Charts (x : Word) where
  p : Fin 512 → Fin 512
  n : Fin 512 → Fin 512
  hp : ∀ i, bit x (p i) = true
  hn : ∀ i, bit x (n i) = false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Wire {x : Word} (c : Charts x) where
  w : Word
  p : Word
  n : Word
  hp : ∀ i, bit p i = bit w (c.p i)
  hn : ∀ i, bit n i = bit w (c.n i)

namespace Wire
variable {x : Word} {c : Charts x}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def binary (d : Bool) (a b : Wire c) : Wire c :=
  ⟨combine d a.w b.w,combine d a.p b.p,combine d a.n b.n,
    fun i => by simp only [bit_bin,a.hp,b.hp],
    fun i => by simp only [bit_bin,a.hn,b.hn]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def flip (a : Wire c) : Wire c :=
  ⟨~~~a.w,~~~a.p,~~~a.n,fun i => by simp only [bit_not,a.hp],
    fun i => by simp only [bit_not,a.hn]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sep (t : ℕ) (a : Wire c) : Word :=
  if t = 0 then a.p &&& ~~~a.n else a.p ^^^ a.n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sep_bit {t : ℕ} (a : Wire c) (i : Fin 512) :
    bit (a.sep t) i = true ↔ distinguishes t a.w (c.p i) (c.n i) := by
  have p := a.hp i
  have n := a.hn i
  by_cases ht : t = 0
  · simpa only [sep,distinguishes,ht,ite_true,bit,BitVec.getElem_and,BitVec.getElem_not,
      Bool.and_eq_true,Bool.not_eq_true'] using (and_congr (congrArg (· = true) p).to_iff
      (congrArg (· = false) n).to_iff)
  · simp only [sep,distinguishes,ht,ite_false,bit,BitVec.getElem_xor]
    change (bit a.p i ^^ bit a.n i) = true ↔ bit a.w (c.p i) ≠ bit a.w (c.n i)
    rw [p,n]
    cases bit a.w (c.p i) <;> cases bit a.w (c.n i) <;> decide
end Wire

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wires {x : Word} {c : Charts x} (v : List (Wire c)) : Finset Word :=
  (v.map Wire.w).toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cover {x : Word} {c : Charts x} (t : ℕ) : List (Wire c) → Word
  | [] => 0
  | w :: v => w.sep t ||| cover t v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_bit {x : Word} {c : Charts x} (t : ℕ) (v : List (Wire c)) (i : Fin 512) :
    bit (cover t v) i = true ↔ ∃ w ∈ v, distinguishes t w.w (c.p i) (c.n i) := by
  induction v with
  | nil => simp only [cover,bit_zero,Bool.false_eq_true,List.not_mem_nil,false_and]; tauto
  | cons a v ih =>
    change bit (combine true _ _) i = true ↔ _
    simp only [bit_bin,ite_true,Bool.or_eq_true,Wire.sep_bit,ih,List.mem_cons,
      exists_eq_or_imp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma distinguish_more {a : Word} {i j : Fin 512} {u t : ℕ}
    (h : distinguishes u a i j) (hu : u ≤ t) : distinguishes t a i j := by
  cases t with
  | zero => simpa [show u=0 by omega] using h
  | succ t =>
    have hp := distinguish_old h
    simpa only [distinguishes,Nat.succ_ne_zero,ite_false] using hp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_live {x : Word} (c : Charts x) {b j t} (v : List (Wire c))
    (h : Live x b j (wires v)) (ht : j ≤ t) : cover t v = top := by
  apply BitVec.eq_of_getElem_eq; intro k hk
  let i : Fin 512 := ⟨k,hk⟩
  change bit (cover t v) i = bit top i
  rw [bit_top,cover_bit]
  obtain ⟨a,ha,hd⟩ := distinguishes_live h (c.hp i) (c.hn i)
  obtain ⟨w, hw, hwa⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact ⟨w,hw,hwa ▸ distinguish_more hd ht⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Exact (x : Word) (b t : ℕ) (S : Finset Word) : Prop :=
  ∃ n ≤ b, ∃ j ≤ t, Live x n j S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma exact_size {x b t S} (h : Exact x b t S) : S.card ≤ b+1 := by
  obtain ⟨n,hn,j,_,h⟩ := h
  exact (count_live h).trans (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma exact_cover {x : Word} (c : Charts x) {b t} (v : List (Wire c))
    (h : Exact x b t (wires v)) : cover t v = top := by
  obtain ⟨n,_,j,hj,h⟩ := h
  exact cover_live c v h hj

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive Step {x : Word} (c : Charts x) where
  | flip (a : Wire c) (keep : Bool)
  | binary (d : Bool) (a b : Wire c) (keepA keepB : Bool)

namespace Step
variable {x : Word} {c : Charts x}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def out : Step c → Wire c
  | .flip a _ => a.flip
  | .binary d a b _ _ => a.binary d b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rest (s : Step c) (v : List (Wire c)) : List (Wire c) :=
  match s with
  | .flip a ka => v.filter (fun y => ka || y.w != a.w)
  | .binary _ a b ka kb =>
    v.filter (fun y => (ka || y.w != a.w) && (kb || y.w != b.w))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def after (s : Step c) (v : List (Wire c)) := s.out :: s.rest v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def budget (s : Step c) (b t : ℕ) :=
  match s with
  | .flip .. => (b,t-1)
  | .binary .. => (b-1,t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def all (b t : ℕ) (v : List (Wire c)) : List (Step c) :=
  v.flatMap fun a =>
    (if t=0 then [] else [Step.flip a false,Step.flip a true]) ++
    (if b=0 then [] else v.flatMap fun w =>
      if a.w.toNat < w.w.toNat then
        [false,true].flatMap fun d => [false,true].flatMap fun ka =>
          [false,true].map (fun kb => Step.binary d a w ka kb)
      else [])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mem_flip {a : Wire c} {b t : ℕ} {v : List (Wire c)} (ht : 0<t) (ha : a ∈ v)
    (ka : Bool) : Step.flip a ka ∈ all b t v := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_append_left _ ?_⟩
  cases ka <;> simp [show t≠0 by omega]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mem_binary {a w : Wire c} {b t : ℕ} {v : List (Wire c)} (hb : 0<b)
    (ha : a ∈ v) (hw : w ∈ v) (hlt : a.w.toNat < w.w.toNat) (d ka kb : Bool) :
    Step.binary d a w ka kb ∈ all b t v := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_append_right _ ?_⟩
  simp only [show b≠0 by omega,ite_false]
  apply List.mem_flatMap.mpr
  refine ⟨w,hw,?_⟩
  simp only [hlt,ite_true]
  apply List.mem_flatMap.mpr
  refine ⟨d,by cases d <;> simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨ka,by cases ka <;> simp,List.mem_map.mpr ⟨kb,by cases kb <;> simp,rfl⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mem_wires {v : List (Wire c)} {w : Word} : w ∈ wires v ↔ ∃ a ∈ v, a.w = w := by
  simp [wires]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma next_flip {a : Wire c} {v : List (Wire c)} {U : Finset Word}
    (hs : wires v = insert a.w U) :
    wires ((Step.flip a (decide (a.w ∈ U))).after v) = insert (~~~a.w) U := by
  ext z
  simp only [after,wires,List.map_cons,List.toFinset_cons,Finset.mem_insert]
  apply or_congr_right
  change z ∈ wires (v.filter _) ↔ z ∈ U
  rw [mem_wires]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨hv,cond⟩ := List.mem_filter.mp hq
    have eq : q.w ∈ insert a.w U := hs ▸ (mem_wires.mpr ⟨q,hv,rfl⟩)
    rcases Finset.mem_insert.mp eq with he|h
    · simpa [he] using cond
    · exact h
  · intro hz
    have hv : z ∈ wires v := hs ▸ Finset.mem_insert_of_mem hz
    obtain ⟨q,hq,eq⟩ := mem_wires.mp hv
    refine ⟨q,List.mem_filter.mpr ⟨hq,?_⟩,eq⟩
    by_cases h : z=a.w
    · simp [←h,eq,hz]
    · simp [eq,h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma next_bin {a w : Wire c} {v : List (Wire c)} {U : Finset Word}
    (hs : wires v = insert a.w (insert w.w U)) :
    wires ((Step.binary d a w (decide (a.w ∈ U)) (decide (w.w ∈ U))).after v) =
      insert (combine d a.w w.w) U := by
  ext z
  simp only [after,wires,List.map_cons,List.toFinset_cons,Finset.mem_insert]
  apply or_congr_right
  change z ∈ wires (v.filter _) ↔ z ∈ U
  rw [mem_wires]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨hv,cond⟩ := List.mem_filter.mp hq
    have eq : q.w ∈ insert a.w (insert w.w U) := hs ▸ (mem_wires.mpr ⟨q,hv,rfl⟩)
    obtain ⟨c1,c2⟩ := Bool.and_eq_true_iff.mp cond
    rcases Finset.mem_insert.mp eq with he|h
    · simpa [he] using c1
    rcases Finset.mem_insert.mp h with he|h
    · simpa [he] using c2
    · exact h
  · intro hz
    have hv : z ∈ wires v := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
    obtain ⟨q,hq,eq⟩ := mem_wires.mp hv
    refine ⟨q,List.mem_filter.mpr ⟨hq,?_⟩,eq⟩
    apply Bool.and_eq_true_iff.mpr
    constructor
    · by_cases h : z=a.w
      · simp [←h,eq,hz]
      · simp [eq,h]
    · by_cases h : z=w.w
      · simp [←h,eq,hz]
      · simp [eq,h]
end Step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def eligible {x : Word} {c : Charts x} (v : List (Wire c)) (s : Step c) : Prop :=
  proper s.out.w ∧ s.out.w ∉ wires v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma descend {x : Word} (c : Charts x) (hx : proper x) {b t : ℕ} {v : List (Wire c)}
    (h : Exact x b t (wires v)) :
    x ∈ wires v ∨ ∃ s ∈ Step.all b t v, eligible v s ∧
      Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)) := by
  obtain ⟨n,hn,j,hj,h⟩ := h
  generalize hs : wires v = S at h
  cases h with
  | done =>
    left; simp
  | @unary nb nt U a pa fresh tail =>
    right
    have hv : a ∈ wires v := hs ▸ Finset.mem_insert_self ..
    obtain ⟨aw,hw,eq⟩ := Step.mem_wires.mp hv
    subst a
    let s := Step.flip aw (decide (aw.w ∈ U))
    refine ⟨s,Step.mem_flip (by omega) hw _,⟨tail.good hx _ (Finset.mem_insert_self ..),?_⟩,
      n,hn,nt,by change nt ≤ t-1; omega,?_⟩
    · change ~~~aw.w ∉ wires v
      rwa [hs]
    · change Live x n nt (wires ((Step.flip aw _).after _))
      rwa [Step.next_flip hs]
  | @binary nb nt U a w d pa pw ne fresh tail =>
    right
    have ha : a ∈ wires v := hs ▸ Finset.mem_insert_self ..
    have hw : w ∈ wires v := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    obtain ⟨aw,ah,a_eq⟩ := Step.mem_wires.mp ha
    obtain ⟨ww,wh,w_eq⟩ := Step.mem_wires.mp hw
    subst a; subst w
    have ord : aw.w.toNat ≠ ww.w.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
    have mk (y z : Wire c) (hy : y ∈ v) (hz : z ∈ v) (hlt : y.w.toNat < z.w.toNat)
        (heads : wires v = insert y.w (insert z.w U))
        (fresh' : combine d y.w z.w ∉ wires v)
        (tail' : Live x nb j (insert (combine d y.w z.w) U)) :
        ∃ s ∈ Step.all b t v, eligible v s ∧
          Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)) := by
      let s := Step.binary d y z (decide (y.w ∈ U)) (decide (z.w ∈ U))
      refine ⟨s,Step.mem_binary (by omega) hy hz hlt ..,
        ⟨tail'.good hx _ (Finset.mem_insert_self ..), fresh'⟩,
        nb,by change nb ≤ b-1; omega,j,hj,?_⟩
      change Live x nb j (wires ((Step.binary d y z _ _).after _))
      rwa [Step.next_bin heads]
    rcases lt_or_gt_of_ne ord with hlt|hlt
    · exact mk aw ww ah wh hlt hs (hs ▸ fresh) tail
    · apply mk ww aw wh ah hlt
      · rwa [Finset.insert_comm]
      · rwa [comm,hs]
      · rwa [comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Basis (x : Word) where
  mask : Word
  raw : List Word
  lo : ℕ
  proj : Projection
  zero : proj.q 0 = 0
  one : proj.q top = top
  refl (a b : Word) : a &&& mask = b &&& mask → proj.q a = proj.q b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Price (x : Word) where
  basis : Basis x
  spent : ℕ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Basis.base {x : Word} (f : Basis x) := (f.raw.map f.proj.q).toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Price.Valid {x : Word} (f : Price x) (t : ℕ) (S : Finset Word) :=
  Guard f.basis.proj x S f.basis.base t f.basis.lo f.spent

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def maskedConst (m a : Word) : Bool := (a &&& m) == 0 || (a &&& m) == m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def freeAt {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) (w : Word) : Bool :=
  maskedConst f.mask w || v.any (fun a => (w &&& f.mask) == (a.w &&& f.mask)) ||
    f.raw.any (fun a => (w &&& f.mask) == (a &&& f.mask))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma maskedConst_sound {x : Word} {f : Basis x} {a : Word}
    (h : maskedConst f.mask a = true) : ¬proper (f.proj.q a) := by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · have eq := f.refl a 0 (by simpa using beq_iff_eq.mp h)
    rw [f.zero] at eq; exact fun hp => hp.1 eq
  · have eq := f.refl a top (by simpa only [top,BitVec.allOnes_and] using beq_iff_eq.mp h)
    rw [f.one] at eq; exact fun hp => hp.2 eq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma freeAt_sound {x : Word} {c : Charts x} {f : Basis x} {v : List (Wire c)} {w : Word}
    (h : freeAt f v w = true) :
    f.proj.q w ∈ available f.proj (wires v) f.base ∨ ¬proper (f.proj.q w) := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inr (maskedConst_sound h)
    · obtain ⟨a,ha,e⟩ := List.any_eq_true.mp h
      rw [f.refl w a.w (beq_iff_eq.mp e)]
      exact Or.inl (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Step.mem_wires.mpr ⟨a,ha,rfl⟩)))
  · obtain ⟨a,ha,e⟩ := List.any_eq_true.mp h
    rw [f.refl w a (beq_iff_eq.mp e)]
    exact Or.inl (Finset.mem_union_right _
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Price.advance {x : Word} {c : Charts x} (f : Price x) (v : List (Wire c)) (s : Step c) :
    Price x := match s with
  | .flip .. => f
  | .binary .. => ⟨f.basis,f.spent + (if freeAt f.basis v s.out.w then 0 else 1)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Step.child_subset {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    wires (s.after v) ⊆ insert s.out.w (wires v) := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  rcases List.mem_cons.mp hw with rfl|hw
  · exact Finset.mem_insert_self ..
  · have h : w ∈ v := by cases s <;> exact List.mem_of_mem_filter hw
    exact Finset.mem_insert_of_mem (Step.mem_wires.mpr ⟨w,h,rfl⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma advance_flip {x : Word} {c : Charts x} {p : Price x} {a : Wire c}
    {v : List (Wire c)} {t : ℕ} (hv : p.Valid (t+1) (wires v)) (ha : a ∈ v) (ka : Bool) :
    (p.advance v (.flip a ka)).Valid t (wires ((Step.flip a ka).after v)) :=
  guard_unary hv (Step.mem_wires.mpr ⟨a,ha,rfl⟩) ((Step.flip a ka).child_subset v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma advance_bin {x : Word} {c : Charts x} {p : Price x} {a b : Wire c}
    {v : List (Wire c)} {t : ℕ} (hv : p.Valid t (wires v)) (ha : a ∈ v) (hb : b ∈ v)
    (d ka kb : Bool) :
    (p.advance v (.binary d a b ka kb)).Valid t (wires ((Step.binary d a b ka kb).after v)) := by
  let s := Step.binary d a b ka kb
  have hnext := guard_binary hv (Step.mem_wires.mpr ⟨a,ha,rfl⟩)
    (Step.mem_wires.mpr ⟨b,hb,rfl⟩) (s.child_subset v)
  have cost_le : cost p.basis.proj (wires v) p.basis.base s.out.w ≤
      (if freeAt p.basis v s.out.w then 0 else 1) := by
    cases h : freeAt p.basis v s.out.w
    · change cost _ _ _ _ ≤ 1
      unfold cost; split <;> omega
    · simp [cost,freeAt_sound h]
  refine ⟨hnext.1,fun k hk => ?_⟩
  exact (hnext.2 k hk).trans (Nat.add_le_add_left (Nat.add_le_add_left cost_le _) _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Step.Legal {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) (b t : ℕ) : Prop :=
  match s with
  | .flip a _ => a ∈ v ∧ 0<t
  | .binary _ a w _ _ => a ∈ v ∧ w ∈ v ∧ 0<b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Step.all_legal {x : Word} {c : Charts x} {s : Step c} {v : List (Wire c)} {b t : ℕ}
    (h : s ∈ Step.all b t v) : s.Legal v b t := by
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i ht
    rcases List.mem_cons.mp hu with rfl|hu
    · exact ⟨ha,by omega⟩
    · obtain rfl := List.mem_singleton.mp hu
      exact ⟨ha,by omega⟩
  · split at hb
    · contradiction
    rename_i hpos
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · obtain ⟨d,_,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,_,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,_,rfl⟩ := List.mem_map.mp h
      exact ⟨ha,hw,by omega⟩
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma advance_valid {x : Word} {c : Charts x} {p : Price x} {s : Step c}
    {v : List (Wire c)} {b t : ℕ} (hv : p.Valid t (wires v)) (h : s.Legal v b t) :
    (p.advance v s).Valid (s.budget b t).2 (wires (s.after v)) := by
  cases s with
  | flip a ka =>
    obtain ⟨hw,ht⟩ := h
    cases t with
    | zero => omega
    | succ t => exact advance_flip hv hw ka
  | binary d a w ka kb => exact advance_bin hv h.1 h.2.1 d ka kb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def loss {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) :=
  ((v.map Wire.w).filter (maskedConst f.mask)).length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma loss_le {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c))
    (nd : (v.map Wire.w).Nodup) : loss f v ≤ constants f.proj (wires v) := by
  rw [loss,←List.toFinset_card_of_nodup (nd.filter _)]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨hm,hc⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
  exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm,maskedConst_sound hc⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Price.cuts {x : Word} {c : Charts x} (p : Price x) (b : ℕ) (v : List (Wire c)) : Bool :=
  decide (b+p.spent < p.basis.lo+loss p.basis v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cut_sound {x : Word} {c : Charts x} {p : Price x} {b t : ℕ} {v : List (Wire c)}
    (nd : (v.map Wire.w).Nodup) (valid : p.Valid t (wires v)) (cut : p.cuts b v = true) :
    ¬ Exact x b t (wires v) := by
  rintro ⟨n,hn,j,hj,h⟩
  have g : Guard p.basis.proj x (wires v) p.basis.base j p.basis.lo p.spent :=
    ⟨valid.1,fun k hk => valid.2 k (weaken hk le_rfl hj (by rfl))⟩
  have e := guard_bound g h
  have l := loss_le p.basis v nd
  have q := of_decide_eq_true cut
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Step.child_nd {x : Word} {c : Charts x} {v : List (Wire c)} (s : Step c)
    (nd : (v.map Wire.w).Nodup) (hf : s.out.w ∉ wires v) :
    ((s.after v).map Wire.w).Nodup := by
  simp only [Step.after,List.map_cons,List.nodup_cons]
  have sub : List.Sublist (s.rest v) v := by cases s <;> exact List.filter_sublist
  exact ⟨fun hm => hf (List.mem_toFinset.mpr ((sub.map Wire.w).subset hm)),
    nd.sublist (sub.map Wire.w)⟩

abbrev Key := List ℕ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive Cache where
  | empty
  | bin (hash : ℕ) (bucket : List Key) (left right : Cache)

namespace Cache
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance : EmptyCollection Cache := ⟨empty⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hashKey (k : Key) := k.foldl (fun h n => Nat.mod (h*101+n) 65521) 7919
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def find (h : ℕ) : Cache → List Key
  | .empty => []
  | .bin n keys l r => if h=n then keys else if h<n then find h l else find h r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def put (h : ℕ) (k : Key) : Cache → Cache
  | .empty => .bin h [k] .empty .empty
  | .bin n keys l r => if h=n then .bin n (k::keys) l r
      else if h<n then .bin n keys (put h k l) r else .bin n keys l (put h k r)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def contains (db : Cache) (k : Key) := (find (hashKey k) db).contains k
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def insert (db : Cache) (k : Key) := put (hashKey k) k db
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Has (k : Key) : Cache → Prop
  | .empty => False
  | .bin _ keys l r => k ∈ keys ∨ Has k l ∨ Has k r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance : Membership Key Cache where mem db k := Has k db
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma find_mem {k : Key} (h : ℕ) (db : Cache) (m : k ∈ find h db) : k ∈ db := by
  induction db with
  | empty => contradiction
  | bin n keys l r il ir =>
    change k ∈ keys ∨ _ ∨ _
    simp only [find] at m
    split at m
    · exact Or.inl m
    split at m
    · exact Or.inr (Or.inl (il m))
    · exact Or.inr (Or.inr (ir m))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma contains_mem {k : Key} {db : Cache} (h : db.contains k) : k ∈ db :=
  find_mem _ _ (List.contains_iff_mem.mp h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mem_put {k v : Key} (h : ℕ) (db : Cache) (m : v ∈ put h k db) : v=k ∨ v ∈ db := by
  induction db with
  | empty =>
    change v ∈ [k] ∨ False ∨ False at m
    exact Or.inl (by simpa using m)
  | bin n keys l r il ir =>
    simp only [put] at m
    split at m
    · change v ∈ k::keys ∨ Has v l ∨ Has v r at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      simp only [List.mem_cons] at m
      tauto
    split at m
    · change v ∈ keys ∨ Has v (put h k l) ∨ Has v r at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      rcases m with a|m|a
      · tauto
      · rcases il m with e|e <;> tauto
      · tauto
    · change v ∈ keys ∨ Has v l ∨ Has v (put h k r) at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      rcases m with a|a|m
      · tauto
      · tauto
      · rcases ir m with e|e <;> tauto
end Cache

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sortNats : List ℕ → List ℕ
  | [] => []
  | a::xs => ordered a (sortNats xs)
where ordered (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b::ys => if a≤b then a::b::ys else b::ordered a ys

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sort_perm (x : List ℕ) : (sortNats x).Perm x := by
  have helper (a : ℕ) (xs : List ℕ) : (sortNats.ordered a xs).Perm (a::xs) := by
    induction xs with
    | nil => exact .refl _
    | cons b ys ih =>
      simp only [sortNats.ordered]
      split
      · exact .refl _
      · exact (List.Perm.cons b ih).trans (List.Perm.swap ..)
  induction x with
  | nil => exact .refl _
  | cons a xs ih => exact (helper a _).trans (List.Perm.cons a ih)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sorted {x : Word} {c : Charts x} (v : List (Wire c)) : List ℕ :=
  sortNats (v.map fun a => a.w.toNat)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def key {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) : Key :=
  b :: t :: sorted v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Safe (x : Word) (db : Cache) :=
  ∀ b t ws, b::t::ws ∈ db → ¬ Exact x b t (ws.map (BitVec.ofNat 512)).toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma key_set {x : Word} {c : Charts x} (v : List (Wire c)) :
    ((sorted v).map (BitVec.ofNat 512)).toFinset = wires v := by
  have perm := (sort_perm (v.map (fun a => a.w.toNat))).map
    (BitVec.ofNat 512)
  ext a
  rw [List.mem_toFinset]
  unfold sorted
  rw [perm.mem_iff]
  simp [wires,Function.comp_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma safe_insert {x : Word} {c : Charts x} {b t : ℕ} {v : List (Wire c)} {db : Cache}
    (hd : Safe x db) (h : ¬Exact x b t (wires v)) : Safe x (db.insert (key b t v)) := by
  intro b' t' ws hk
  rcases Cache.mem_put _ _ hk with e|hm
  · have eq : key b t v = b'::t'::ws := e.symm
    obtain ⟨rfl,rfl,rfl⟩ := (by simpa only [key,List.cons.injEq] using eq :
      b=b' ∧ t=t' ∧ sorted v=ws)
    rw [key_set]; exact h
  · exact hd _ _ _ hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def batch {α : Type} (run : α → Cache → Option Cache) : List α → Cache → Option Cache
  | [], db => some db
  | a::xs, db => (run a db).bind (batch run xs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma batch_sound {α : Type} {x : Word} {Q : α → Prop} {run : α → Cache → Option Cache}
    (xs : List α) {db out : Cache} (legal : ∀ a ∈ xs, ∀ d e, Safe x d → run a d = some e →
      Safe x e ∧ Q a) (sd : Safe x db) (done : batch run xs db = some out) :
      Safe x out ∧ ∀ a ∈ xs, Q a := by
  induction xs generalizing db with
  | nil => exact ⟨(Option.some.inj done) ▸ sd,by simp⟩
  | cons a xs ih =>
    simp only [batch] at done
    cases ha : run a db with
    | none => simp [ha] at done
    | some e =>
      have hh := legal a (by simp) db e sd ha
      have hr := ih (fun z hz => legal z (by simp [hz])) hh.1 (by simpa [ha] using done)
      exact ⟨hr.1,fun z hz => (List.mem_cons.mp hz).elim (fun eq => eq ▸ hh.2) (hr.2 z)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def isEligible {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) : Bool :=
  s.out.w != 0 && s.out.w != top && !(v.any fun a => a.w == s.out.w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma eligible_iff {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    isEligible s v = true ↔ eligible v s := by
  simp only [isEligible,eligible,proper,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',
    List.any_eq_false,beq_iff_eq,Step.mem_wires,not_exists,not_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def immediate {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) (ps : List (Price x)) :
    Bool := decide (b+1 < v.length) || cover t v != top || ps.any (fun p => p.cuts b v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma immediate_sound {x : Word} {c : Charts x} {b t} {v : List (Wire c)} {ps}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v))
    (h : immediate b t v ps = true) : ¬Exact x b t (wires v) := by
  intro he
  rcases Bool.or_eq_true_iff.mp h with h|h
  · rcases Bool.or_eq_true_iff.mp h with hs|hc
    · have hsz := exact_size he
      have ec := List.toFinset_card_of_nodup nd
      rw [List.length_map] at ec
      change (v.map Wire.w).toFinset.card ≤ b+1 at hsz
      have hh := of_decide_eq_true hs
      omega
    · simp [exact_cover c v he] at hc
  · obtain ⟨p,hp,cut⟩ := List.any_eq_true.mp h
    exact cut_sound nd (valid p hp) cut he

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def close {x : Word} (c : Charts x) : ℕ → ℕ → ℕ → List (Wire c) → List (Price x) →
    Cache → Option Cache
  | 0,_,_,_,_,_ => none
  | fuel+1,b,t,v,ps,db =>
    if immediate b t v ps then some db
    else
      let k := key b t v
      if db.contains k then some db
      else if v.any (fun a => a.w == x) then none
      else
        let act := fun s e =>
          if isEligible s v then
            close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v)
              (ps.map (fun p => p.advance v s)) e
          else some e
        (batch act (Step.all b t v) db).map (fun e => e.insert k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma close_sound {x : Word} (c : Charts x) (hx : proper x) (fuel : ℕ) {b t}
    {v : List (Wire c)} {ps} {db out : Cache}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v)) (safe : Safe x db)
    (done : close c fuel b t v ps db = some out) : Safe x out ∧ ¬Exact x b t (wires v) := by
  induction fuel generalizing b t v ps db out with
  | zero => contradiction
  | succ fuel ih =>
    simp only [close] at done
    split at done
    · rename_i h
      obtain rfl := Option.some.inj done
      exact ⟨safe, immediate_sound nd valid h⟩
    split at done
    · rename_i h
      obtain rfl := Option.some.inj done
      have e := safe b t (sorted v) (Cache.contains_mem h)
      rw [key_set] at e; exact ⟨safe,e⟩
    split at done
    · contradiction
    rename_i nx
    have nox : x ∉ wires v := by
      rintro hm
      obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      exact nx (List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩)
    let act := fun (s : Step c) (e : Cache) =>
      if isEligible s v then
        close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v)
          (ps.map (fun p => p.advance v s)) e
      else some e
    change (batch act (Step.all b t v) db).map (fun e => e.insert (key b t v)) = some out at done
    cases hb : batch act (Step.all b t v) db with
    | none => simp [hb] at done
    | some e =>
      have outEq : e.insert (key b t v) = out := by simpa only [hb,Option.map_some,
        Option.some.injEq] using done
      obtain ⟨se,branches⟩ := batch_sound (Q:=fun s => eligible v s →
        ¬Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)))
        (Step.all b t v) (run:=act) (db:=db) (out:=e) (by
          intro s hs d o sd sol
          by_cases he : isEligible s v = true
          · have h := (eligible_iff s v).1 he
            have sol' : close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v) (ps.map (fun p => p.advance v s)) d = some o := by simpa [act,he] using sol
            have h' := ih (s.child_nd nd h.2) (by
              intro p hp
              obtain ⟨orig,hm,rfl⟩ := List.mem_map.mp hp
              exact advance_valid (valid _ hm) (Step.all_legal hs)) sd sol'
            exact ⟨h'.1,fun _ => h'.2⟩
          · have outEq : d=o := by simpa [act,he] using sol
            exact ⟨outEq ▸ sd,fun el => False.elim (he ((eligible_iff s v).2 el))⟩) safe hb
      have impossible : ¬Exact x b t (wires v) := by
        intro hypothetical
        rcases (descend c hx hypothetical).resolve_left nox with ⟨s,hs,el,h⟩
        exact branches s hs el h
      exact ⟨outEq ▸ safe_insert se impossible,impossible⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma price_subset {x : Word} {p : Price x} {t : ℕ} {S T : Finset Word}
    (h : p.Valid t S) (sub : T ⊆ S) : p.Valid t T := by
  refine ⟨h.1, fun b hb => h.2 b (weaken hb le_rfl le_rfl ?_)⟩
  exact Finset.union_subset_union_left (Finset.image_subset_image sub)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def validate {x : Word} (c : Charts x) (b t : ℕ) (v : List (Wire c)) (ps : List (Price x)) :=
  (batch (fun u db => close c (b+t+2) b t u ps db) v.sublists ∅).isSome

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verified {x : Word} (c : Charts x) (hx : proper x) {b t} {v : List (Wire c)} {ps}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v))
    (check : validate c b t v ps = true) : ¬Feasible x b t (wires v) := by
  obtain ⟨out,done⟩ := Option.isSome_iff_exists.mp check
  have sf : Safe x ∅ := by intro b' t' ws h; exact False.elim h
  obtain ⟨_,no⟩ := batch_sound (Q:=fun u => ¬Exact x b t (wires u)) v.sublists
    (run:=fun u db => close c (b+t+2) b t u ps db) (db:=∅) (out:=out) (by
      intro u hu d e sd hh
      have sub := List.mem_sublists.mp hu
      have incl : wires u ⊆ wires v := by
        intro a ha; exact List.mem_toFinset.mpr ((sub.map Wire.w).subset (List.mem_toFinset.mp ha))
      exact close_sound c hx _ (nd.sublist (sub.map Wire.w))
        (fun p hp => price_subset (valid p hp) incl) sd hh) sf done
  rintro ⟨i,hi,j,hj,T,sub,hL⟩
  let u := v.filter (fun a => decide (a.w ∈ T))
  have eq : wires u = T := by
    ext a; rw [Step.mem_wires]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact of_decide_eq_true (List.mem_filter.mp hw).2
    · intro ha
      obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
      exact ⟨w,List.mem_filter.mpr ⟨hw,by simpa [e] using ha⟩,e⟩
  apply no u (List.mem_sublists.mpr List.filter_sublist)
  rw [eq]; exact ⟨i,hi,j,hj,hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def unpack (code : ℕ) (i : Fin 512) : Fin 512 := Fin.ofNat 512 (code >>> (9*i.val))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def basisFor (x : Word) (m : Word) (raw : List Word) (lo : ℕ) (row : Fin 512 → Fin 512)
    (good : ∀ i, bit m (row i) = true) : Basis x where
  mask := m
  raw := raw
  lo := lo
  proj := faceQ row
  zero := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ row).q 0) ⟨r,hr⟩ = bit 0 ⟨r,hr⟩
    rw [q_bit,bit_zero,bit_zero]
  one := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ row).q top) ⟨r,hr⟩ = bit top ⟨r,hr⟩
    rw [q_bit,bit_top,bit_top]
  refl a b e := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    let i : Fin 512 := ⟨r,hr⟩
    change bit ((faceQ row).q a) i = bit ((faceQ row).q b) i
    rw [q_bit,q_bit]
    have he := congrArg (fun w => bit w (row i)) e
    change bit (combine false a m) (row i) = bit (combine false b m) (row i) at he
    simpa only [bit_bin,Bool.false_eq_true,ite_false,good,Bool.and_true] using he

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initial_price {x y : Word} {f : Basis x} {S child : Finset Word}
    (hy : proper y) (forbidden : ¬Feasible y (f.lo-1) 1 child) (ex : f.proj.q x = y)
    (inc : available f.proj S f.base ⊆ insert 0 child) :
    (Price.mk f 0).Valid 1 S := by
  refine ⟨ex ▸ hy, ?_⟩
  intro b h
  by_contra fail
  have bl : b ≤ f.lo-1 := by change ¬f.lo ≤ b+0 at fail; omega
  rw [ex] at h
  apply forbidden
  exact ignore hy (weaken h bl le_rfl inc) (Or.inr fun hp => hp.1 rfl)

-- Replay short gate sequences and certify the search in bounded-depth pieces.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def vanished (keep : Bool) (a : Word) : Finset Word := if keep then ∅ else {a}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def debit (keep : Bool) := if keep then 0 else 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma vanishes (keep : Bool) (a : Word) : (vanished keep a).card = debit keep := by
  cases keep <;> simp [vanished,debit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Step.discard {x : Word} {c : Charts x} : Step c → Finset Word
  | .flip a ka => vanished ka a.w
  | .binary _ a w ka kb => vanished ka a.w ∪ vanished kb w.w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Step.drops {x : Word} {c : Charts x} : Step c → ℕ
  | .flip _ ka => debit ka
  | .binary _ _ _ ka kb => debit ka + debit kb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma discard_le {x : Word} {c : Charts x} (s : Step c) : s.discard.card ≤ s.drops := by
  cases s with
  | flip a ka => exact (vanishes ka a.w).le
  | binary d a b ka kb =>
    exact (Finset.card_union_le ..).trans (by simp only [Step.drops,vanishes,le_refl])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rest_inclusion {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    wires v ⊆ wires (s.rest v) ∪ s.discard := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  by_cases keepW : w ∈ s.rest v
  · exact Finset.mem_union_left _ (Step.mem_wires.mpr ⟨w,keepW,rfl⟩)
  · apply Finset.mem_union_right
    cases s with
    | flip a ka =>
      cases ka <;> simp_all [Step.discard,Step.rest,vanished,List.mem_filter]
    | binary d a b ka kb =>
      cases ka <;> cases kb <;> simp_all [Step.discard,Step.rest,vanished,List.mem_filter]
      all_goals tauto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fits_step {x : Word} {c : Charts x} {b t} (v : List (Wire c)) (s : Step c)
    (nd : (v.map Wire.w).Nodup) (el : eligible v s) (h : Exact x (s.budget b t).1
      (s.budget b t).2 (wires (s.after v))) :
    v.length+1 ≤ (s.budget b t).1+1+s.drops := by
  have le₁ := Finset.card_le_card (rest_inclusion s v)
  have le₂ := Finset.card_union_le (wires (s.rest v)) s.discard
  have le₃ := discard_le s
  have le₄ := exact_size h
  have eq : (wires v).card = v.length := by simpa [wires] using List.toFinset_card_of_nodup nd
  have fresh : s.out.w ∉ wires (s.rest v) := by
    intro hm
    obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
    have mem : w ∈ v := by cases s <;> exact List.mem_of_mem_filter hw
    exact el.2 (Step.mem_wires.mpr ⟨w,mem,e⟩)
  have ee : (wires (s.after v)).card = (wires (s.rest v)).card + 1 := by
    simpa only [wires,Step.after,List.map_cons,List.toFinset_cons] using
      Finset.card_insert_of_notMem fresh
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Step.anyBad {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) (test : Step c → Bool) :=
  v.all (fun a =>
    ((t==0) || (test (.flip a false) && test (.flip a true))) &&
    ((b==0) || v.all (fun w =>
      !(decide (a.w.toNat < w.w.toNat)) ||
      [false,true].all (fun d => [false,true].all (fun ka =>
        test (.binary d a w ka false) && test (.binary d a w ka true))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma checked_steps {x : Word} {c : Charts x} {b t} {v : List (Wire c)} {test : Step c → Bool}
    (h : Step.anyBad b t v test=true) {s} (hs : s ∈ Step.all b t v) : test s=true := by
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hs
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i ht
    have q := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hh.1).resolve_left
      (by simpa only [beq_iff_eq] using ht))
    rcases List.mem_cons.mp hu with rfl|hu
    · exact q.1
    · obtain rfl := List.mem_singleton.mp hu; exact q.2
  · split at hb
    · contradiction
    rename_i hbPos
    have q := (Bool.or_eq_true_iff.mp hh.2).resolve_left (by simpa only [beq_iff_eq] using hbPos)
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · rename_i lt
      have gate := (Bool.or_eq_true_iff.mp (List.all_eq_true.mp q w hw)).resolve_left (by simp [lt])
      obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,hka,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp h
      have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp gate d hd) ka hka)
      cases kb
      · exact both.1
      · exact both.2
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Frame {x : Word} (c : Charts x) where
  b : ℕ
  t : ℕ
  v : List (Wire c)
  ps : List (Price x)

namespace Frame
variable {x : Word} {c : Charts x}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Valid (f : Frame c) := (f.v.map Wire.w).Nodup ∧ ∀ p ∈ f.ps, p.Valid f.t (wires f.v)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def No (f : Frame c) := ¬Exact x f.b f.t (wires f.v)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def code (f : Frame c) := key f.b f.t f.v
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def child (f : Frame c) (s : Step c) : Frame c :=
  ⟨(s.budget f.b f.t).1,(s.budget f.b f.t).2,s.after f.v,f.ps.map (fun p => p.advance f.v s)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma child_valid {f : Frame c} (h : f.Valid) {s} (ok : eligible f.v s)
    (legal : s.Legal f.v f.b f.t) : (f.child s).Valid := by
  refine ⟨s.child_nd h.1 ok.2,?_⟩
  intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact advance_valid (h.2 q hq) legal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma transfer {f g : Frame c} (eq : f.code = g.code) (h : f.No) : g.No := by
  obtain ⟨b,t,s⟩ := (by simpa only [code,key,List.cons.injEq] using eq :
    f.b=g.b ∧ f.t=g.t ∧ sorted f.v=sorted g.v)
  have e : wires f.v=wires g.v := by rw [←key_set f.v,←key_set g.v,s]
  unfold No at *
  rwa [←b,←t,←e]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def decoded (f : Frame c) (j : ℕ) : Option (Step c) :=
  if j < 32 then
    if f.t = 0 then none else
      (f.v[j/2]?).map (fun a => .flip a (Nat.mod j 2 == 1))
  else if f.b = 0 then none else
    let i := j-32
    (f.v[i/128]?).bind fun a =>
      (f.v[Nat.mod (i/8) 16]?).map fun w => .binary (Nat.mod (i/4) 2 == 1) a w
        (Nat.mod (i/2) 2 == 1) (Nat.mod i 2 == 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma decode_legal {f : Frame c} {j : ℕ} {s : Step c} (h : f.decoded j = some s) :
    s.Legal f.v f.b f.t := by
  unfold decoded at h
  split at h
  · split at h
    · contradiction
    rename_i ht
    cases e : f.v[j/2]? with
    | none => simp [e] at h
    | some a =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst s; exact ⟨List.mem_of_getElem? e,by omega⟩
  · split at h
    · contradiction
    rename_i hb
    let i := j-32
    change ((f.v[i/128]?).bind _)=some s at h
    cases e : f.v[i/128]? with
    | none => simp [e] at h
    | some a =>
      simp only [e,Option.bind_some] at h
      cases ew : f.v[Nat.mod (i/8) 16]? with
      | none => simp [i] at ew; simp [ew] at h
      | some w =>
        change Option.map _ (f.v[Nat.mod (i/8) 16]?) = some s at h
        simp only [ew,Option.map_some,Option.some.injEq] at h
        subst s; exact ⟨List.mem_of_getElem? e,List.mem_of_getElem? ew,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def jump (f : Frame c) (j : ℕ) : Option (Frame c) :=
  (f.decoded j).bind (fun s => if isEligible s f.v then some (f.child s) else none)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma jump_valid {f g : Frame c} {j : ℕ} (h : f.Valid) (eq : f.jump j=some g) : g.Valid := by
  unfold jump at eq
  cases e : f.decoded j with
  | none => simp [e] at eq
  | some s =>
    simp only [e,Option.bind_some] at eq
    split at eq
    · rename_i eligibleS
      obtain rfl := Option.some.inj eq
      exact child_valid h ((eligible_iff ..).1 eligibleS) (decode_legal e)
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def replay (f : Frame c) : ℕ → ℕ → Option (Frame c)
  | 0,_ => some f
  | d+1,tape => (f.replay d (tape / 4096)).bind fun g => g.jump (Nat.mod tape 4096-1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma replay_valid {f g : Frame c} {d tape : ℕ} (h : f.Valid)
    (eq : f.replay d tape = some g) : g.Valid := by
  induction d generalizing tape g with
  | zero => exact (Option.some.inj eq) ▸ h
  | succ d ih =>
    unfold replay at eq
    cases e : f.replay d (tape/4096) with
    | none => simp [e] at eq
    | some g' =>
      exact jump_valid (ih e) (by simpa only [e,Option.bind_some] using eq)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def check (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => immediate f.b f.t f.v f.ps || known f
  | d+1,f =>
    immediate f.b f.t f.v f.ps ||
      (!(f.v.any (fun a => a.w == x)) &&
        Step.anyBad f.b f.t f.v (fun s =>
          decide ((s.budget f.b f.t).1+1+s.drops < f.v.length+1) || !(isEligible s f.v) || check known d (f.child s)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma check_sound (known : Frame c → Bool) (good : ∀ f, known f = true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (v : f.Valid) (h : check known d f=true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp h with hi|hk
    · exact immediate_sound v.1 v.2 hi
    · exact good f hk
  | succ d ih =>
    rcases Bool.or_eq_true_iff.mp h with hi|hs
    · exact immediate_sound v.1 v.2 hi
    obtain ⟨no,all⟩ := Bool.and_eq_true_iff.mp hs
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · have chk := checked_steps all hs
      have fits := fits_step f.v s v.1 el ht
      simp only [show ¬ ((s.budget f.b f.t).1+1+s.drops < f.v.length+1) by omega,
        decide_false,Bool.false_or,(eligible_iff ..).2 el,Bool.not_true] at chk
      exact ih (child_valid v el (Step.all_legal hs)) chk ht
end Frame

abbrev Table := Array ℕ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lowerIndex (a : Table) (h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,l,_ => l
  | fuel+1,l,r =>
    if l<r then
      let m := (l+r)/2
      if Nat.mod a[m]! 65521 < h then lowerIndex a h fuel (m+1) r
        else lowerIndex a h fuel l m
    else l

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def TableSound {x : Word} {c : Charts x} (root : Frame c) (depth : ℕ) (a : Table) :=
  ∀ (j w : ℕ), a[j]?=some w → ∀ f, root.replay depth (w/65521) = some f → f.No

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hitRow {x : Word} {c : Charts x} (root : Frame c) (depth h : ℕ) (k : Key) : Option ℕ → Bool
  | none => false
  | some w =>
    Nat.mod w 65521 == h && (root.replay depth (w/65521)).any (fun g => g.code == k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lookup {x : Word} {c : Charts x} (root : Frame c) (depth : ℕ) (a : Table) (f : Frame c) :=
  let k := f.code
  let h := Cache.hashKey k
  let j := lowerIndex a h 20 0 a.size
  [0,1,2,3,4,5].any (fun n => hitRow root depth h k (a[j+n]?))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lookup_sound {x : Word} {c : Charts x} {root : Frame c} {depth} {a : Table}
    (sound : TableSound root depth a) (f : Frame c) (ok : lookup root depth a f = true) :
    f.No := by
  let k := f.code
  let h := Cache.hashKey k
  let j := lowerIndex a h 20 0 a.size
  obtain ⟨n,_,eh⟩ := List.any_eq_true.mp ok
  change hitRow root depth h k (a[j+n]?) = true at eh
  cases e : a[j+n]? with
  | none => simp [e,hitRow] at eh
  | some w =>
    have pair := Bool.and_eq_true_iff.mp (by simpa only [e,hitRow] using eh :
      Nat.mod w 65521 == h && (root.replay depth (w/65521)).any (fun g => g.code == k))
    cases eq : root.replay depth (w/65521) with
    | none => simp [eq] at pair
    | some g =>
      have hkey : g.code=k := by simpa [eq] using pair.2
      exact Frame.transfer hkey (sound (j+n) w e g eq)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tableRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (Frame.check known hops))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Span (p : ℕ → Bool) (lo hi : ℕ) := ∀ j, lo ≤ j → j < hi → p j=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sampleSpan (p : ℕ → Bool) (lo n : ℕ) := (List.range n).all (fun i => p (lo+i))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma checked_span {p : ℕ → Bool} {lo n : ℕ} (h : sampleSpan p lo n = true) : Span p lo (lo+n) := by
  intro j hj htop
  have q := List.all_eq_true.mp h (j-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le hj] using q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma join_span {p : ℕ → Bool} {lo mid hi : ℕ} (h : Span p lo mid) (k : Span p mid hi) :
    Span p lo hi := by
  intro j hj ht
  by_cases e : j < mid
  · exact h j hj e
  · exact k j (by omega) ht
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma certified_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (a : Table) {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (h : Span (tableRow root d a known hops) 0 a.size) : TableSound root d a := by
  intro j w ew f ef
  have hj := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
  have e : Frame.check known hops f=true := by simpa only [tableRow,ew,Option.all_some,ef] using hj
  exact Frame.check_sound known sk hx hops (Frame.replay_valid vr ef) e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def checkSubsets {x : Word} {c : Charts x} (root : Frame c) (known : Frame c → Bool) (hops : ℕ) :=
  root.v.sublists.all (fun u => Frame.check known hops {root with v:=u})

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma checked_root {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (ok : checkSubsets root known hops=true) :
    ¬Feasible x root.b root.t (wires root.v) := by
  rintro ⟨i,hi,j,hj,T,sub,hL⟩
  let u := root.v.filter (fun a => decide (a.w ∈ T))
  have eq : wires u=T := by
    ext a; rw [Step.mem_wires]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact of_decide_eq_true (List.mem_filter.mp hw).2
    · intro ha; obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
      exact ⟨w,List.mem_filter.mpr ⟨hw,by simpa [e] using ha⟩,e⟩
  have hchk := List.all_eq_true.mp ok u (List.mem_sublists.mpr List.filter_sublist)
  have q : ({root with v:=u} : Frame c).Valid := ⟨vr.1.sublist (List.filter_sublist.map _), fun p hp =>
    price_subset (vr.2 p hp) (eq ▸ sub)⟩
  have no := Frame.check_sound known sk hx hops q hchk
  apply no
  change Exact x root.b root.t (wires u); rw [eq]
  exact ⟨i,hi,j,hj,hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma check_block {p : ℕ → Bool} {lo hi : ℕ} (h : sampleSpan p lo (hi-lo)=true) :
    Span p lo hi := by
  intro j hj htop
  exact checked_span h j hj (by omega)

-- Share positive and negative sample masks between related gate choices.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def keepList {α : Type} (k : Bool) (a : α) := if k then [a] else []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def addSep (k : Bool) (a r : Word) := if k then a ||| r else r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_keep {x : Word} {c : Charts x} (t : ℕ) (a : Wire c) (k : Bool)
    (tail : List (Wire c)) :
    cover t (keepList k a ++ tail)=addSep k (a.sep t) (cover t tail) := by
  cases k <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma preserve_cover {x : Word} {c : Charts x} {b t} {S : Finset Word} (v : List (Wire c))
    (h : Exact x b t S) (sub : S ⊆ wires v) : cover t v=top := by
  obtain ⟨n,_,j,hj,h⟩ := h
  apply BitVec.eq_of_getElem_eq; intro k hk
  let i : Fin 512 := ⟨k,hk⟩
  change bit (cover t v) i=bit top i
  rw [bit_top,cover_bit]
  obtain ⟨a,ha,hd⟩ := distinguishes_live h (c.hp i) (c.hn i)
  obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
  exact ⟨w,hw,e ▸ distinguish_more hd hj⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def alone {x : Word} {c : Charts x} (a : Wire c) (v : List (Wire c)) :=
  v.filter (fun w => w.w != a.w)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def aside {x : Word} {c : Charts x} (a b : Wire c) (v : List (Wire c)) :=
  v.filter (fun w => w.w != a.w && w.w != b.w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_unary {x : Word} {c : Charts x} {n t} {a : Wire c} {v : List (Wire c)} (k : Bool)
    (h : Exact x n t (wires ((Step.flip a k).after v))) :
    a.flip.sep t ||| addSep k (a.sep t) (cover t (alone a v))=top := by
  let v' := a.flip :: (keepList k a ++ alone a v)
  have hv : cover t v'=top := preserve_cover v' h (by
    intro z hz; obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp hz
    rcases List.mem_cons.mp hw with rfl|hw
    · exact Step.mem_wires.mpr ⟨_,List.mem_cons_self,rfl⟩
    obtain ⟨wm,ok⟩ := List.mem_filter.mp hw
    by_cases e : w.w=a.w
    · cases k
      · simp [e] at ok
      · exact Step.mem_wires.mpr ⟨a,by simp [v',keepList],e.symm⟩
    · exact Step.mem_wires.mpr ⟨w,List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_filter.mpr ⟨wm,by simp [e]⟩)),rfl⟩)
  simpa only [v',cover,cover_keep] using hv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_binary {x : Word} {c : Charts x} {n t} {a b : Wire c} {v : List (Wire c)}
    (d ka kb : Bool) (h : Exact x n t (wires ((Step.binary d a b ka kb).after v))) :
    (a.binary d b).sep t ||| addSep ka (a.sep t) (addSep kb (b.sep t) (cover t (aside a b v)))=top := by
  let v' := a.binary d b :: (keepList ka a ++ (keepList kb b ++ aside a b v))
  have hv : cover t v'=top := preserve_cover v' h (by
    intro z hz; obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp hz
    rcases List.mem_cons.mp hw with rfl|hw
    · exact Step.mem_wires.mpr ⟨_,List.mem_cons_self,rfl⟩
    obtain ⟨wm,ok⟩ := List.mem_filter.mp hw
    obtain ⟨okA,okB⟩ := Bool.and_eq_true_iff.mp ok
    by_cases ea : w.w=a.w
    · cases ka
      · simp [ea] at okA
      · exact Step.mem_wires.mpr ⟨a,by simp [v',keepList],ea.symm⟩
    by_cases eb : w.w=b.w
    · cases kb
      · simp [eb] at okB
      · exact Step.mem_wires.mpr ⟨b,by simp [v',keepList],eb.symm⟩
    exact Step.mem_wires.mpr ⟨w,List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_filter.mpr ⟨wm,by simp [ea,eb]⟩))),rfl⟩)
  simpa only [v',cover,cover_keep] using hv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def scan {x : Word} {c : Charts x} (f : Frame c) (next : Frame c → Bool) :=
  let len := f.v.length
  let test := fun (s : Step c) (budget : ℕ) (bits : Word) =>
    decide (budget+1+s.drops < len+1) || bits != top || !isEligible s f.v || next (f.child s)
  f.v.all (fun a =>
    ((f.t==0) ||
      (let t := f.t-1
       let r := cover t (alone a f.v)
       let g := a.flip.sep t
       test (.flip a false) f.b (g ||| r) && test (.flip a true) f.b (g ||| (a.sep t ||| r)))) &&
    ((f.b==0) || f.v.all (fun w => !(decide (a.w.toNat < w.w.toNat)) ||
      (let r := cover f.t (aside a w f.v)
       let wa := a.sep f.t
       let wb := w.sep f.t
       [false,true].all (fun d =>
         let g := (a.binary d w).sep f.t
         [false,true].all (fun ka => [false,true].all (fun kb =>
           test (.binary d a w ka kb) (f.b-1) (g ||| addSep ka wa (addSep kb wb r)))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Fast {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => immediate f.b f.t f.v f.ps || known f
  | k+1,f => immediate f.b f.t f.v f.ps ||
      (!(f.v.any (fun a => a.w == x)) && scan f (Fast known k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma scan_sound {x : Word} {c : Charts x} {f : Frame c} {s : Step c} {next : Frame c → Bool}
    (h : scan f next = true) (nd : (f.v.map Wire.w).Nodup)
    (hs : s ∈ Step.all f.b f.t f.v) (el : eligible f.v s)
    (ht : Exact x (s.budget f.b f.t).1 (s.budget f.b f.t).2 (wires (s.after f.v))) :
    next (f.child s)=true := by
  have fit := fits_step f.v s nd el ht
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hs
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i tpos
    have q := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hh.1).resolve_left
      (by simpa only [beq_iff_eq] using tpos))
    rcases List.mem_cons.mp hu with rfl|hu
    · have eq := cover_unary false ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,Bool.false_eq_true,ite_false] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.1
    · obtain rfl := List.mem_singleton.mp hu
      have eq := cover_unary true ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,ite_true] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.2
  · split at hb
    · contradiction
    rename_i bpos
    have q := (Bool.or_eq_true_iff.mp hh.2).resolve_left (by simpa only [beq_iff_eq] using bpos)
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · rename_i lt
      have gate := (Bool.or_eq_true_iff.mp (List.all_eq_true.mp q w hw)).resolve_left (by simp [lt])
      obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,hka,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp h
      have val := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp gate d hd) ka hka) kb hkb
      have eq := cover_binary d ka kb ht
      simp only [Step.budget] at eq
      change f.v.length+1 ≤ f.b-1+1+_ at fit
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using val
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : Fast known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact immediate_sound valid.1 valid.2 h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact immediate_sound valid.1 valid.2 h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def fastRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (Fast known hops))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (a : Table) {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (h : Span (fastRow root d a known hops) 0 a.size) : TableSound root d a := by
  intro j w ew f ef
  have hj := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
  have e : Fast known hops f=true := by simpa only [fastRow,ew,Option.all_some,ef] using hj
  exact fast_sound known sk hx hops (Frame.replay_valid vr ef) e

-- Relabel truth-table rows along graph automorphisms.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Automorphism (x : Word) where
  p : Projection
  zero : p.q 0=0
  one : p.q top=top
  inj : Function.Injective p.q
  fix : p.q x=x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def autoFor (x : Word) (f g : Fin 512 → Fin 512) (rightInv : ∀ i, f (g i)=i)
    (fixed : (faceQ f).q x=x) : Automorphism x where
  p := faceQ f
  zero := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ f).q 0) ⟨r,hr⟩ = bit 0 ⟨r,hr⟩; rw [q_bit,bit_zero,bit_zero]
  one := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ f).q top) ⟨r,hr⟩ = bit top ⟨r,hr⟩; rw [q_bit,bit_top,bit_top]
  inj := by
    intro a b h
    apply BitVec.eq_of_getElem_eq; intro r hr
    let i : Fin 512 := ⟨r,hr⟩
    have e := congrArg (fun w => bit w (g i)) h
    change bit a i=bit b i
    simpa only [q_bit,rightInv] using e
  fix := fixed

namespace Automorphism
variable {x : Word}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma maps_proper (R : Automorphism x) {a} (h : proper a) : proper (R.p.q a) := by
  constructor
  · exact fun e => h.1 (R.inj (e.trans R.zero.symm))
  · exact fun e => h.2 (R.inj (e.trans R.one.symm))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma map_live (R : Automorphism x) {b t S} (h : Live x b t S) :
    Live x b t (S.image R.p.q) := by
  induction h with
  | done => simpa only [Finset.image_singleton,R.fix] using (Live.done (target:=x))
  | @unary b t U a pa fresh tail ih =>
    rw [Finset.image_insert]
    rw [Finset.image_insert,R.p.neg] at ih
    apply Live.unary (R.maps_proper pa) _ ih
    rw [←R.p.neg,←Finset.image_insert]
    intro hm
    obtain ⟨y,hy,e⟩ := Finset.mem_image.mp hm
    exact fresh ((R.inj e) ▸ hy)
  | @binary b t U a w d pa pw ne fresh tail ih =>
    rw [Finset.image_insert,Finset.image_insert]
    rw [Finset.image_insert,R.p.bin] at ih
    apply Live.binary (d:=d) (R.maps_proper pa) (R.maps_proper pw) (fun e => ne (R.inj e)) _ ih
    rw [←R.p.bin,←Finset.image_insert,←Finset.image_insert]
    intro hm
    obtain ⟨y,hy,e⟩ := Finset.mem_image.mp hm
    exact fresh ((R.inj e) ▸ hy)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma map_exact (R : Automorphism x) {b t S} (h : Exact x b t S) :
    Exact x b t (S.image R.p.q) := by
  obtain ⟨n,hn,j,hj,hl⟩ := h
  exact ⟨n,hn,j,hj,R.map_live hl⟩
end Automorphism

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bareStep (v : List Word) (j : ℕ) : List Word :=
  if j < 32 then
    let a := v.getD (j/2) 0
    ~~~a :: v.filter (fun u => (Nat.mod j 2 == 1) || u != a)
  else
    let i := j-32
    let a := v.getD (i/128) 0
    let b := v.getD (Nat.mod (i/8) 16) 0
    combine (Nat.mod (i/4) 2 == 1) a b :: v.filter (fun u =>
      ((Nat.mod (i/2) 2 == 1) || u != a) && ((Nat.mod i 2 == 1) || u != b))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bareReplay (v : List Word) : ℕ → ℕ → List Word
  | 0,_ => v
  | d+1,tape => bareStep (bareReplay v d (tape/4096)) (Nat.mod tape 4096-1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma filt_map {α β : Type} (f : α→β) (p : α→Bool) (q : β→Bool) (ok : ∀ a, q (f a)=p a)
    (v : List α) : (v.map f).filter q = (v.filter p).map f := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.map_cons,List.filter_cons,ok]
    cases p a <;> simp [ih]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mapped_get {α β : Type} (f : α→β) (a : α) (v : List α) (i : ℕ) :
    (v.map f).getD i (f a)=f (v.getD i a) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases v[i]? <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma project_step {x : Word} (R : Automorphism x) (v : List Word) (j : ℕ) :
    bareStep (v.map R.p.q) j=(bareStep v j).map R.p.q := by
  have bne (a b : Word) : (R.p.q a != R.p.q b) = (a != b) := by
    apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne]; exact not_congr R.inj.eq_iff
  have get (i : ℕ) : (v.map R.p.q).getD i 0 = R.p.q (v.getD i 0) := by
    simpa only [R.zero] using mapped_get R.p.q 0 v i
  by_cases small : j < 32
  · simp only [bareStep,small,ite_true,get,List.map_cons,R.p.neg]
    congr 1; exact filt_map _ _ _ (fun u => by simp only [bne]) _
  · simp only [bareStep,small,ite_false,get,List.map_cons,R.p.bin]
    congr 1; exact filt_map _ _ _ (fun u => by simp only [bne]) _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma project_tape {x : Word} (R : Automorphism x) (v : List Word) (d tape : ℕ) :
    bareReplay (v.map R.p.q) d tape=(bareReplay v d tape).map R.p.q := by
  induction d generalizing tape with
  | zero => rfl
  | succ d ih => simp only [bareReplay,ih,project_step]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma decode_words {x : Word} {c : Charts x} {f : Frame c} {j : ℕ} {s : Step c}
    (eq : f.decoded j=some s) :
    (s.after f.v).map Wire.w=bareStep (f.v.map Wire.w) j := by
  unfold Frame.decoded at eq
  unfold bareStep
  split at eq
  · rename_i small
    simp only [small,ite_true]
    split at eq
    · contradiction
    cases e : f.v[j/2]? with
    | none => simp [e] at eq
    | some a =>
      simp only [e,Option.map_some,Option.some.injEq] at eq
      subst s
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,e,Option.map_some,Option.getD_some,
        Step.after,Step.out,Step.rest,Wire.flip,List.map_cons,List.cons.injEq,true_and]
      exact (filt_map Wire.w _ (fun u => (Nat.mod j 2 == 1) || u != a.w) (fun _ => rfl) f.v).symm
  · rename_i large
    simp only [large,ite_false]
    split at eq
    · contradiction
    let i := j-32
    change ((f.v[i/128]?).bind _)=some s at eq
    cases e : f.v[i/128]? with
    | none => simp [e] at eq
    | some a =>
      simp only [e,Option.bind_some] at eq
      cases z : f.v[Nat.mod (i/8) 16]? with
      | none => simp [i] at z; simp [z] at eq
      | some b =>
        change Option.map _ (f.v[Nat.mod (i/8) 16]?) = some s at eq
        simp only [z,Option.map_some,Option.some.injEq] at eq
        subst s
        simp only [i] at e z
        simp only [List.getD_eq_getElem?_getD,List.getElem?_map,e,z,Option.map_some,Option.getD_some,
          Step.after,Step.out,Step.rest,Wire.binary,List.map_cons,List.cons.injEq,true_and]
        exact (filt_map Wire.w _ (fun u => ((Nat.mod (i/2) 2 == 1) || u != a.w) && ((Nat.mod i 2 == 1) || u != b.w)) (fun _ => rfl) f.v).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma jump_words {x : Word} {c : Charts x} {f g : Frame c} {j : ℕ} (h : f.jump j=some g) :
    g.v.map Wire.w=bareStep (f.v.map Wire.w) j := by
  unfold Frame.jump at h
  cases e : f.decoded j with
  | none => simp [e] at h
  | some s =>
    simp only [e,Option.bind_some] at h
    split at h
    · obtain rfl := Option.some.inj h; exact decode_words e
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma replay_words {x : Word} {c : Charts x} {f g : Frame c} {d tape} (h : f.replay d tape=some g) :
    g.v.map Wire.w=bareReplay (f.v.map Wire.w) d tape := by
  induction d generalizing tape g with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ d ih =>
    unfold Frame.replay at h
    cases e : f.replay d (tape/4096) with
    | none => simp [e] at h
    | some q =>
      obtain hq := jump_words (by simpa only [e,Option.bind_some] using h :
        q.jump (Nat.mod tape 4096-1)=some g)
      rw [hq,ih e]; rfl

-- Transfer an infeasibility proof within each orbit and certify representatives.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gather (v : ℕ) : List ℕ → ℕ
  | [] => 0
  | j::xs => (if v.testBit j then 1 else 0) + 2*gather v xs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def assignRows (order : List ℕ) (i : Fin 512) : Fin 512 := Fin.ofNat 512 (gather i.val order)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Rotation {x : Word} {c : Charts x} (root : Frame c) where
  R : Automorphism x
  base : List Word
  eq : base=(root.v.map Wire.w).map R.p.q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def refCode (links : Array ℕ) (j : ℕ) := (links[j]?).getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def linked {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (tag tape : ℕ) (f : Frame c) : Bool :=
  let k := tag/16-1
  refCode links k == 0 &&
    (rot[Nat.mod tag 16]?).any (fun A =>
      (rows[k]?).any (fun w => (root.replay d (w/65521)).any (fun g =>
        f.b==g.b && f.t==g.t && (bareReplay A.base d tape).isPerm (g.v.map Wire.w))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def symRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (known : Frame c → Bool) (hops j : ℕ) :=
  let tag := refCode links j
  if tag=0 then fastRow root d rows known hops j else
    (rows[j]?).all (fun w => (root.replay d (w/65521)).all (linked root d rows links rot tag (w/65521)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma linked_sound {x : Word} {c : Charts x} {root : Frame c} {d : ℕ} {rows links : Array ℕ}
    {rot : Array (Rotation root)} {tag tape : ℕ} {f : Frame c}
    (reps : ∀ (j w : ℕ), refCode links j=0 → rows[j]?=some w →
      ∀ g, root.replay d (w/65521)=some g → g.No)
    (he : root.replay d tape=some f) (h : linked root d rows links rot tag tape f=true) : f.No := by
  let k := tag/16-1
  obtain ⟨tagZero,rotHit⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨A,_,rowHit⟩ := (Option.any_eq_true ..).1 rotHit
  obtain ⟨word,ew,frameHit⟩ := (Option.any_eq_true ..).1 rowHit
  obtain ⟨g,eg,hit⟩ := (Option.any_eq_true ..).1 frameHit
  obtain ⟨bud,perm⟩ := Bool.and_eq_true_iff.mp hit
  obtain ⟨eb,et⟩ := Bool.and_eq_true_iff.mp bud
  have eb := beq_iff_eq.mp eb
  have et := beq_iff_eq.mp et
  have ng := reps k word (beq_iff_eq.mp tagZero) ew g eg
  have listEq : bareReplay A.base d tape=(f.v.map Wire.w).map A.R.p.q := by
    rw [A.eq,project_tape,←replay_words he]
  have eq : (wires f.v).image A.R.p.q = wires g.v := by
    ext a
    have p := (List.isPerm_iff.mp perm).mem_iff (a:=a)
    rw [listEq] at p
    simpa only [wires,List.mem_toFinset,List.mem_map,Finset.mem_image] using p
  intro hf
  have mapped := A.R.map_exact hf
  rw [eb,et,eq] at mapped
  exact ng mapped

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sym_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (rows links : Table) (rot : Array (Rotation root)) {known : Frame c → Bool}
    (sk : ∀ f, known f=true → f.No) (hops : ℕ)
    (h : Span (symRow root d rows links rot known hops) 0 rows.size) : TableSound root d rows := by
  have reps (j w : ℕ) (zero : refCode links j=0) (ew : rows[j]?=some w)
      (f : Frame c) (ef : root.replay d (w/65521)=some f) : f.No := by
    have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    have ck : Fast known hops f=true := by
      simpa only [symRow,zero,ite_true,fastRow,ew,Option.all_some,ef] using hh
    exact fast_sound known sk hx hops (Frame.replay_valid vr ef) ck
  intro j w ew f ef
  by_cases z : refCode links j=0
  · exact reps j w z ew f ef
  · have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    apply linked_sound reps ef (rot:=rot) (tag:=refCode links j)
    simpa only [symRow,z,ite_false,ew,Option.all_some,ef] using hh

-- A read-once monotone suffix cannot realize the six-row AND and OR requirements on a single pair of leaves.
abbrev Tiny := BitVec 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure TracePoint where
  row : Fin 6 → Fin 512

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def TracePoint.sig (p : TracePoint) (w : Word) : Tiny :=
  BitVec.ofBoolListBE [bit w (p.row 5),bit w (p.row 4),bit w (p.row 3),
    bit w (p.row 2),bit w (p.row 1),bit w (p.row 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sig_bit (p : TracePoint) (w : Word) (i : Fin 6) : (p.sig w)[i.val] = bit w (p.row i) := by
  let rows := [bit w (p.row 5),bit w (p.row 4),bit w (p.row 3),bit w (p.row 2),bit w (p.row 1),bit w (p.row 0)]
  have q := BitVec.getElem_ofBoolListBE (bs:=rows) (i:=i.val) (show i.val<rows.length from i.isLt)
  exact q.trans (by fin_cases i <;> rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sig_combine (p : TracePoint) (d : Bool) (a b : Word) :
    p.sig (combine d a b) = if d then p.sig a ||| p.sig b else p.sig a &&& p.sig b := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let i : Fin 6 := ⟨j,hj⟩
  rw [sig_bit p (combine d a b) i,bit_bin]
  cases d <;> simp only [Bool.false_eq_true,ite_false,ite_true,BitVec.getElem_and,BitVec.getElem_or] <;> rw [←sig_bit p a i,←sig_bit p b i]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def allowed (a b : Bool) (s : Tiny) : Bool :=
  (if a then (if b then 0xfffffffffdffffff else 0xdddddddd0000dddd)
    else (if b then 0xf5f5f5f500f500f5 else 0xd5d5d5d5000000d5) : ℕ).testBit s.toNat

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allowed_join : ∀ (a b c d : Bool) (s t : Tiny) (op : Bool),
    (a && c)=false → (b && d)=false → allowed a b s=true → allowed c d t=true →
    allowed (a||c) (b||d) (if op then s ||| t else s &&& t)=true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mergeMark (a b z w : Word) := if w=a ∨ w=b then z else w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rof_live {x : Word} (p : TracePoint) {n t S} (live : Live x n t S) (zero : t=0)
    (full : S.card=n+1) (A B : Word) (memA : A∈S) (memB : B∈S)
    (ok : ∀ w∈S, allowed (w==A) (w==B) (p.sig w)=true) :
    allowed true true (p.sig x)=true := by
  induction live generalizing A B with
  | done =>
    obtain rfl := Finset.mem_singleton.mp memA
    obtain rfl := Finset.mem_singleton.mp memB
    simpa using ok _ (Finset.mem_singleton_self _)
  | unary _ _ _ ih => omega
  | @binary n t U a b d pa pb ab fresh tail ih =>
    let z := combine d a b
    have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := count_live tail
    rw [Finset.card_insert_of_notMem zU] at cap
    have hbU : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at full
      have bind := Finset.card_insert_le a U
      omega
    have hbcard := Finset.card_insert_of_notMem hbU
    have haB : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at full
      omega
    rw [Finset.card_insert_of_notMem haB,hbcard] at full
    have member (w : Word) (pw : w∈insert a (insert b U)) :
        mergeMark a b z w ∈ insert z U := by
      by_cases eq : w=a ∨ w=b
      · simp [mergeMark,eq]
      · have hu : w∈U := ((Finset.mem_insert.mp ((Finset.mem_insert.mp pw).resolve_left (not_or.mp eq).1)).resolve_left (not_or.mp eq).2)
        simp [mergeMark,eq,hu]
    have mz (w : Word) (pw : w∈insert a (insert b U)) :
        (z==mergeMark a b z w) = ((a==w) || (b==w)) := by
      have zw : z≠w := fun e => fresh (show z∈insert a (insert b U) by rwa [e])
      by_cases e1 : w=a
      · simp [mergeMark,e1]
      by_cases e2 : w=b
      · simp [mergeMark,e2]
      simp only [mergeMark,e1,e2,or_self,ite_false]
      rw [beq_eq_false_iff_ne.mpr zw,beq_eq_false_iff_ne.mpr (Ne.symm e1),beq_eq_false_iff_ne.mpr (Ne.symm e2)]
      rfl
    have normal (u w : Word) (uU : u∈U) :
        (u==mergeMark a b z w)=(u==w) := by
      have ua : u≠a := by rintro rfl; exact haB (Finset.mem_insert_of_mem uU)
      have ub : u≠b := by rintro rfl; exact hbU uU
      have uz : u≠z := by rintro rfl; exact zU uU
      by_cases e1 : w=a <;> by_cases e2 : w=b <;> simp_all [mergeMark]
    apply ih zero (by rw [Finset.card_insert_of_notMem zU]; omega)
      (mergeMark a b z A) (mergeMark a b z B) (member A memA) (member B memB)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · change allowed (z==_) (z==_) (p.sig (combine d a b))=true
      rw [mz A memA,mz B memB,sig_combine]
      apply allowed_join
      · by_cases h : a=A
        · have nb : b≠A := by rintro e; exact ab (h.trans e.symm)
          simp [h,nb]
        · simp [h]
      · by_cases h : a=B
        · have nb : b≠B := by rintro e; exact ab (h.trans e.symm)
          simp [h,nb]
        · simp [h]
      · exact ok a (Finset.mem_insert_self ..)
      · exact ok b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    · rw [normal w A hw,normal w B hw]
      exact ok w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

-- Test six-row witnesses in parallel on the packed positive and negative samples.
abbrev Patch := BitVec 36
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lane (v : Word) (n : ℕ) : Patch := v.extractLsb' n 36

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def patchPoint {x : Word} (c : Charts x) (k : Fin 36) : TracePoint :=
  ⟨![c.p ⟨k.val, by omega⟩,c.n ⟨k.val,by omega⟩,c.n ⟨36+k.val,by omega⟩,
     c.p ⟨36+k.val,by omega⟩,c.p ⟨72+k.val,by omega⟩,c.n ⟨72+k.val,by omega⟩]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pGrey {x : Word} {c : Charts x} (w : Wire c) : Patch :=
  (~~~(lane w.p 0) ||| (lane w.n 0 &&& lane w.n 36)) &&&
  (~~~(lane w.p 36 ||| lane w.p 72) ||| lane w.n 72)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pLeft {x : Word} {c : Charts x} (w : Wire c) : Patch := lane w.n 0 &&& ~~~(lane w.p 72)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pRight {x : Word} {c : Charts x} (w : Wire c) : Patch := lane w.n 36 &&& ~~~(lane w.p 36)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wordGrey (s : Tiny) := (!s[0] || (s[1] && s[2])) && (!(s[3] || s[4]) || s[5])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wordLeft (s : Tiny) := s[1] && !s[4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wordRight (s : Tiny) := s[2] && !s[3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma legal_grey : ∀ s, wordGrey s=true → allowed false false s=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma legal_left : ∀ s, wordLeft s=true → allowed true false s=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma legal_right : ∀ s, wordRight s=true → allowed false true s=true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lane_bit (v : Word) (n : ℕ) (k : Fin 36) (h : n+k.val < 512) :
   (lane v n)[k.val] = bit v ⟨n+k.val,h⟩ := by
  exact (BitVec.getElem_extractLsb' (x:=v) (start:=n) k.isLt).trans (BitVec.getLsbD_eq_getElem h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma patch_extract {x : Word} {c : Charts x} (w : Wire c) (k : Fin 36) :
    (pGrey w)[k.val] = wordGrey ((patchPoint c k).sig w.w) ∧
    (pLeft w)[k.val] = wordLeft ((patchPoint c k).sig w.w) ∧
    (pRight w)[k.val] = wordRight ((patchPoint c k).sig w.w) := by
  have point (j : ℕ) (h : j<6) : ((patchPoint c k).sig w.w)[j]=bit w.w ((patchPoint c k).row ⟨j,h⟩) := sig_bit (patchPoint c k) w.w ⟨j,h⟩
  simp only [wordGrey,wordLeft,wordRight,pGrey,pLeft,pRight,BitVec.getElem_and,BitVec.getElem_or,
    BitVec.getElem_not,lane_bit _ 0 k (by omega),lane_bit _ 36 k (by omega),lane_bit _ 72 k (by omega)]
  rw [point 0 (by decide),point 1 (by decide),point 2 (by decide),point 3 (by decide),point 4 (by decide),point 5 (by decide)]
  simp only [w.hp,w.hn,Nat.zero_add]
  exact ⟨rfl,rfl,rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma patch_target {x : Word} (c : Charts x) (k : Fin 36) : (patchPoint c k).sig x=25 := by
  have q (i : Fin 6) : bit x ((patchPoint c k).row i) = (25 : Tiny)[i.val] := by
    fin_cases i <;> first | exact c.hp _ | exact c.hn _
  apply BitVec.eq_of_getElem_eq
  intro j hj
  exact (sig_bit (patchPoint c k) x ⟨j,hj⟩).trans (q ⟨j,hj⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def greyRest {x : Word} {c : Charts x} (a b : Word) : List (Wire c) → Patch
  | [] => BitVec.allOnes 36
  | w::v => if w.w==a || w.w==b then greyRest a b v else pGrey w &&& greyRest a b v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def findConflict {x : Word} {c : Charts x} (v : List (Wire c)) :=
  v.any (fun a => v.any (fun b => a.w != b.w &&
    (pLeft a &&& pRight b &&& greyRest a.w b.w v) != 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma uncovered {u : Patch} (neq : u≠0) : ∃ k : Fin 36, u[k.val]=true := by
  by_contra! no
  apply neq
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have q := no ⟨j,hj⟩
  cases h : u[j] <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rest_grey {x : Word} {c : Charts x} {a b : Word} {v : List (Wire c)} {k : Fin 36}
    (ok : (greyRest a b v)[k.val]=true) (w : Wire c) (inV : w∈v)
    (wa : w.w≠a) (wb : w.w≠b) : (pGrey w)[k.val]=true := by
  induction v with
  | nil => contradiction
  | cons h l ih =>
    cases e : (h.w==a || h.w==b)
    · rw [greyRest,e] at ok
      have val : (pGrey h &&& greyRest a b l)[k.val]=true := ok
      rw [BitVec.getElem_and] at val
      have two := Bool.and_eq_true_iff.mp val
      rcases List.mem_cons.mp inV with rfl|hw
      · exact two.1
      · exact ih two.2 hw
    · rw [greyRest,e] at ok
      apply ih ok
      apply (List.mem_cons.mp inV).resolve_left
      rintro rfl
      simp [beq_eq_false_iff_ne.mpr wa,beq_eq_false_iff_ne.mpr wb] at e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma no_readOnce {x : Word} {c : Charts x} {v : List (Wire c)} {b : ℕ}
    (nd : (v.map Wire.w).Nodup) (width : b+1=v.length) (hit : findConflict v=true) :
    ¬Exact x b 0 (wires v) := by
  rintro ⟨n,hn,t,ht,h⟩
  have card : (wires v).card=v.length := by
    change (v.map Wire.w).toFinset.card=v.length
    rw [List.toFinset_card_of_nodup nd,List.length_map]
  have cap := count_live h
  have eq : (wires v).card=n+1 := by omega
  obtain ⟨a,ha,yy⟩ := List.any_eq_true.mp hit
  obtain ⟨d,hd,yy⟩ := List.any_eq_true.mp yy
  obtain ⟨ad,mask⟩ := Bool.and_eq_true_iff.mp yy
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp mask)
  rw [BitVec.getElem_and,BitVec.getElem_and] at hk
  obtain ⟨both,rest⟩ := Bool.and_eq_true_iff.mp hk
  obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp both
  have valid := rof_live (patchPoint c k) h (by omega) eq a.w d.w
    (Step.mem_wires.mpr ⟨a,ha,rfl⟩) (Step.mem_wires.mpr ⟨d,hd,rfl⟩)
  have bad := valid (by
    intro y hy; obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp hy
    by_cases ea : u.w=a.w
    · rw [ea,beq_self_eq_true,beq_eq_false_iff_ne.mpr (bne_iff_ne.mp ad)]
      exact legal_left _ ((patch_extract a k).2.1 ▸ left)
    by_cases eb : u.w=d.w
    · rw [eb,beq_self_eq_true,beq_eq_false_iff_ne.mpr (Ne.symm (bne_iff_ne.mp ad))]
      exact legal_right _ ((patch_extract d k).2.2 ▸ right)
    rw [beq_eq_false_iff_ne.mpr ea,beq_eq_false_iff_ne.mpr eb]
    apply legal_grey
    rw [←(patch_extract u k).1]
    exact rest_grey rest u hu ea eb)
  rw [patch_target] at bad
  exact (by decide : allowed true true 25 ≠ true) bad

-- Assign the two distinguished inputs and verify the remaining inputs by a four-state scan.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Flags where
  grey : Patch
  a : Patch
  b : Patch
  ab : Patch

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def flagFold {x : Word} {c : Charts x} : List (Wire c) → Flags
  | [] => ⟨BitVec.allOnes 36,0,0,0⟩
  | w::v =>
    let f := flagFold v
    let g := pGrey w
    let a := pLeft w
    let b := pRight w
    ⟨g &&& f.grey,(g &&& f.a) ||| (a &&& f.grey),(g &&& f.b) ||| (b &&& f.grey),
      (g &&& f.ab) ||| (a &&& f.b) ||| (b &&& f.a)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def AllGrey {x : Word} {c : Charts x} (k : Fin 36) (v : List (Wire c)) :=
  ∀ w∈v, (pGrey w)[k.val]=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def OneSlot {x : Word} {c : Charts x} (mark : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, (mark a)[k.val]=true ∧ ∀ w∈v, w.w≠a.w → (pGrey w)[k.val]=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def TwoSlots {x : Word} {c : Charts x} (ma mb : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, ∃ b∈v, a.w≠b.w ∧ (ma a)[k.val]=true ∧ (mb b)[k.val]=true ∧
    ∀ w∈v, w.w≠a.w → w.w≠b.w → (pGrey w)[k.val]=true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma next_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c}
    (h : (pGrey w)[k.val]=true) (hg : AllGrey k v) : AllGrey k (w::v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma one_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {mark}
    (h : (pGrey w)[k.val]=true) (hg : OneSlot mark k v) : OneSlot mark k (w::v) := by
  obtain ⟨a,ha,hm,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,hm,?_⟩
  intro q hq nq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq nq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma one_pick {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {mark : Wire c→Patch}
    (h : (mark w)[k.val]=true) (hg : AllGrey k v) : OneSlot mark k (w::v) := by
  refine ⟨w,List.mem_cons_self,h,?_⟩
  intro q hq nq
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact nq rfl))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {ma mb}
    (h : (pGrey w)[k.val]=true) (hg : TwoSlots ma mb k v) : TwoSlots ma mb k (w::v) := by
  obtain ⟨a,ha,b,hb,ne,pa,pb,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,b,List.mem_cons_of_mem _ hb,ne,pa,pb,?_⟩
  intro q hq qa qb
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq qa qb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_pick {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {ma mb : Wire c→Patch}
    (nw : w.w∉wires v) (h : (ma w)[k.val]=true) (hg : OneSlot mb k v) : TwoSlots ma mb k (w::v) := by
  obtain ⟨a,ha,pa,hg⟩ := hg
  have ne : w.w≠a.w := fun eq => nw (Step.mem_wires.mpr ⟨a,ha,eq.symm⟩)
  refine ⟨w,List.mem_cons_self,a,List.mem_cons_of_mem _ ha,ne,h,pa,?_⟩
  intro q hq qw qa
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact qw rfl)) qa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_swap {x : Word} {c : Charts x} {k} {v : List (Wire c)} {ma mb}
    (h : TwoSlots ma mb k v) : TwoSlots mb ma k v := by
  obtain ⟨a,ha,b,hb,n,pa,pb,hh⟩ := h
  exact ⟨b,hb,a,ha,n.symm,pb,pa,fun q hq qb qa => hh q hq qa qb⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma flags_sound {x : Word} {c : Charts x} (k : Fin 36) (v : List (Wire c)) (nd : (v.map Wire.w).Nodup) :
    ((flagFold v).grey[k.val]=true → AllGrey k v) ∧
    ((flagFold v).a[k.val]=true → OneSlot pLeft k v) ∧
    ((flagFold v).b[k.val]=true → OneSlot pRight k v) ∧
    ((flagFold v).ab[k.val]=true → TwoSlots pLeft pRight k v) := by
  induction v with
  | nil => simp [AllGrey,flagFold]
  | cons w l ih =>
    obtain ⟨nw,nl⟩ := List.nodup_cons.mp nd
    have nm : w.w∉wires l := fun hh => nw (List.mem_toFinset.mp hh)
    obtain ⟨ig,ia,ib,iab⟩ := ih nl
    simp only [flagFold,BitVec.getElem_and,BitVec.getElem_or,Bool.and_eq_true,Bool.or_eq_true]
    refine ⟨fun ⟨wG,g⟩ => next_grey wG (ig g),?_,?_,?_⟩
    · rintro (⟨wg,a⟩|⟨wa,g⟩)
      · exact one_grey wg (ia a)
      · exact one_pick wa (ig g)
    · rintro (⟨wg,b⟩|⟨wb,g⟩)
      · exact one_grey wg (ib b)
      · exact one_pick wb (ig g)
    · rintro ((⟨wg,ab⟩|⟨wa,b⟩)|⟨wb,a⟩)
      · exact two_grey wg (iab ab)
      · exact two_pick nm wa (ib b)
      · exact two_swap (two_pick nm wb (ia a))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grey_rest_of {x : Word} {c : Charts x} {a b : Word} {v : List (Wire c)} {k : Fin 36}
    (h : ∀ w∈v, w.w≠a → w.w≠b → (pGrey w)[k.val]=true) : (greyRest a b v)[k.val]=true := by
  induction v with
  | nil => exact BitVec.getElem_allOnes k.val k.isLt
  | cons w l ih =>
    have tl := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases ea : w.w=a
    · simp [greyRest,ea,tl]
    by_cases eb : w.w=b
    · simp [greyRest,eb,tl]
    have ww := h w List.mem_cons_self ea eb
    simp only [greyRest,beq_eq_false_iff_ne.mpr ea,beq_eq_false_iff_ne.mpr eb,Bool.false_or,
      Bool.false_eq_true,ite_false,BitVec.getElem_and,ww,tl,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma certified_flags {x : Word} {c : Charts x} {v : List (Wire c)} {b : ℕ}
    (nd : (v.map Wire.w).Nodup) (width : b+1=v.length) (hit : (flagFold v).ab != 0) :
    ¬Exact x b 0 (wires v) := by
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp hit)
  obtain ⟨a,ha,z,hz,nz,pa,pz,gy⟩ := (flags_sound k v nd).2.2.2 hk
  apply no_readOnce nd width
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨z,hz,Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr nz,?_⟩⟩⟩
  apply bne_iff_ne.mpr
  intro eq
  have h := congrArg (fun u : Patch => u[k.val]) eq
  simp only [BitVec.getElem_and,pa,pz,grey_rest_of gy,Bool.true_and] at h
  exact Bool.noConfusion (h.trans (BitVec.getElem_zero k.isLt))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tightConflict {x : Word} {c : Charts x} (f : Frame c) :=
  (f.t==0 && f.b+1==f.v.length) && (flagFold f.v).ab != 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tight_sound {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid)
    (ok : tightConflict f=true) : f.No := by
  obtain ⟨small,hit⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨t,width⟩ := Bool.and_eq_true_iff.mp small
  have h := certified_flags valid.1 (beq_iff_eq.mp width) hit
  change ¬ Exact x f.b f.t (wires f.v)
  rwa [beq_iff_eq.mp t]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def readCut {x : Word} {c : Charts x} (f : Frame c) :=
  immediate f.b f.t f.v f.ps || tightConflict f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma read_cut {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid) (h : readCut f=true) : f.No := by
  rcases Bool.or_eq_true_iff.mp h with hi|hc
  · exact immediate_sound v.1 v.2 hi
  · exact tight_sound v hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ReadSearch {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => readCut f || known f
  | k+1,f => readCut f ||
      (!(f.v.any (fun a => a.w == x)) && scan f (ReadSearch known k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma read_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : ReadSearch known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact read_cut valid h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact read_cut valid h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def readRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (ReadSearch known hops))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rSymRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (known : Frame c → Bool) (hops j : ℕ) :=
  let tag := refCode links j
  if tag=0 then readRow root d rows known hops j else
    (rows[j]?).all (fun w => (root.replay d (w/65521)).all (linked root d rows links rot tag (w/65521)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rSym_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (rows links : Table) (rot : Array (Rotation root)) {known : Frame c → Bool}
    (sk : ∀ f, known f=true → f.No) (hops : ℕ)
    (h : Span (rSymRow root d rows links rot known hops) 0 rows.size) : TableSound root d rows := by
  have reps (j w : ℕ) (zero : refCode links j=0) (ew : rows[j]?=some w)
      (f : Frame c) (ef : root.replay d (w/65521)=some f) : f.No := by
    have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    have ck : ReadSearch known hops f=true := by
      simpa only [rSymRow,zero,ite_true,readRow,ew,Option.all_some,ef] using hh
    exact read_sound known sk hx hops (Frame.replay_valid vr ef) ck
  intro j w ew f ef
  by_cases z : refCode links j=0
  · exact reps j w z ew f ef
  · have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    apply linked_sound reps ef (rot:=rot) (tag:=refCode links j)
    simpa only [rSymRow,z,ite_false,ew,Option.all_some,ef] using hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Positive (x : Word) (S : Finset Word) : Prop :=
  ∀ a∈S, ∃ i j : Fin 512, bit x i=true ∧ bit x j=false ∧ bit a i=true ∧ bit a j=false ∧
    ∀ w∈S, w≠a → bit w i=bit w j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma exact_difference {x b t S} (h : Live x b t S) {i j : Fin 512}
    (xi : bit x i=true) (xj : bit x j=false) : ∃ a∈S, bit a i≠bit a j := by
  obtain ⟨a,ha,d⟩ := distinguishes_live h xi xj
  refine ⟨a,ha,?_⟩
  by_cases z : t=0
  · obtain ⟨u,v⟩ := (by simpa [distinguishes,z] using d : bit a i=true ∧ bit a j=false)
    simp [u,v]
  · simpa [distinguishes,z] using d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tight_parts {x : Word} {n t U a b d} (ab : a≠b)
    (fresh : combine d a b∉insert a (insert b U)) (tail : Live x n t (insert (combine d a b) U))
    (width : (insert a (insert b U)).card=n+1+1) :
    a∉U ∧ b∉U ∧ (insert (combine d a b) U).card=n+1 := by
  have zu : combine d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have cnt := count_live tail
  rw [Finset.card_insert_of_notMem zu] at cnt ⊢
  have notB : b∉U := by
    intro h
    rw [Finset.insert_eq_of_mem h] at width
    have lim := Finset.card_insert_le a U
    omega
  have bcard := Finset.card_insert_of_notMem notB
  have notA : a∉insert b U := by
    intro h
    rw [Finset.insert_eq_of_mem h] at width
    omega
  rw [Finset.card_insert_of_notMem notA,bcard] at width
  exact ⟨fun h => notA (Finset.mem_insert_of_mem h),notB,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tight_positive {x : Word} {n t S} (live : Live x n t S) (one : t≤1)
    (width : S.card=n+1) (positive : Positive x S) : t=0 := by
  induction live with
  | done => rfl
  | @unary n t U a ha fresh tail ih =>
    have zero : t=0 := by omega
    have zu : ~~~a ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
    have cnt := count_live tail
    rw [Finset.card_insert_of_notMem zu] at cnt
    have au : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at width
      -- A unary operation keeps the same budget, so retaining its input violates the tight width.
      omega
    obtain ⟨i,j,xi,xj,ai,aj,q⟩ := positive a (Finset.mem_insert_self ..)
    obtain ⟨w,hw,dist⟩ := distinguishes_live tail xi xj
    have dl : bit w i=true ∧ bit w j=false := by simpa [distinguishes,zero] using dist
    rcases Finset.mem_insert.mp hw with rfl|wu
    · simp [bit_not,ai] at dl
    · have wa : w≠a := by rintro rfl; exact au wu
      have e := q w (Finset.mem_insert_of_mem wu) wa
      simp [dl.1,dl.2] at e
  | @binary n t U a b d pa pb ab fresh tail ih =>
    obtain ⟨au,bu,tw⟩ := tight_parts ab fresh tail width
    apply ih one tw
    intro w hw
    have am : a∈insert a (insert b U) := Finset.mem_insert_self ..
    have bm : b∈insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    rcases Finset.mem_insert.mp hw with rfl|wu
    · obtain ⟨i,j,xi,xj,ai,aj,other⟩ := positive a am
      have beq := other b bm ab.symm
      obtain ⟨w,hw,diff⟩ := exact_difference tail xi xj
      have wz : w=combine d a b := (Finset.mem_insert.mp hw).resolve_right (by
        intro hu
        apply diff
        exact other w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) (by rintro rfl; exact au hu))
      subst w
      have pos : bit (combine d a b) i=true ∧ bit (combine d a b) j=false := by
        cases d <;> cases h : bit b j <;> simp_all only [bit_bin,Bool.false_eq_true,ite_false,ite_true,
          Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or] <;> decide
      refine ⟨i,j,xi,xj,pos.1,pos.2,?_⟩
      intro w hw wz
      have hu := (Finset.mem_insert.mp hw).resolve_left wz
      exact other w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) (by rintro rfl; exact au hu)
    · obtain ⟨i,j,xi,xj,wi,wj,other⟩ := positive w
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem wu))
      refine ⟨i,j,xi,xj,wi,wj,?_⟩
      intro q hq qw
      rcases Finset.mem_insert.mp hq with rfl|qu
      · have ae := other a am (by rintro rfl; exact au wu)
        have be := other b bm (by rintro rfl; exact bu wu)
        simp only [bit_bin,ae,be]
      · exact other q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem qu)) qw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def diffWords {x : Word} {c : Charts x} : List (Wire c) → Word × Word
  | [] => (0,0)
  | w::v =>
    let r := diffWords v
    let d := w.p ^^^ w.n
    (d ||| r.1,(d &&& r.1) ||| r.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma df_bit {x : Word} {c : Charts x} (v : List (Wire c)) (i : Fin 512) :
    (∀ w ∈ v, bit (w.p ^^^ w.n) i=true → bit (diffWords v).1 i=true) ∧
    (∀ w ∈ v, ∀ u ∈ v, w.w≠u.w → bit (w.p ^^^ w.n) i=true → bit (u.p ^^^ u.n) i=true →
      bit (diffWords v).2 i=true) := by
  induction v with
  | nil => simp
  | cons h l ih =>
    obtain ⟨one,two⟩ := ih
    have bor (u z : Word) : bit (u ||| z) i = (bit u i || bit z i) := BitVec.getElem_or _
    have band (u z : Word) : bit (u &&& z) i = (bit u i && bit z i) := BitVec.getElem_and _
    simp only [diffWords,bor,band,Bool.or_eq_true,Bool.and_eq_true]
    constructor
    · intro w hw eq
      rcases List.mem_cons.mp hw with rfl|hw
      · exact Or.inl eq
      · exact Or.inr (one w hw eq)
    · intro w hw u hu ne pw pu
      rcases List.mem_cons.mp hw with rfl|hw
      · have ut := (List.mem_cons.mp hu).resolve_left (by rintro rfl; exact ne rfl)
        exact Or.inl ⟨pw,one u ut pu⟩
      rcases List.mem_cons.mp hu with rfl|hu
      · have tl : w∈l := (List.mem_cons.mp hw).resolve_left (by rintro rfl; exact ne rfl)
        exact Or.inl ⟨pu,one w tl pw⟩
      · exact Or.inr (two w hw u hu ne pw pu)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def allPositive {x : Word} {c : Charts x} (v : List (Wire c)) :=
  let single := ~~~(diffWords v).2
  v.all (fun w => (w.p &&& ~~~w.n &&& single) != 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma marked_word {q : Word} (n : q≠0) : ∃ i : Fin 512, bit q i=true := by
  by_contra! no
  apply n
  apply BitVec.eq_of_getElem_eq
  intro j h
  have z := no ⟨j,h⟩
  change bit q ⟨j,h⟩=bit 0 ⟨j,h⟩
  rw [bit_zero]
  cases eq : bit q ⟨j,h⟩ <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma positive_checked {x : Word} {c : Charts x} {v : List (Wire c)}
    (ok : allPositive v=true) : Positive x (wires v) := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  have nz := List.all_eq_true.mp ok w hw
  obtain ⟨i,e⟩ := marked_word (bne_iff_ne.mp nz)
  have cast : bit (w.p &&& ~~~w.n &&& ~~~(diffWords v).2) i =
      ((bit w.p i && !bit w.n i) && !bit (diffWords v).2 i) := by
    simp only [bit,BitVec.getElem_and,BitVec.getElem_not]
  rw [cast] at e
  have ⟨a,e0⟩ := Bool.and_eq_true_iff.mp e
  have ⟨p,n⟩ := Bool.and_eq_true_iff.mp a
  have wn : bit w.n i=false := by simpa using n
  have wt : bit (w.p ^^^ w.n) i=true := by
    rw [show bit (w.p ^^^ w.n) i=(bit w.p i ^^ bit w.n i) from BitVec.getElem_xor _]
    simp [p,wn]
  refine ⟨c.p i,c.n i,c.hp i,c.hn i,(w.hp i) ▸ p,(w.hn i) ▸ wn,?_⟩
  intro u hu ne
  obtain ⟨z,hz,rfl⟩ := Step.mem_wires.mp hu
  rw [←z.hp i,←z.hn i]
  by_contra bad
  have dz : bit (z.p ^^^ z.n) i=true := by
    rw [show bit (z.p ^^^ z.n) i=(bit z.p i ^^ bit z.n i) from BitVec.getElem_xor _]
    cases e1 : bit z.p i <;> cases e2 : bit z.n i <;> simp_all
  have h2 := (df_bit v i).2 w hw z hz ne.symm wt dz
  simp [h2] at e0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def positiveConflict {x : Word} {c : Charts x} (f : Frame c) :=
  (f.b+1==f.v.length) && ((f.t==0 || (f.t==1 && allPositive f.v)) && (flagFold f.v).ab != 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma positive_conflict {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid)
    (ok : positiveConflict f=true) : f.No := by
  obtain ⟨width,rest⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨tst,mask⟩ := Bool.and_eq_true_iff.mp rest
  have width := beq_iff_eq.mp width
  have no := certified_flags valid.1 width mask
  rcases Bool.or_eq_true_iff.mp tst with t|p
  · change ¬Exact x f.b f.t (wires f.v)
    rwa [beq_iff_eq.mp t]
  obtain ⟨one,positive⟩ := Bool.and_eq_true_iff.mp p
  have one := beq_iff_eq.mp one
  rintro ⟨b,hb,t,ht,h⟩
  have card : (wires f.v).card=f.v.length := by
    change (f.v.map Wire.w).toFinset.card=f.v.length
    rw [List.toFinset_card_of_nodup valid.1,List.length_map]
  have cap := count_live h
  have zero := tight_positive h (by omega) (by omega) (positive_checked positive)
  exact no ⟨b,hb,t,by omega,h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full_raw {x b t S} (sens : Positive x S) (h : ¬Exact x b t S) :
    ¬Feasible x b t S := by
  rintro ⟨n,hn,j,hj,T,sub,live⟩
  have need : S⊆T := by
    intro a ha
    obtain ⟨i,k,pi,ni,_,_,only⟩ := sens a ha
    obtain ⟨w,hw,diff⟩ := exact_difference live pi ni
    by_contra miss
    have ne : w≠a := by rintro rfl; exact miss hw
    exact diff (only w (sub hw) ne)
  have eq := Finset.Subset.antisymm sub need
  exact h ⟨n,hn,j,hj,eq ▸ live⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def countConst {x : Word} {c : Charts x} (m : Word) : List (Wire c) → ℕ
  | [] => 0
  | a::l => if maskedConst m a.w then (countConst m l)+1 else countConst m l

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma count_const {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) :
    countConst f.mask v=loss f v := by
  induction v with
  | nil => rfl
  | cons a l ih =>
    cases e : maskedConst f.mask a.w <;> simp_all [countConst,loss,List.filter_cons]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cheapCut {x : Word} {c : Charts x} (b : ℕ) (v : List (Wire c)) (p : Price x) :=
  let need := p.basis.lo+countConst p.basis.mask v
  decide (b<need) && decide (b+p.spent<need)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cheap_sound_cut {x : Word} {c : Charts x} {b} {v : List (Wire c)} {p : Price x}
    (ok : cheapCut b v p=true) : p.cuts b v=true := by
  have q := (Bool.and_eq_true_iff.mp ok).2
  simpa only [Price.cuts,count_const] using q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Cheap {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => f.ps.any (cheapCut f.b f.v) || known f
  | k+1,f => f.ps.any (cheapCut f.b f.v) ||
      (!(f.v.any (fun a => a.w == x)) && scan f (Cheap known k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cheap_cut {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid)
    (h : f.ps.any (cheapCut f.b f.v)=true) : f.No := by
  obtain ⟨p,hp,hc⟩ := List.any_eq_true.mp h
  exact cut_sound v.1 (v.2 _ hp) (cheap_sound_cut hc)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cheap_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : Cheap known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact cheap_cut valid h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact cheap_cut valid h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

-- The three coverage counters follow the construction in the Petersen parent proof.
abbrev Cov := Word × Word × Word

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def addCov (z : Word) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def takeOne (c : Cov) (a : Word) : Word := c.1 &&& ~~~(c.2.1 &&& a)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def takeTwo (c : Cov) (a b : Word) : Word :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_one (c : Cov) (a : Word) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_two (c : Cov) (a b : Word) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma add_swap (c : Cov) (a b : Word) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def accumCov {x : Word} {c : Charts x} (t : ℕ) : List (Wire c) → Cov
  | [] => (0,0,0)
  | a::rest => addCov (a.sep t) (accumCov t rest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_permute {x : Word} {c : Charts x} (t : ℕ) {u v : List (Wire c)} (p : u.Perm v) : accumCov t u=accumCov t v := by
  induction p with
  | nil => rfl
  | cons a _ h => exact congrArg (addCov (a.sep t)) h
  | swap a b t => exact add_swap ..
  | trans _ _ a b => exact a.trans b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_first {x : Word} {c : Charts x} (t : ℕ) (v : List (Wire c)) : (accumCov t v).1=cover t v := by
  induction v with
  | nil => rfl
  | cons a v ih => change a.sep t ||| (accumCov t v).1= _; rw [ih]; rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wire_injective {x : Word} {c : Charts x} : Function.Injective (Wire.w (c:=c)) := by
  intro a b e
  have pe:a.p=b.p := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    change bit a.p ⟨j,hj⟩=bit b.p ⟨j,hj⟩; rw [a.hp,b.hp,e]
  have ne:a.n=b.n := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    change bit a.n ⟨j,hj⟩=bit b.n ⟨j,hj⟩; rw [a.hn,b.hn,e]
  cases a; cases b; simp_all
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_single {x : Word} {c : Charts x} {a : Wire c} {v : List (Wire c)} (nd : v.Nodup) (ha : a∈v) : v.Perm (a::alone a v) := by
  classical
  have p:=List.perm_cons_erase ha
  rw [nd.erase_eq_filter] at p
  have filt : v.filter (fun w=>w != a)=alone a v := by
    apply List.filter_congr; intro w _
    by_cases e:w=a
    · simp [e]
    · have h : w.w≠a.w := fun z=>e (wire_injective z)
      simp [bne_iff_ne.mpr e,bne_iff_ne.mpr h]
  rwa [filt] at p
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_alone {x : Word} {c : Charts x} {a : Wire c} {v : List (Wire c)} (t : ℕ)
    (nd : (v.map Wire.w).Nodup) (ha : a∈v) : takeOne (accumCov t v) (a.sep t)=cover t (alone a v) := by
  rw [cov_permute t (split_single (List.Nodup.of_map _ nd) ha)]
  exact (cov_one ..).trans (cov_first ..)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_aside {x : Word} {c : Charts x} {a b : Wire c} {v : List (Wire c)} (t : ℕ)
    (nd : (v.map Wire.w).Nodup) (ha : a∈v) (hb : b∈v) (ab : a.w.toNat<b.w.toNat) :
    takeTwo (accumCov t v) (a.sep t) (b.sep t)=cover t (aside a b v) := by
  have vnd:=List.Nodup.of_map _ nd
  have neq : b.w≠a.w := by intro eq; simp [eq] at ab
  have bm : b∈alone a v := List.mem_filter.mpr ⟨hb,bne_iff_ne.mpr neq⟩
  have perm := (split_single vnd ha).trans ((split_single (vnd.filter _) bm).cons a)
  have eq : alone b (alone a v)=aside a b v := by
    simp only [alone,aside,List.filter_filter]; apply List.filter_congr; intro w _; exact Bool.and_comm ..
  rw [cov_permute t perm,←eq]
  exact (cov_two ..).trans (cov_first ..)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def coveredScan {x : Word} {c : Charts x} (f : Frame c) (next : Frame c → Bool) :=
  let len := f.v.length
  let test := fun (s : Step c) (budget : ℕ) (bits : Word) =>
    decide (budget+1+s.drops < len+1) || bits != top || !isEligible s f.v || next (f.child s)
  f.v.all (fun a =>
    ((f.t==0) ||
      (let t := f.t-1
       let r := takeOne (accumCov t f.v) (a.sep t)
       let g := a.flip.sep t
       test (.flip a false) f.b (g ||| r) && test (.flip a true) f.b (g ||| (a.sep t ||| r)))) &&
    ((f.b==0) || f.v.all (fun w => !(decide (a.w.toNat < w.w.toNat)) ||
      (let r := takeTwo (accumCov f.t f.v) (a.sep f.t) (w.sep f.t)
       let wa := a.sep f.t
       let wb := w.sep f.t
       [false,true].all (fun d =>
         let g := (a.binary d w).sep f.t
         [false,true].all (fun ka => [false,true].all (fun kb =>
           test (.binary d a w ka kb) (f.b-1) (g ||| addSep ka wa (addSep kb wb r)))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma covered_sound {x : Word} {c : Charts x} {f : Frame c} {s : Step c} {next : Frame c → Bool}
    (h : coveredScan f next = true) (nd : (f.v.map Wire.w).Nodup)
    (hs : s ∈ Step.all f.b f.t f.v) (el : eligible f.v s)
    (ht : Exact x (s.budget f.b f.t).1 (s.budget f.b f.t).2 (wires (s.after f.v))) :
    next (f.child s)=true := by
  have fit := fits_step f.v s nd el ht
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hs
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i tpos
    have q := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hh.1).resolve_left
      (by simpa only [beq_iff_eq] using tpos))
    rw [cov_alone _ nd ha] at q
    rcases List.mem_cons.mp hu with rfl|hu
    · have eq := cover_unary false ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,Bool.false_eq_true,ite_false] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.1
    · obtain rfl := List.mem_singleton.mp hu
      have eq := cover_unary true ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,ite_true] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.2
  · split at hb
    · contradiction
    rename_i bpos
    have q := (Bool.or_eq_true_iff.mp hh.2).resolve_left (by simpa only [beq_iff_eq] using bpos)
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · rename_i lt
      have gate := (Bool.or_eq_true_iff.mp (List.all_eq_true.mp q w hw)).resolve_left (by simp [lt])
      rw [cov_aside _ nd ha hw lt] at gate
      obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,hka,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp h
      have val := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp gate d hd) ka hka) kb hkb
      have eq := cover_binary d ka kb ht
      simp only [Step.budget] at eq
      change f.v.length+1 ≤ f.b-1+1+_ at fit
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using val
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive ReadTree
  | atom (w : Word) (inv : Bool)
  | gate (d : Bool) (a b : ReadTree)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def signedWord (w : Word) (inv : Bool) := if inv then ~~~w else w
namespace ReadTree
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def value : ReadTree → Word
  | atom w i => signedWord w i
  | gate d a b => combine d a.value b.value

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hits (w : Word) : ReadTree → ℕ
  | atom a _ => if a=w then 1 else 0
  | gate _ a b => a.hits w + b.hits w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def has (w : Word) (i : Bool) : ReadTree → Prop
  | atom a j => a=w ∧ j=i
  | gate _ a b => a.has w i ∨ b.has w i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma has_hit {t : ReadTree} {w i} (h : t.has w i) : 0<t.hits w := by
  induction t with
  | atom a j => obtain ⟨rfl,_⟩ := h; simp [hits]
  | gate d a b ia ib => rcases h with h|h <;> simp only [hits] <;> first | have := ia h; omega | have := ib h; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma one_sign (t : ReadTree) {w i j} (n : t.hits w ≤ 1) (p : t.has w i) (q : t.has w j) : i=j := by
  induction t with
  | atom a k => exact p.2.symm.trans q.2
  | gate d a b ai bi =>
    change a.hits w+b.hits w≤1 at n
    rcases p with p|p <;> rcases q with q|q
    · exact ai (by omega) p q
    · have := has_hit p; have := has_hit q; omega
    · have := has_hit p; have := has_hit q; omega
    · exact bi (by omega) p q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def splice (u : Word) (f : Bool → ReadTree) : ReadTree → ReadTree
  | atom a i => if a=u then f i else atom a i
  | gate d a b => gate d (a.splice u f) (b.splice u f)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma splice_value (t : ReadTree) (u : Word) (f : Bool → ReadTree)
    (ok : ∀ i, (f i).value=signedWord u i) : (t.splice u f).value=t.value := by
  induction t with
  | atom a i => by_cases e:a=u <;> simp [splice,value,e,ok]
  | gate d a b ia ib => simp only [splice,value,ia,ib]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma splice_hits (t : ReadTree) (u w : Word) (f : Bool → ReadTree) (m : ℕ)
    (ok : ∀ i, (f i).hits w=m) : (t.splice u f).hits w =
      (if w=u then 0 else t.hits w) + t.hits u*m := by
  induction t with
  | atom a i => cases i <;> by_cases e : a=u <;> by_cases q : w=u <;> simp_all [splice,hits,eq_comm] <;> omega
  | gate d a b ia ib =>
    simp only [splice,hits,ia,ib,Nat.add_mul]
    split <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma separating (t : ReadTree) (i j : Fin 512) (p : bit t.value i=true) (q : bit t.value j=false) :
    ∃ w s, t.has w s ∧ bit (signedWord w s) i=true ∧ bit (signedWord w s) j=false := by
  induction t with
  | atom w s => exact ⟨w,s,⟨rfl,rfl⟩,p,q⟩
  | gate d a b ia ib =>
    simp only [value,bit_bin] at p q
    have aux : (bit a.value i=true ∧ bit a.value j=false) ∨ (bit b.value i=true ∧ bit b.value j=false) := by
      cases d <;> cases h : bit a.value i <;> cases h' : bit a.value j <;> simp_all
    rcases aux with h|h
    · obtain ⟨w,s,z,e₁,e₂⟩ := ia h.1 h.2; exact ⟨w,s,Or.inl z,e₁,e₂⟩
    · obtain ⟨w,s,z,e₁,e₂⟩ := ib h.1 h.2; exact ⟨w,s,Or.inr z,e₁,e₂⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma marks (t : ReadTree) (p : TracePoint) (A B : Word) (ca : t.hits A≤1) (cb : t.hits B≤1)
    (ok : ∀ w s, t.has w s → allowed (w==A) (w==B) (p.sig (signedWord w s))=true) :
    allowed (decide (0<t.hits A)) (decide (0<t.hits B)) (p.sig t.value)=true := by
  induction t with
  | atom w s =>
    have eq (X : Word) : decide (0 < (ReadTree.atom w s).hits X) = (w==X) := by
      by_cases e : w=X
      · simp [hits,e]
      · simp [hits,e,beq_eq_false_iff_ne.mpr e]
    rw [eq,eq]; exact ok w s ⟨rfl,rfl⟩
  | gate d a b ia ib =>
    change a.hits A+b.hits A≤1 at ca; change a.hits B+b.hits B≤1 at cb
    have la := ia (by omega) (by omega) (fun w s h=>ok w s (Or.inl h))
    have lb := ib (by omega) (by omega) (fun w s h=>ok w s (Or.inr h))
    have one (j k : ℕ) (e : j+k≤1) : (decide (0<j) && decide (0<k))=false := by simp; omega
    have pos (j k : ℕ) : decide (0<j+k)=(decide (0<j)||decide (0<k)) := by
      by_cases hj : 0<j <;> by_cases hk : 0<k <;> simp_all <;> omega
    change allowed (decide (0<a.hits A+b.hits A)) (decide (0<a.hits B+b.hits B)) (p.sig (combine d a.value b.value))=true
    rw [pos,pos,sig_combine]
    exact allowed_join _ _ _ _ _ _ d (one _ _ ca) (one _ _ cb) la lb
end ReadTree

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def deMorgan (d i : Bool) (a b : Word) :=
  ReadTree.gate (d ^^ i) (.atom a i) (.atom b i)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma deMorgan_value (d i : Bool) (a b : Word) : (deMorgan d i a b).value=signedWord (combine d a b) i := by
  cases d <;> cases i <;> simp [deMorgan,ReadTree.value,signedWord,combine]
  all_goals apply BitVec.eq_of_getElem_eq; intro j hj; simp [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Once (x : Word) (S : Finset Word) := ∃ t : ReadTree, t.value=x ∧ ∀ w, t.hits w=if w∈S then 1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma once_of_tight {x n k S} (h : Live x n k S) (width : S.card=n+1) : Once x S := by
  induction h with
  | done => exact ⟨.atom x false,rfl,by intro w; by_cases e:x=w <;> simp_all [ReadTree.hits,eq_comm]⟩
  | @unary n k U a ha fresh tail ih =>
    have zu : ~~~a∉U := fun h=>fresh (Finset.mem_insert_of_mem h)
    have cnt:=count_live tail
    rw [Finset.card_insert_of_notMem zu] at cnt
    have au : a∉U := by rintro eh; rw [Finset.insert_eq_of_mem eh] at width; omega
    obtain ⟨t,eq,ht⟩ := ih (by rw [Finset.card_insert_of_notMem au] at width; rw [Finset.card_insert_of_notMem zu]; omega)
    let f := fun i => ReadTree.atom a (!i)
    refine ⟨t.splice (~~~a) f,(t.splice_value _ f (fun i=>by cases i <;> simp [f,ReadTree.value,signedWord])).trans eq,?_⟩
    intro w
    rw [t.splice_hits (~~~a) w f (if a=w then 1 else 0) (by intro i; rfl),ht,ht]
    have az : ~~~a≠a := fun e=>fresh (Finset.mem_insert.mpr (Or.inl e))
    by_cases e : w=a <;> by_cases z : w = ~~~a <;> simp_all [eq_comm]
  | @binary n k U a b d ha hb ab fresh tail ih =>
    let z:=combine d a b
    have zu : z∉U := fun h=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    obtain ⟨au,bu,tw⟩ := tight_parts ab fresh tail width
    obtain ⟨t,eq,ht⟩ := ih tw
    let f:=fun i=>deMorgan d i a b
    refine ⟨t.splice z f,(t.splice_value z f (fun i=>deMorgan_value ..)).trans eq,?_⟩
    intro w
    rw [t.splice_hits z w f ((if a=w then 1 else 0)+(if b=w then 1 else 0)) (by intro i; rfl),ht,ht]
    have za : z≠a := fun e=>fresh (Finset.mem_insert.mpr (Or.inl e))
    have zb : z≠b := fun e=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e)))
    change _ + (if z∈insert z U then _ else _)*_=_
    by_cases e : w=a <;> by_cases g : w=b <;> by_cases q : w=z <;> simp_all [eq_comm,z]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def maskFold {x : Word} {c : Charts x} (gray left right : Wire c→Patch) : List (Wire c) → Flags
  | [] => ⟨BitVec.allOnes 36,0,0,0⟩
  | w::v =>
    let f := maskFold gray left right v
    let g := gray w
    let a := left w
    let b := right w
    ⟨g &&& f.grey,(g &&& f.a) ||| (a &&& f.grey),(g &&& f.b) ||| (b &&& f.grey),
      (g &&& f.ab) ||| (a &&& f.b) ||| (b &&& f.a)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def MaskGrey {x : Word} {c : Charts x} (gray : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∀ w∈v, (gray w)[k.val]=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def MaskOne {x : Word} {c : Charts x} (gray : Wire c→Patch) (mark : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, (mark a)[k.val]=true ∧ ∀ w∈v, w.w≠a.w → (gray w)[k.val]=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def MaskTwo {x : Word} {c : Charts x} (gray : Wire c→Patch) (ma mb : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, ∃ b∈v, a.w≠b.w ∧ (ma a)[k.val]=true ∧ (mb b)[k.val]=true ∧
    ∀ w∈v, w.w≠a.w → w.w≠b.w → (gray w)[k.val]=true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_next {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c}
    (h : (gray w)[k.val]=true) (hg : MaskGrey gray k v) : MaskGrey gray k (w::v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_onegrey {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {mark}
    (h : (gray w)[k.val]=true) (hg : MaskOne gray mark k v) : MaskOne gray mark k (w::v) := by
  obtain ⟨a,ha,hm,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,hm,?_⟩
  intro q hq nq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq nq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_onepick {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {mark : Wire c→Patch}
    (h : (mark w)[k.val]=true) (hg : MaskGrey gray k v) : MaskOne gray mark k (w::v) := by
  refine ⟨w,List.mem_cons_self,h,?_⟩
  intro q hq nq
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact nq rfl))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_twogrey {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {ma mb}
    (h : (gray w)[k.val]=true) (hg : MaskTwo gray ma mb k v) : MaskTwo gray ma mb k (w::v) := by
  obtain ⟨a,ha,b,hb,ne,pa,pb,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,b,List.mem_cons_of_mem _ hb,ne,pa,pb,?_⟩
  intro q hq qa qb
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq qa qb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_twopick {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {ma mb : Wire c→Patch}
    (nw : w.w∉wires v) (h : (ma w)[k.val]=true) (hg : MaskOne gray mb k v) : MaskTwo gray ma mb k (w::v) := by
  obtain ⟨a,ha,pa,hg⟩ := hg
  have ne : w.w≠a.w := fun eq => nw (Step.mem_wires.mpr ⟨a,ha,eq.symm⟩)
  refine ⟨w,List.mem_cons_self,a,List.mem_cons_of_mem _ ha,ne,h,pa,?_⟩
  intro q hq qw qa
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact qw rfl)) qa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_swap {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {ma mb}
    (h : MaskTwo gray ma mb k v) : MaskTwo gray mb ma k v := by
  obtain ⟨a,ha,b,hb,n,pa,pb,hh⟩ := h
  exact ⟨b,hb,a,ha,n.symm,pb,pa,fun q hq qb qa => hh q hq qa qb⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_sound {x : Word} {c : Charts x} (gray left right : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) (nd : (v.map Wire.w).Nodup) :
    ((maskFold gray left right v).grey[k.val]=true → MaskGrey gray k v) ∧
    ((maskFold gray left right v).a[k.val]=true → MaskOne gray left k v) ∧
    ((maskFold gray left right v).b[k.val]=true → MaskOne gray right k v) ∧
    ((maskFold gray left right v).ab[k.val]=true → MaskTwo gray left right k v) := by
  induction v with
  | nil => simp [MaskGrey,maskFold]
  | cons w l ih =>
    obtain ⟨nw,nl⟩ := List.nodup_cons.mp nd
    have nm : w.w∉wires l := fun hh => nw (List.mem_toFinset.mp hh)
    obtain ⟨ig,ia,ib,iab⟩ := ih nl
    simp only [maskFold,BitVec.getElem_and,BitVec.getElem_or,Bool.and_eq_true,Bool.or_eq_true]
    refine ⟨fun ⟨wG,g⟩ => mask_next wG (ig g),?_,?_,?_⟩
    · rintro (⟨wg,a⟩|⟨wa,g⟩)
      · exact mask_onegrey wg (ia a)
      · exact mask_onepick wa (ig g)
    · rintro (⟨wg,b⟩|⟨wb,g⟩)
      · exact mask_onegrey wg (ib b)
      · exact mask_onepick wb (ig g)
    · rintro ((⟨wg,ab⟩|⟨wa,b⟩)|⟨wb,a⟩)
      · exact mask_twogrey wg (iab ab)
      · exact mask_twopick nm wa (ib b)
      · exact mask_swap (mask_twopick nm wb (ia a))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def turned {x : Word} {c : Charts x} (w : Wire c) (s : Bool) : Wire c := if s then w.flip else w
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma turned_word {x : Word} {c : Charts x} (w : Wire c) (s : Bool) : (turned w s).w=signedWord w.w s := by cases s <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def adverse {x : Word} {c : Charts x} (single : Word) (w : Wire c) (s : Bool) :=
  let a:=turned w s
  (a.n &&& ~~~a.p &&& single) != 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairedMask {x : Word} {c : Charts x} (single : Word) (m : Wire c→Patch) (w : Wire c) :=
  (if adverse single w false then BitVec.allOnes 36 else m w) &&&
  (if adverse single w true then BitVec.allOnes 36 else m w.flip)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma paired_bit {x : Word} {c : Charts x} {w : Wire c} {single : Word} {k : Fin 36}
    {m : Wire c→Patch} {s : Bool} (h : (pairedMask single m w)[k.val]=true)
    (go : adverse single w s=false) : (m (turned w s))[k.val]=true := by
  rw [pairedMask,BitVec.getElem_and,Bool.and_eq_true] at h
  cases s
  · simpa only [go,Bool.false_eq_true,ite_false,turned] using h.1
  · simpa only [go,Bool.false_eq_true,ite_false,turned,ite_true] using h.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma turns_diff {x : Word} {c : Charts x} {w : Wire c} {s : Bool} {i : Fin 512}
    (dif : bit (signedWord w.w s) (c.p i) ≠ bit (signedWord w.w s) (c.n i)) :
    bit (w.p ^^^ w.n) i=true := by
  rw [show bit (w.p ^^^ w.n) i=(bit w.p i ^^ bit w.n i) from BitVec.getElem_xor _,w.hp,w.hn]
  cases s <;> cases a : bit w.w (c.p i) <;> cases b : bit w.w (c.n i) <;>
    simp_all [signedWord,bit_not]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sign_used {x : Word} {c : Charts x} {v : List (Wire c)} {t : ReadTree} (val : t.value=x)
    (hits : ∀ w, t.hits w=if w∈wires v then 1 else 0) {w : Wire c} (hw : w∈v) {s : Bool}
    (used : t.has w.w s) : adverse (~~~(diffWords v).2) w s=false := by
  by_contra! fail
  have neq : ((turned w s).n &&& ~~~(turned w s).p &&& ~~~(diffWords v).2)≠0 := bne_iff_ne.mp (Bool.eq_true_of_not_eq_false fail)
  obtain ⟨i,fi⟩ := marked_word neq
  have detail : (bit (turned w s).n i && !bit (turned w s).p i && !bit (diffWords v).2 i)=true := by simpa only [bit,BitVec.getElem_and,BitVec.getElem_not] using fi
  obtain ⟨first,unique⟩ := Bool.and_eq_true_iff.mp detail
  obtain ⟨down,nup⟩ := Bool.and_eq_true_iff.mp first
  have up : bit (signedWord w.w s) (c.p i)=false := by simpa only [←turned_word,(turned w s).hp,Bool.not_eq_true'] using nup
  have dn : bit (signedWord w.w s) (c.n i)=true := by simpa only [←turned_word,(turned w s).hn] using down
  obtain ⟨a,j,here,pa,na⟩ := t.separating (c.p i) (c.n i) (val ▸ c.hp i) (val ▸ c.hn i)
  by_cases eq : a=w.w
  · subst a
    have jm := t.one_sign (by rw [hits]; split <;> omega) here used
    simp [jm,up] at pa
  · have present : a∈wires v := by
      have q:=ReadTree.has_hit here; by_contra hm; simp [hits,hm] at q
    obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp present
    have d1:=turns_diff (w:=u) (s:=j) (i:=i) (by simp [pa,na])
    have d2:=turns_diff (w:=w) (s:=s) (i:=i) (by simp [up,dn])
    have two := (df_bit v i).2 u hu w hw eq d1 d2
    simp [two] at unique

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def signCut {x : Word} {c : Charts x} (f : Frame c) :=
  f.b+1==f.v.length &&
    (let single:= ~~~(diffWords f.v).2
     let m:=pairedMask single
     (maskFold (m pGrey) (m pLeft) (m pRight) f.v).ab != 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sign_cut {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid) (cut : signCut f=true) : f.No := by
  obtain ⟨width,hit⟩ := Bool.and_eq_true_iff.mp cut
  have width:=beq_iff_eq.mp width
  rintro ⟨n,hn,j,hj,live⟩
  have len : (wires f.v).card=f.v.length := by
    change (f.v.map Wire.w).toFinset.card=f.v.length
    rw [List.toFinset_card_of_nodup valid.1,List.length_map]
  have cap:=count_live live
  obtain ⟨t,val,hits⟩ := once_of_tight live (by omega)
  let single:= ~~~(diffWords f.v).2
  let m:=pairedMask (c:=c) single
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp hit)
  obtain ⟨a,ha,z,hz,nz,pa,pz,gy⟩ := (mask_sound (m pGrey) (m pLeft) (m pRight) k f.v valid.1).2.2.2 hk
  have ah : t.hits a.w=1 := by rw [hits,if_pos (Step.mem_wires.mpr ⟨a,ha,rfl⟩)]
  have zh : t.hits z.w=1 := by rw [hits,if_pos (Step.mem_wires.mpr ⟨z,hz,rfl⟩)]
  have allok := t.marks (patchPoint c k) a.w z.w ah.le zh.le (by
    intro w s hs
    have present : w∈wires f.v := by
      have q:=ReadTree.has_hit hs; by_contra h; simp [hits,h] at q
    obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp present
    have ok := sign_used val hits hu hs
    by_cases ua : u.w=a.w
    · rw [ua,beq_self_eq_true,beq_eq_false_iff_ne.mpr nz]
      have useA : t.has a.w s := ua ▸ hs
      have v := paired_bit pa (sign_used val hits ha useA)
      rw [←turned_word]
      exact legal_left _ ((patch_extract (turned a s) k).2.1 ▸ v)
    by_cases uz : u.w=z.w
    · rw [uz,beq_eq_false_iff_ne.mpr nz.symm,beq_self_eq_true]
      have useZ : t.has z.w s := uz ▸ hs
      have v := paired_bit pz (sign_used val hits hz useZ)
      rw [←turned_word]
      exact legal_right _ ((patch_extract (turned z s) k).2.2 ▸ v)
    · rw [beq_eq_false_iff_ne.mpr ua,beq_eq_false_iff_ne.mpr uz,←turned_word]
      have v := paired_bit (gy u hu ua uz) ok
      exact legal_grey _ ((patch_extract (turned u s) k).1 ▸ v))
  rw [val,patch_target,ah,zh] at allok
  exact (by decide : allowed true true 25 ≠ true) allok

noncomputable def permEquiv {x : Word} (a : Automorphism x) : Word ≃ Word :=
  Equiv.ofBijective a.p.q ⟨a.inj,Finite.surjective_of_injective a.inj⟩

noncomputable def Automorphism.back {x : Word} (a : Automorphism x) : Automorphism x := by
  let f := permEquiv a
  have inv (w : Word) : a.p.q (f.symm w)=w := f.apply_symm_apply w
  refine ⟨⟨f.symm,?_,?_⟩,?_,?_,f.symm.injective,?_⟩
  · intro w; apply a.inj; rw [inv,a.p.neg,inv]
  · intro d u v; apply a.inj; rw [inv,a.p.bin,inv,inv]
  · apply a.inj; rw [inv,a.zero]
  · apply a.inj; rw [inv,a.one]
  · apply a.inj; rw [inv,a.fix]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Automorphism.back_q {x : Word} (a : Automorphism x) (w : Word) : a.back.p.q (a.p.q w)=w := by
  change (permEquiv a).symm (permEquiv a w)=w
  exact Equiv.symm_apply_apply ..
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Automorphism.reflect {x : Word} (a : Automorphism x) {b t S} (h : Exact x b t (S.image a.p.q)) : Exact x b t S := by
  have r:=a.back.map_exact h
  have eq : (S.image a.p.q).image a.back.p.q=S := by ext w; simp [Finset.mem_image,a.back_q]
  rwa [eq] at r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def fromOrbit {x : Word} {c : Charts x} (root : Frame c) (depth tape : ℕ) (a : Rotation root) (f : Frame c) :=
  (root.replay depth tape).any (fun g=>f.b==g.b && f.t==g.t && (bareReplay a.base depth tape).isPerm (f.v.map Wire.w))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma orbit_hit {x : Word} {c : Charts x} {root f : Frame c} {depth tape} {a : Rotation root}
    (good : ∀ g, root.replay depth tape=some g → g.No) (hit : fromOrbit root depth tape a f=true) : f.No := by
  obtain ⟨g,eg,h⟩ := (Option.any_eq_true ..).1 hit
  obtain ⟨⟨b,t⟩,pm⟩ := (Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
  have eq : (wires g.v).image a.R.p.q=wires f.v := by
    have words : bareReplay a.base depth tape=(g.v.map Wire.w).map a.R.p.q := by
      rw [a.eq,project_tape,←replay_words eg]
    ext z
    have p := (List.isPerm_iff.mp pm).mem_iff (a:=z)
    rw [words] at p
    simpa only [wires,List.mem_toFinset,List.mem_map,Finset.mem_image] using p
  intro he
  apply good g eg
  apply a.R.reflect
  rw [eq,←beq_iff_eq.mp b,←beq_iff_eq.mp t]
  exact he

abbrev Rows := Array (Array ℕ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def fetchRow (r : Rows) (i : ℕ) := ((r[i/24]?).getD #[])[Nat.mod i 24]?.getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tapeAt (r : Rows) (d i : ℕ) := Nat.mod (fetchRow r i) (2^(12*d))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Region {x : Word} {c : Charts x} (root : Frame c) (d num : ℕ) (r : Rows) :=
  ∀ j<num, ∀ g, root.replay d (tapeAt r d j)=some g → g.No

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def glimpse {x : Word} {c : Charts x} (f : Frame c) :=
  Nat.mod (f.v.foldl (fun acc w=>acc+w.w.toNat) (f.b+17*f.t)) 4093

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def linkBits {x : Word} {c : Charts x} (root : Frame c) (next : Rows) (rot : Array (Rotation root))
    (d num key : ℕ) (f : Frame c) : ℕ→ℕ→Bool
  | 0,_ => false
  | cnt+1,blob =>
    if blob=0 then false else
      (let h:=blob &&& 0xfffffff
       let idx:=h >>> 16
       h &&& 4095 == key && decide (idx<num) &&
         (rot[(h >>> 12) &&& 15]?).any (fun a=>fromOrbit root d (tapeAt next d idx) a f)) ||
      linkBits root next rot d num key f cnt (blob >>> 28)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma links_valid {x : Word} {c : Charts x} {root f : Frame c} {r : Rows} {rot} {d num key blob cnt}
    (good : Region root d num r) (hit : linkBits root r rot d num key f cnt blob=true) : f.No := by
  induction cnt generalizing blob with
  | zero => contradiction
  | succ n ih =>
    simp only [linkBits] at hit
    split at hit
    · contradiction
    rcases Bool.or_eq_true_iff.mp hit with use|go
    · obtain ⟨⟨_,idx⟩,q⟩ := (Bool.and_eq_true_iff.mp use).imp_left Bool.and_eq_true_iff.mp
      obtain ⟨a,_,h⟩ := (Option.any_eq_true ..).1 q
      exact orbit_hit (good _ (of_decide_eq_true idx)) h
    · exact ih go

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selectPrices {x : Word} (ps : List (Price x)) : ℕ→ℕ→List (Price x)
  | 0,_ => []
  | n+1,blob => if blob=0 then [] else
      (ps[(blob &&& 15)-1]?).toList ++ selectPrices ps n (blob >>> 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prices_mem {x : Word} {ps : List (Price x)} {n blob p} (h : p∈selectPrices ps n blob) : p∈ps := by
  induction n generalizing blob with
  | zero => contradiction
  | succ n ih =>
    simp only [selectPrices] at h
    split at h
    · contradiction
    rcases List.mem_append.mp h with a|b
    · exact List.mem_of_getElem? (Option.mem_toList.mp a)
    · exact ih b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shapeCut {x : Word} {c : Charts x} (f : Frame c) :=
  if f.t=0 then tightConflict f else signCut f
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_sound {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid) (h : shapeCut f=true) : f.No := by
  unfold shapeCut at h; split at h
  · exact tight_sound v h
  · exact sign_cut v h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def localClose {x : Word} {c : Charts x} (root : Frame c) (next : Rows) (rot : Array (Rotation root))
    (d num links : ℕ) (f : Frame c) :=
  f.ps.any (cheapCut f.b f.v) || shapeCut f ||
    (links != 0 && linkBits root next rot d num (glimpse f) f 100 links)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma local_close {x : Word} {c : Charts x} {root f : Frame c} {next : Rows} {rot d num links}
    (v : f.Valid) (gn : Region root d num next) (h : localClose root next rot d num links f=true) : f.No := by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · rcases Bool.or_eq_true_iff.mp h with h|h
    · exact cheap_cut v h
    · exact shape_sound v h
  · exact links_valid gn (Bool.and_eq_true_iff.mp h).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def atlasRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows next : Rows)
    (num : ℕ) (rot : Array (Rotation root)) (i : ℕ) :=
  let pack:=fetchRow rows i >>> (12*d)
  (root.replay d (tapeAt rows d i)).all (fun f =>
    let g:Frame c:={f with ps:=selectPrices f.ps 10 (pack &&& 0xffffffffff)}
    !(g.v.any (fun w=>w.w==x)) && coveredScan g (localClose root next rot (d+1) num (pack >>> 40)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma atlas_sound {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (v : root.Valid)
    (d n num : ℕ) (rows next : Rows) (rot : Array (Rotation root))
    (gn : Region root (d+1) num next) (h : Span (atlasRow root d rows next num rot) 0 n) : Region root d n rows := by
  intro i hi f ef
  have good:=Frame.replay_valid v ef
  let pack:=fetchRow rows i >>> (12*d)
  let g:Frame c:={f with ps:=selectPrices f.ps 10 (pack &&& 0xffffffffff)}
  have gv : g.Valid:=⟨good.1,fun p hp=>good.2 p (prices_mem hp)⟩
  have ck:=h i (Nat.zero_le _) hi
  simp only [atlasRow,ef,Option.all_some] at ck
  obtain ⟨none,run⟩ := Bool.and_eq_true_iff.mp ck
  intro he
  rcases descend c hx he with hm|⟨s,hs,el,nxt⟩
  · obtain ⟨w,hw,eq⟩:=Step.mem_wires.mp hm
    have found : f.v.any (fun z=>z.w==x)=true:=List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr eq⟩
    simp [found] at none
  · have ok:=covered_sound (f:=g) run gv.1 hs el nxt
    exact local_close (Frame.child_valid gv el (Step.all_legal hs)) gn ok nxt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma whole {x : Word} {c : Charts x} {root : Frame c} {r : Rows}
    (h : Region root 0 1 r) : root.No := by
  exact h 0 (by decide) root rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root_choices {x : Word} {c : Charts x} (root : Frame c) (pivot : Word) (raw : List (Wire c))
    (rv : wires root.v=insert pivot (wires raw))
    (force : ∀ a∈wires raw, ∃ i j : Fin 512, bit x i=true ∧ bit x j=false ∧
      ∀ w∈wires root.v, w≠a → bit w i=bit w j)
    (wholeNo : root.No) (rawNo : ¬Feasible x root.b root.t (wires raw)) : ¬Feasible x root.b root.t (wires root.v) := by
  rintro ⟨n,hn,j,hj,T,sub,h⟩
  have allRaw : wires raw ⊆ T := by
    intro a ha
    obtain ⟨u,v,xu,xv,only⟩:=force a ha
    obtain ⟨z,hz,d⟩:=exact_difference h xu xv
    by_contra miss
    exact d (only z (sub hz) (by rintro rfl; exact miss hz))
  by_cases use:pivot∈T
  · have eq : wires root.v=T := Finset.Subset.antisymm (rv ▸ Finset.insert_subset use allRaw) sub
    exact wholeNo ⟨n,hn,j,hj,eq ▸ h⟩
  · apply rawNo
    refine ⟨n,hn,j,hj,T,?_,h⟩
    intro w hw
    have ins : w ∈ insert pivot (wires raw) := rv ▸ sub hw
    exact (Finset.mem_insert.mp ins).resolve_left (fun e=>use (e ▸ hw))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def forcedExcept {x : Word} {c : Charts x} (v raw : List (Wire c)) :=
  let single:= ~~~(diffWords v).2
  raw.all (fun w=>(w.p &&& ~~~w.n &&& single) != 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma forced_except {x : Word} {c : Charts x} {v raw : List (Wire c)} (inc : ∀ w∈raw, w∈v)
    (ck : forcedExcept v raw=true) (a) (ha : a∈wires raw) :
    ∃ i j : Fin 512, bit x i=true ∧ bit x j=false ∧ ∀ w∈wires v, w≠a → bit w i=bit w j := by
  obtain ⟨w,hw,rfl⟩:=Step.mem_wires.mp ha
  obtain ⟨i,hi⟩:=marked_word (bne_iff_ne.mp (List.all_eq_true.mp ck w hw))
  have e : (bit w.p i && !bit w.n i && !bit (diffWords v).2 i)=true := by
    simpa only [bit,BitVec.getElem_and,BitVec.getElem_not] using hi
  obtain ⟨⟨pi,nn⟩,unique⟩:=(Bool.and_eq_true_iff.mp e).imp_left Bool.and_eq_true_iff.mp
  have wn : bit w.n i=false := by simpa using nn
  have dif : bit (w.p ^^^ w.n) i=true := by simp only [bit,BitVec.getElem_xor] at *; simp [pi,wn]
  refine ⟨c.p i,c.n i,c.hp i,c.hn i,?_⟩
  intro z hz ne
  obtain ⟨q,hq,rfl⟩ := Step.mem_wires.mp hz
  rw [←q.hp i,←q.hn i]
  by_contra bad
  have dd : bit (q.p ^^^ q.n) i=true := by
    rw [show bit (q.p ^^^ q.n) i=(bit q.p i ^^ bit q.n i) from BitVec.getElem_xor _]
    cases h : bit q.p i <;> cases k : bit q.n i <;> simp_all
  have since := (df_bit v i).2 q hq w (inc w hw) ne dd dif
  simp [since] at unique

-- Prove induced graph bounds in order, using previously proved smaller restrictions.
def paddedSamples (data count last : Nat) : Nat :=
  data + ((last * ((2 ^ (9 * (512 - count)) - 1) / 511)) <<< (9 * count))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0X : Word := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0C : Charts g0X := ⟨unpack (paddedSamples 0x0 0 3),unpack (paddedSamples 0x401 2 1),by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0W0 : Wire g0C := ⟨inputColumn0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0W1 : Wire g0C := ⟨inputColumn1,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,2,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0V := [g0W0,g0W1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g0proper : proper g0X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g0nd : (g0V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g0bound : ¬Feasible g0X 0 1 (wires g0V) := by
  apply full_raw (positive_checked (v:=g0V) (by decide +kernel))
  intro h
  have total := exact_size h
  have count : (wires g0V).card=2 := by decide +kernel
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1X : Word := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1C : Charts g1X := ⟨unpack (paddedSamples 0x1c0c06030140a05 7 5),unpack (paddedSamples 0xc0803010100601 7 1),by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1W0 : Wire g1C := ⟨inputColumn0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd3,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1W1 : Wire g1C := ⟨inputColumn1,0x78,0x5a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1W2 : Wire g1C := ⟨inputColumn2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x24,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1V := [g1W0,g1W1,g1W2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g1proper : proper g1X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g1nd : (g1V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g1bound : ¬Feasible g1X 1 1 (wires g1V) := by
  apply full_raw (positive_checked (v:=g1V) (by decide +kernel))
  intro h
  have total := exact_size h
  have count : (wires g1V).card=3 := by decide +kernel
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2X : Word := 0xfca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2C : Charts g2X := ⟨unpack (paddedSamples 0xe06830180c06030160b05028140a0501c0e05028140a05 21 5),unpack (paddedSamples 0x60482410060200c1203048200c03010180609030100601 21 1),by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2W0 : Wire g2C := ⟨inputColumn0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8307f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec7933,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2W1 : Wire g2C := ⟨inputColumn1,0x103fe0,0x1153ea,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2W2 : Wire g2C := ⟨inputColumn2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07f,0x11824c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2W3 : Wire g2C := ⟨inputColumn3,0x1fff80,0xe2c10,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2V := [g2W0,g2W1,g2W2,g2W3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2proper : proper g2X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2nd : (g2V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2f0 : Basis g2X := basisFor g2X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g2V.map Wire.w) 2 (assignRows [9,0,1,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2f0valid : (Price.mk g2f0 0).Valid 1 (wires g2V) :=
  initial_price g1proper g1bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2f1 : Basis g2X := basisFor g2X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g2V.map Wire.w) 2 (assignRows [0,9,2,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2f1valid : (Price.mk g2f1 0).Valid 1 (wires g2V) :=
  initial_price g1proper g1bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2f2 : Basis g2X := basisFor g2X 0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505 (g2V.map Wire.w) 1 (assignRows [9,0,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2f2valid : (Price.mk g2f2 0).Valid 1 (wires g2V) :=
  initial_price g0proper g0bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2f3 : Basis g2X := basisFor g2X 0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033 (g2V.map Wire.w) 1 (assignRows [0,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2f3valid : (Price.mk g2f3 0).Valid 1 (wires g2V) :=
  initial_price g0proper g0bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2prices : List (Price g2X) := [⟨g2f0,0⟩,⟨g2f1,0⟩,⟨g2f2,0⟩,⟨g2f3,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2valid : ∀ p ∈ g2prices, p.Valid 1 (wires g2V) := by
  intro p hp
  simp only [g2prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact g2f0valid
  · exact g2f1valid
  · exact g2f2valid
  · exact g2f3valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g2bound : ¬Feasible g2X 3 1 (wires g2V) := by
  apply verified g2C g2proper g2nd g2valid
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3X : Word := 0xfff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3C : Charts g3X := ⟨unpack (paddedSamples 0x381a0c86430180c06030180c0582c150a05028140a0502813098381c0d0682c140a05028140a0501c0a05028140a050280c06030180c0603 50 3),unpack (paddedSamples 0x1812088242411080301208030480c1109044200c048180812088300c0c048242411060241006010182411060240c0400848220c048180401 50 1),by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W0 : Wire g3C := ⟨inputColumn0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc01019c07fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcd21488d414a9,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W1 : Wire g3C := ⟨inputColumn1,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd00601e7fc07f,0x120e85221e246,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W2 : Wire g3C := ⟨inputColumn2,0x2007fe7807f80,0x204a167094b14,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W3 : Wire g3C := ⟨inputColumn3,0x3ff8007ff8000,0x2470185ce0c18,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W4 : Wire g3C := ⟨inputColumn4,0x3fffff8000000,0x1b85e18303060,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3V := [g3W0,g3W1,g3W2,g3W3,g3W4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3proper : proper g3X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3nd : (g3V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f0 : Basis g3X := basisFor g3X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g3V.map Wire.w) 4 (assignRows [9,0,1,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f0valid : (Price.mk g3f0 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f1 : Basis g3X := basisFor g3X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g3V.map Wire.w) 4 (assignRows [0,9,2,1,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f1valid : (Price.mk g3f1 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f2 : Basis g3X := basisFor g3X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g3V.map Wire.w) 4 (assignRows [0,2,9,3,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f2valid : (Price.mk g3f2 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f3 : Basis g3X := basisFor g3X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g3V.map Wire.w) 4 (assignRows [2,0,3,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f3valid : (Price.mk g3f3 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f4 : Basis g3X := basisFor g3X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g3V.map Wire.w) 4 (assignRows [2,3,0,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f4valid : (Price.mk g3f4 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3prices : List (Price g3X) := [⟨g3f0,0⟩,⟨g3f1,0⟩,⟨g3f2,0⟩,⟨g3f3,0⟩,⟨g3f4,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3valid : ∀ p ∈ g3prices, p.Valid 1 (wires g3V) := by
  intro p hp
  simp only [g3prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact g3f0valid
  · exact g3f1valid
  · exact g3f2valid
  · exact g3f3valid
  · exact g3f4valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3bound : ¬Feasible g3X 6 1 (wires g3V) := by
  apply verified g3C g3proper g3nd g3valid
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8X : Word := 0xffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8C : Charts g8X := ⟨unpack (paddedSamples 0x72381a0cc6432188c06030180c06030168b0582a148a05028140a05028130984a251188c4221108844221108743a1c0e06c361a0d05c2c150a85028140a050281407838160b05028140a050281407038180c06030180c06 78 6),unpack (paddedSamples 0x32181204c44120889044200c84c200d0689018220489044200c84c1a081208848051100c482210064260d008641a180606426180904c2411028904419098401a04068301203120883213068200405018904419098340802 78 2),by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W0 : Wire g8C := ⟨inputColumn0,0x24808803ffe6580b0180,0x248d88e147e659ab399c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W1 : Wire g8C := ⟨inputColumn1,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc700100cc007e00fffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7241244d202e28152a9,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W2 : Wire g8C := ⟨inputColumn2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc800e00f00787ffc01ff,0x841e42b21280c3c8946,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W3 : Wire g8C := ⟨inputColumn3,0x3000fff0007f800ffe00,0x3009a8b0057d012e2c14,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W4 : Wire g8C := ⟨inputColumn4,0x3fff0000007ffff00000,0x358e00c00657f1c03018,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W5 : Wire g8C := ⟨inputColumn5,0x3fffffffff8000000000,0xa70570eb8000600c060,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8V := [g8W0,g8W1,g8W2,g8W3,g8W4,g8W5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g8proper : proper g8X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g8nd : (g8V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8f0 : Basis g8X := basisFor g8X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g8V.map Wire.w) 7 (assignRows [9,0,1,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g8f0valid : (Price.mk g8f0 0).Valid 1 (wires g8V) :=
  initial_price g3proper g3bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g8bound : ¬Feasible g8X 7 1 (wires g8V) := by
  apply full_raw (positive_checked (v:=g8V) (by decide +kernel))
  exact cut_sound g8nd g8f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11X : Word := 0xfffffffffffffcccfffaffaaf0f0f000fffffffffffffcccfffaffaaf0f0f000fffffffffffffcccfffaffaaf0f0f000fffffffffffffcccfffaffaaf0f0f000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11C : Charts g11X := ⟨unpack (paddedSamples 0xe470349a0cc6532190c46130180c06030180c0602d968b2592c160aa5429948a25128140a05028140a05026934984c2592c944a2391c8c462190c844221108844221108763a1d0e470381b0d86834198cc6231170b0562a150a45028140a05028140a04e271289446231088442211088442210f8783a1c0b85c2c160a85428140a05028140a0501e0f070381a0d06030180c06030180c 134 12),unpack (paddedSamples 0x6430249204c452209044412491480321308036070d8689219240608a440984882112491480321306c20072491490442482c900a2281c88062080c9245200c84c1b0380836320d06460181909860241904c601113090162205024924519098401b0401c4c071201444032491464261006c0e010d86832180981c24060881492451909836100381016070501812052491464260d8200e04 134 4),by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W0 : Wire g11C := ⟨inputColumn0,0x9100b2b00cccc0240f2403fffacc03300,0x91c3b2bc5cccf1a40527155c7acf2b3ca,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W1 : Wire g11C := ⟨inputColumn1,0x22200c0c000fffff8ccb803300cf003c00,0x2221bc0c1d05547f8ccb8d7336cf0ebc3a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W2 : Wire g11C := ⟨inputColumn2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3c0003000f0f0000f0c003c00ffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3c490304950f128050c147c520554d553,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W3 : Wire g11C := ⟨inputColumn3,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc000fc000ff0003f00fffc000f0003fff,0xc082fc084af0212d002e18084f0222a8c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W4 : Wire g11C := ⟨inputColumn4,0x30000fffff000003fff0000000ffffc000,0x30012d4d16000053faf0090024fa8b0028,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W5 : Wire g11C := ⟨inputColumn5,0x3ffff00000000003ffffffffff00000000,0x3261c000180000612fad0e2a38000c0030,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W6 : Wire g11C := ⟨inputColumn6,0x3ffffffffffffffc000000000000000000,0xd9e02b2e0faab8000003000c0003000c0,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11V := [g11W0,g11W1,g11W2,g11W3,g11W4,g11W5,g11W6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g11proper : proper g11X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g11nd : (g11V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11f0 : Basis g11X := basisFor g11X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g11V.map Wire.w) 8 (assignRows [9,0,1,2,3,4,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g11f0valid : (Price.mk g11f0 0).Valid 1 (wires g11V) :=
  initial_price g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g11bound : ¬Feasible g11X 8 1 (wires g11V) := by
  apply full_raw (positive_checked (v:=g11V) (by decide +kernel))
  exact cut_sound g11nd g11f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13X : Word := 0xfffffffeffffffccfffffafaf888f888fffffffeffffffccfffffafaf888f888fffffffeffffffccfffffafaf888f888fffffffeffffffccfffffafaf888f888
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13proper : proper g13X := by decide +kernel

-- The seven remaining vertices, in the order of this word's input columns,
-- are 1, 6, 7, 5, 3, 2, 8 of the original graph.
open PEqualNP.Outside.L_meta_3024.Theta in
def thetaRead (w : Word) (x : Om) : Bool :=
  bit w ((if x 1 then 1 else 0) + (if x 6 then 2 else 0) +
    (if x 7 then 4 else 0) + (if x 5 then 8 else 0) +
    (if x 3 then 16 else 0) + (if x 2 then 32 else 0) + (if x 8 then 64 else 0))

open PEqualNP.Outside.L_meta_3024.Theta in
lemma thetaLive {x : Word} {b t : ℕ} {S : Finset Word} (h : Live x b t S) :
    ∀ (W : Set (Om → Bool)), (∀ a ∈ S, nrm (thetaRead a) ∈ W) →
      Der opF b W (nrm (thetaRead x)) := by
  induction h with
  | done =>
    intro W hw
    exact .here (hw _ (Finset.mem_singleton_self _))
  | @unary b t U a _ _ _ ih =>
    intro W hw
    apply ih W
    intro w hw'
    rcases Finset.mem_insert.mp hw' with rfl | hu
    · have e : thetaRead (~~~a) = fun x => !thetaRead a x := by
        funext x
        exact bit_not a _
      rw [e, nrm_not]
      exact hw _ (Finset.mem_insert_self ..)
    · exact hw _ (Finset.mem_insert_of_mem hu)
  | @binary b t U a c d _ _ _ _ _ ih =>
    intro W hw
    obtain ⟨j, he⟩ := nrm_bin d (thetaRead a) (thetaRead c)
    have e : thetaRead (combine d a c) = fun x =>
        if d then thetaRead a x || thetaRead c x else thetaRead a x && thetaRead c x := by
      funext x
      exact bit_bin d a c _
    refine .step j (nrm (thetaRead a)) (nrm (thetaRead c))
      (hw _ (Finset.mem_insert_self ..))
      (hw _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))) (ih _ ?_)
    intro w hw'
    rcases Finset.mem_insert.mp hw' with rfl | hu
    · left
      exact (congrArg nrm e).trans he
    · right
      exact hw _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

def thetaInputs : List Word :=
  [inputColumn0,inputColumn1,inputColumn2,inputColumn3,inputColumn4,inputColumn5,inputColumn6]

open PEqualNP.Outside.L_meta_3024.Theta in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g13bound : ¬ Feasible g13X 10 1 thetaInputs.toFinset := by
  rintro ⟨b,hb,_,_,S,hS,hl⟩
  let W : Set (Om → Bool) := {F | ∃ i : Fin 7, F = nrm (thetaRead (thetaInputs.getD i.val 0))}
  have h := thetaLive hl W (by
    intro w hw
    have hcol : w ∈ thetaInputs := List.mem_toFinset.mp (hS hw)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcol
    exact ⟨⟨i, by simpa [thetaInputs] using hi⟩, by simp [List.getD_eq_getElem?_getD,hi]⟩)
  have ht := (h.le hb).map (op' := opN) encF encF_op
  have out : encF (nrm (thetaRead g13X)) = LO := by
    apply encF_eq (bdd_of_lt LO_lt)
    decide +kernel
  rw [out] at ht
  apply theta (ht.mono ?_)
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  right
  let j : Fin 7 := [0,4,5,3,2,1,6].getD i.val 0
  refine ⟨j, encF_eq (bdd_of_lt (ip_lt j)) ?_⟩
  dsimp [j]
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16X : Word := 0xfffffffffffffffcfffffffffffff0f0ffffffffffccffccffeaeaeaffc0c0c0fffffffffffffffcfffffffffffff0f0ffffffffffccffccffeaeaeaffc0c0c0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16C : Charts g16X := ⟨unpack (paddedSamples 0x385c0d56a345a2d06832d94c964b2190c562b1188c361b0984b4592c158ab552a952a85429146a25128540a05028140a05028140a05026d34994c255289349a49249148a41209048241209048241209047a391a8d462310e8642a150884422110884422110884421d4e874391c4e070361a8d06532190c46130180c06030180c06030180c05d2e164b0572b14ca652291349a4c2612c944924920904824120904824120904823918864321108844221108844221108843c1e0e874381c0d86c351a8cc6631188b85c2d168ac5629148984c251288c4621108844221108844221108843a1d0e070361b0d06832190c06030180c06030180c06030170b8582c0f078381c07038180c06030180c06030180c06 243 6),unpack (paddedSamples 0x30580552a304a2c02822d14c144b0110c122b0088c141b010434190c0588b450a9128814091068211205828b401546832160a8401306a2d148944054288309a08248108b0516802a8d0642c1504c200d45a29120d44031068240815828b401546832160a8260d02154a83419144a030160a8504522090444160a2caa401a0c8582a1004c1a552a144a0552a1442650091141a440602c144104b051655200d0642c1504c1a0822910820360a2caa401a0c8582a098340434160c85430140d064340a8c82630088b0542c068a816280489044240288806c1459546832160a84013068042a0d0a030260b09028220960a2caa34190b0541308034101509850240d05830140501b0516551a0c8582a098340802 243 2),by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W0 : Wire g16C := ⟨inputColumn0,0x565998122400559800b2c0044110015665800b00001f9f9ffff3300199800,0x565998122741d59e85b2f434411e075665f06be0c00a8a8bc1f33e1599f0c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W1 : Wire g16C := ⟨inputColumn1,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80601e9c380061e000c300008420001f86000fffe66666660003c001fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80600a9c391561e22cc31160842454028622c145a62626269503c4b0aaa59,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W2 : Wire g16C := ⟨inputColumn2,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9801e1204000060000ffffff09c0019878000c0018787878003c0001fffff,0x1800a12040688600d114469f09c2a39878152c2a5858585868bc0345551a6,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W3 : Wire g16C := ⟨inputColumn3,0x7e003f8000780000fc00000e0001e07ffff0001f807f80003ffffe1e000,0x6a003f810cf80219fc10d00e0432002ea1b0434a807f808c9554661e234,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W4 : Wire g16C := ⟨inputColumn4,0x1f8001c000007fffff000007f00001ff800000001fff8000003fffffe0000,0x1a8001c0007106a8e6000727f002c5ff8016402c957f8000712aa399e01c8,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W5 : Wire g16C := ⟨inputColumn5,0x600001ffffff800000000007fffffe00000000001fffffffffc0000000000,0x1e4c83e0000780003c19e60f8000007800f1ff575743e0001e0000f0,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W6 : Wire g16C := ⟨inputColumn6,0x7ffffe000000000000000007ffffffffffffffffe00000000000000000000,0x7f95f4000240000480002406619b01fd51580eb00000000140000a0000500,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W7 : Wire g16C := ⟨inputColumn7,0x7ffffffffffffffffffffff80000000000000000000000000000000000000,0x657f5e1b3780795700ebb800000c0000006000c00000000180000c0000600,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16V := [g16W0,g16W1,g16W2,g16W3,g16W4,g16W5,g16W6,g16W7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16proper : proper g16X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16nd : (g16V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16f0 : Basis g16X := basisFor g16X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g16V.map Wire.w) 11 (assignRows [9,0,1,2,3,4,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16f0valid : (Price.mk g16f0 0).Valid 1 (wires g16V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g16bound : ¬Feasible g16X 11 1 (wires g16V) := by
  apply full_raw (positive_checked (v:=g16V) (by decide +kernel))
  exact cut_sound g16nd g16f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17X : Word := 0xfffffffffffffffcfffffffafffffff0ffffffffffeeffccfefefafaeeee0000fffffffffffffffcfffffffafffffff0ffffffffffeeffccfefefafaeeee0000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17C : Charts g17X := ⟨unpack (paddedSamples 0x1c4e170381a8d16834192c862b1588c461b0d84c25c2c960b0552a950a85329146a350a8538984a24d249148241209048241209048241208f47235188b45a29148944a21108844221108844221108843a1d0c8642a150884422110884422110884421e0e870381a8d06532188c26030180c06030180c06030180b85c2c160ac552a948a251279389a4d26130964a2492490482412090482412090482411c8e462310c864221108844221108844221108783c1d0e872341a0c86431178b85c2d160b0562b148a44e261309448241209048241209048241208c4621108844221108844221108843e1e0f0743a1b0d06832190b8582c150a84c241209048241209048241209044221108844221108844221130109202130240c04848108c084090902242288d120a81a044229012220484844048b0321a2a090324228448c244108241210a2022515404588214204490242421084a108890b0241908424210889024211238108e02404884c20892042d058285a0e048085108438340241110b10e07058044841110a108451 350 81),unpack (paddedSamples 0x144c160280a8c16014182c060915804460a0d80821c2894030510a940285128144835020438180a20d048160a8906802a114702a0e0401e0f07034188305a08148104b054483401508a38150701e084181d04064081582a241a00a8451c0a8380f020e0a850180a850452208882c15120ca845200e054200e03ca81c28060a85422940a041078388a0d22030160a2082582a2419508a401c0a8380f041140e440310406c15120ca845200e0541c07808701c1c0a870300a0c04430078a81c0d14030540b140240e220301582a2419508a3815080380f0208806c15120ca8451c0a8401c078041e1c070701a0b0c0283009038500c140280d82a2419508a3815070200f0130544832a114702a0e0401e016020c608350300601850208a045150508a8322850a0280e11482a02a0a0381c1508830a20a0a030221030100a02004080c00810040c018280a0c02808100801814020101030060505004080101020080500a28088c00c08904822082102505020580a040204504428300048120910a030180040481008100441 350 65),by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W0 : Wire g17C := ⟨inputColumn0,0xffffffffffffffffffffffffffffffffffffffffd12cc003c500159800cc000120001bb2c00660002193e4007ffe739c007ff10028600040b54185900a441859,0xffffffffffffffffffffffffffffffffffffffffd12cc00145a4359d22ce9101350409b2ea167508009166a1350e318ea154350138600000000000000a441859,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W1 : Wire g17C := ⟨inputColumn1,0x2000f4cb060019e000f00004400024c30007fffcc6e3380060039ce7ff8004049000511700020a2070002022,0x200054cb066139e30af185044c2400c31852ac2c42e339896c4a94a589b125049000d1000000000070002022,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W2 : Wire g17C := ⟨inputColumn2,0x20f000c28001e0000ffffa1800338fc0007800318fc3fff8003e0f800000001448a08a00294504a00010404,0x2050000280cbe00665433a1830f38fc0637831908b42c63831be0f8650ca0016ccb08000000000a00010404,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W3 : Wire g17C := ⟨inputColumn3,0x3008f030001fffff0000460003c0fffff80003e0ffc0000003ff00000000100105a6084828200084020000,0x8503003bea81f000f46006d40d740f8007be0ffc01b00dbff001d03a0108187a6000000000084020000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W4 : Wire g17C := ⟨inputColumn4,0xffffffffffffffffffffffffffffffffffffffffc3c00f003fffe000000000780003ff0000000003ff0000000003fffffffff248aef079033440aaa049a8f3d1,0x2400900380ac00054002a78024bf60004a00253bd00005202914a50560ac232468b2a048a8f351881008380,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W5 : Wire g17C := ⟨inputColumn5,0x3c000fffc00000000000007ffffc000000000003fffffffffffc0000000009a2458a1d6089115d5d02d48b88,0x24000ffe8043000218010c4e4870000010c00862f74a911c48e00001182302a88114d5902c48a88440920180,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W6 : Wire g17C := ⟨inputColumn6,0xfffffffffffffffffffffffffffffffffffffffffffff000000000000000007ffffffffffffffffc000000000000000000000cb618012214122a2005b530c723,0xffffffffffffffffffffffffffffffffffffffffdbffa000008c000460023031b382bf28a70553800000026013000002604c08432a68004b538452330921ce01,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W7 : Wire g17C := ⟨inputColumn7,0x3fffffffffffffffffffff800000000000000000000000000000000000000249031484d84a85000711fb4484,0x3dbaf6afc7f0015780abc0001c00000038001c00000003801c00000380700dcc101010711530484532fc5010,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17V := [g17W0,g17W1,g17W2,g17W3,g17W4,g17W5,g17W6,g17W7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17proper : proper g17X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17nd : (g17V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f0 : Basis g17X := basisFor g17X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g17V.map Wire.w) 11 (assignRows [9,0,3,4,1,2,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f0valid : (Price.mk g17f0 0).Valid 1 (wires g17V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f1 : Basis g17X := basisFor g17X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g17V.map Wire.w) 11 (assignRows [0,9,4,3,1,5,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f1valid : (Price.mk g17f1 0).Valid 1 (wires g17V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f2 : Basis g17X := basisFor g17X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g17V.map Wire.w) 11 (assignRows [0,4,9,3,5,1,6,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f2valid : (Price.mk g17f2 0).Valid 1 (wires g17V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f3 : Basis g17X := basisFor g17X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g17V.map Wire.w) 11 (assignRows [4,0,3,9,5,6,1,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f3valid : (Price.mk g17f3 0).Valid 1 (wires g17V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f4 : Basis g17X := basisFor g17X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g17V.map Wire.w) 9 (assignRows [0,1,3,4,9,5,6,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f4valid : (Price.mk g17f4 0).Valid 1 (wires g17V) :=
  initial_price g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f5 : Basis g17X := basisFor g17X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g17V.map Wire.w) 9 (assignRows [0,3,1,4,5,9,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f5valid : (Price.mk g17f5 0).Valid 1 (wires g17V) :=
  initial_price g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f6 : Basis g17X := basisFor g17X 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff (g17V.map Wire.w) 9 (assignRows [3,0,4,1,5,2,9,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f6valid : (Price.mk g17f6 0).Valid 1 (wires g17V) :=
  initial_price g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f7 : Basis g17X := basisFor g17X 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff (g17V.map Wire.w) 9 (assignRows [3,4,0,1,2,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f7valid : (Price.mk g17f7 0).Valid 1 (wires g17V) :=
  initial_price g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17prices : List (Price g17X) := [⟨g17f0,0⟩,⟨g17f1,0⟩,⟨g17f2,0⟩,⟨g17f3,0⟩,⟨g17f4,0⟩,⟨g17f5,0⟩,⟨g17f6,0⟩,⟨g17f7,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17valid : ∀ p ∈ g17prices, p.Valid 1 (wires g17V) := by
  intro p hp
  simp only [g17prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact g17f0valid
  · exact g17f1valid
  · exact g17f2valid
  · exact g17f3valid
  · exact g17f4valid
  · exact g17f5valid
  · exact g17f6valid
  · exact g17f7valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17frame : Frame g17C := ⟨12,1,g17V,g17prices⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17vframe : g17frame.Valid := ⟨g17nd,g17valid⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto0 := autoFor g17X (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot0 : Rotation g17frame := ⟨g17auto0,[g17W0.w,g17W1.w,g17W2.w,g17W3.w,g17W4.w,g17W5.w,g17W6.w,g17W7.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto1 := autoFor g17X (assignRows [0, 2, 1, 3, 5, 4, 7, 6, 8]) (assignRows [0, 2, 1, 3, 5, 4, 7, 6, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot1 : Rotation g17frame := ⟨g17auto1,[g17W0.w,g17W2.w,g17W1.w,g17W3.w,g17W5.w,g17W4.w,g17W7.w,g17W6.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto2 := autoFor g17X (assignRows [1, 0, 3, 2, 4, 6, 5, 7, 8]) (assignRows [1, 0, 3, 2, 4, 6, 5, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot2 : Rotation g17frame := ⟨g17auto2,[g17W1.w,g17W0.w,g17W3.w,g17W2.w,g17W4.w,g17W6.w,g17W5.w,g17W7.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto3 := autoFor g17X (assignRows [1, 3, 0, 2, 6, 4, 7, 5, 8]) (assignRows [2, 0, 3, 1, 5, 7, 4, 6, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot3 : Rotation g17frame := ⟨g17auto3,[g17W1.w,g17W3.w,g17W0.w,g17W2.w,g17W6.w,g17W4.w,g17W7.w,g17W5.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto4 := autoFor g17X (assignRows [2, 0, 3, 1, 5, 7, 4, 6, 8]) (assignRows [1, 3, 0, 2, 6, 4, 7, 5, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot4 : Rotation g17frame := ⟨g17auto4,[g17W2.w,g17W0.w,g17W3.w,g17W1.w,g17W5.w,g17W7.w,g17W4.w,g17W6.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto5 := autoFor g17X (assignRows [2, 3, 0, 1, 7, 5, 6, 4, 8]) (assignRows [2, 3, 0, 1, 7, 5, 6, 4, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot5 : Rotation g17frame := ⟨g17auto5,[g17W2.w,g17W3.w,g17W0.w,g17W1.w,g17W7.w,g17W5.w,g17W6.w,g17W4.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto6 := autoFor g17X (assignRows [3, 1, 2, 0, 6, 7, 4, 5, 8]) (assignRows [3, 1, 2, 0, 6, 7, 4, 5, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot6 : Rotation g17frame := ⟨g17auto6,[g17W3.w,g17W1.w,g17W2.w,g17W0.w,g17W6.w,g17W7.w,g17W4.w,g17W5.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto7 := autoFor g17X (assignRows [3, 2, 1, 0, 7, 6, 5, 4, 8]) (assignRows [3, 2, 1, 0, 7, 6, 5, 4, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot7 : Rotation g17frame := ⟨g17auto7,[g17W3.w,g17W2.w,g17W1.w,g17W0.w,g17W7.w,g17W6.w,g17W5.w,g17W4.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot := #[g17rot0,g17rot1,g17rot2,g17rot3,g17rot4,g17rot5,g17rot6,g17rot7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows0 : Rows := #[
 #[0x4802004325000162ed00021e700417a000140610030ebb0021f5e0000f200031b4e002009700407300012ad00042d1e00107a60001b3c0000004321]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows1 : Rows := #[
 #[0x13faf00c304f01465020180c1d02118b00150df6001649200c68320143a8001f2dc000a5e4f01710df00e1cc001d256d00417fa01f750800a03d0017465d000006432100c,0xc2de7008683501e08d200c47cc025678e0022337002475d0263fe9000064321524c,0x1520bd0221d910230e340150df601674fa0165fc90162e4e016015c00b2c7e019389200b05070191e5401306fb000084321525c,0x2154ff0002f4a0182ee1000049d0180c1d01b084b0221d91000742d0005a1b0200b8a00f4e8c007597f01c4c8102108390205a7800f1d7a0070dcb01c10d001a05d201018d400007643212d8,0x10d7100627bf01203d3014175600d2d0f00825d0000742d00503ff00f4e8c02446820115112001649200010c0006129001247f901470ae005627000f0cfd0245f2f01149bf00905d200310620000753412258]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows2 : Rows := #[
 #[0x5a18de092094a00258de0884d7905e18de0987eb304f0cec00000006312d8368,0x5b4a14003535304954d002c475308c5e3a050334100d7e9d0070c4300b05f101d1c110150f2d0191c4702f757302e100306f2570004548e01c3f1b0007583412258012,0x4776e004068ad0770e550060ab40672dfe02765d106856f10000347251254066,0x85008100945d104f0cec04f697f064056107609010856b4f0480c420703dff05f55cc012778904860b2070226f05f480701219c407c1b2004e0cdd00006843212e0001,0x8a1da30720e4603616180363c060532b680530af608e1b3c000054321800a062,0x34672e0354d2e0900e710000000012258328,0x3235be092094a01e09af0326dd8031550603105060880fb4065150608530530856b4f0000003142250368,0x8657fd03f0eb900f07e400003be00000000212d8064,0x405d8c04036480a0082c0773f670763b9d069600500000000172503e4,0x3d527500c0bb10354d2e0336fb103d469b0355b9f033086100e5dd10805cec00e45240804e7b06148c10892a0e0000573412258002,0x76ea8093358c0967ca700a350807372df0140149000042315600c04c,0x24152d0782b510251bf409912690233bb607b0d2c0521d8103e35d10660289000053182425c056,0x300a6a04776e0067338f0105fb102d02d006000040008743215254012,0x373f10036dd303235be0322cdc03b1f0b0031b0f0325f30032488803b049c003072b0a30ed8055209200c26610643b0000c313206420a200000032412503e8,0x194aa1087748b0196ff1039170f03847b208754b7000084321500a066,0x5033410170d2308b09fa0a30ed807e26920491a5f050667b04b15d10463a900000003142258066,0x983cd009812230a2093e06e09e104c05d109861b309847a108f19110442e7c03c3df009b035e08f391d0440e8803c10ab09b26160000584321260001,0x81738501a0d670316c7005a338e0055b4002c16bf0840da30655c7007d0e9f05e338e0831a4c0000043216360323,0x5b4a1403209b203b3be108c11350325f3003b049c01f392105b1d4e01f6e010453e01045692107d189103d527503d075500005831422583e6,0x2913f8091049b0412d9602829aa041061f0280f6c000084321525c001,0x1e40a201713be0815611003535305b629105015f901a3a7e0562a4d036634e00006412382e0012,0x79725c01b3d2b0792bb001b6ebb02439e009c05f409912690233bb60382b9607216d00a13160000684321525c00e,0x7901820510e5606a4ef901b6ebb02057b209e414f03a753504a5690037530f000004328525c0a5,0xb592b015726a02d7b2802b261805677e8082612f07a79cd095071e0574aa0000054321700a05a],
 #[0x502bee00149e302b4dd902b135a0507adc0011e2f000074321600c360,0x9c416d06d474507100e005d0b3a00006432172d42a5,0x2a45a300f539802a149100f07e404344e20225d6904310960220e7b00006742312d8002,0x8b09fa08b481c0a2093e08b170a0a30ed8021182b02104be09a0b2d0a212640000064321260360,0x15a3c002609e05c0f95054115d002357e05e057e0010d7605e509e06b039500000432172603a3,0x9607610965c410742ae107473d9000031426700e054,0x5838ba05822b404d0ef206201180626a8a000000000524c3e4,0xd68f20185b7a0167ca001d5e7001068f80971b33000084213700e066,0x3f5eb902a45a302645ff00000000212d82a8,0x17480a039170f08a1da3016314b0161e1e09442fd09f55ff0085d7306300e507553e704906f80540a4b000765421300a360,0x7844b9051679e051485605137a00511fd606e09e1078183007b1dd802901c1000000000626035c,0x2509ff06a329a06a5ce406a1d6906a7d9c06a6bee06a0ce606a4ef906a251f02536320251bf40590457091049b0255d760911707000000000525c35c,0x1f3921034524e013042e0335527045692109d3c4d06c367b00000000043602a4,0x4271f007f7c2b0303a2e0a0082c05822b404260d007f6132030564a08d230f000007432835c0a5,0x694ca0062404301134dd0112a0300008431262dc001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows3 : Rows := #[
 #[0xce5f9700000000002d8064001,0x5700a2e8423,0x250360321,0x400a2d8470,0x7e392a000000000400a3e80a2,0x7f61cc0000000000258323066,0xf29ed0534cd70000000005254066323,0x8258012063,0x2d801202b,0xa66aa200000001562500012d8,0x3d2f970ce5f970000000008010054066,0x9956ba08903c10000387142258012061,0x931fed00000000002580023f0,0x6e2af5000000005300a056368,0x706ca302065d00000000485360002056,0x5417e300000000082d80020ea,0x32c2f000000035700a0563e4,0x90250a0196ee6000871432535c00104a,0x4c115a0250cf606e63a102813260000043126258001052,0x86072000000000043602a4225,0x8133050966a20000004213600c04c045,0x9979460c70cfd0324b8509f3b6005718f9000000002625801205a,0x166ed90254ed9000000002626000e056,0xce38ff0000000042258066010],
 #[0x5b450106e63a1000031742600e04e052,0x5f471d03f771d00000000372e001005e,0x1b2dc9000000006700e3e83a3,0x3b132804839bc08478cd08a6e0c00000763212d4225010,0x8c1c080d14e010804e7a03f282f06e63a10000654312250010029,0x924e610071bd500000003172e0010056,0xbf2bb5000000000625000e3ee,0x2502de322,0x107fc70771138000000000225c1a5058,0x26036002a,0xb43e7a0b41e7a0881bfb0883bd30804e7a00000000052d8002052,0xa403ba0a24a4e00007432162d4066011,0x60004308f06d70384db40ad1ff600000000002d42a7012,0x9a1e6209a393400c07b900c2ac409e11fd09e37bf0154066000000000025c35c325,0x9142000944200066cd2006336a00000000072603a8001,0x5254056002,0x6b3409000685432125c001051,0x9d5a7e09d07070510029000004321626035c001,0xb505d0000000042726000242f,0xb45fa300e7e960802fa3000000000600a0522e8,0x9c11000c21bb404435f3000000000500c3e8323,0x356c2600a3e980b87f000437877000000000525401205a,0xc6258a00000421372e001002d,0x300a3680a6],
 #[0x3790a0356c260580e78005092900000754212541a5010,0x250062367,0x25836846e,0xb31733086585f07d0c9d07a086000000000082580020ea,0x2580640ed,0x2065d00406ae1000000042536000232f,0x6d2d680801d68000000003700c05a368,0x6675240465d9807b1dfd0174783000008542125c1a5002,0x3b02c00563d8f03b5c140566f1f0a416580601c1a000000007525c01005e,0x423408000000000626000e066,0x9824f80654106000000000025c225058,0x105fa00000000032502de3e6,0xab18d2013462501365fd00000000002d800104c,0xb34c130706ca302e21b700000000782583e6002,0x62d4066002,0x2d80640ed,0x5254056366,0x9d1c6909b1648000854321625c001052,0xb7078c04f448e000000000024c225058,0xb525d0000000000626000205e,0x2f7db702f23380d205b100d0e6f0008543216260001056,0xb353dc000000000125005c325,0x87568403041fa07a4cec07a6fb0054439702c2a77068732402c0b71068541e000000432125005e001,0x600a364327],
 #[0xa36fed069293000000000002e0001060,0x3654710ae1433000000004300a36006e,0x74581f02625f70526a150980fc70086ba107134f6000000000325c1a504c,0xb515d002055d002075d0076611f076438e00000000432d8066002,0x582600012e8,0xd52899000000000024c3e40a5,0x673d6c0a622bf02149da021566d0ac224f0c115ef067283d0a7363108b195f0a72d0908b792f00000862142e000103d,0x9071002149da00000000872d8368001,0x227a8e000000002125005e010,0x4b786f000000000025c0a52d8,0xc01e5206259e906275d60346c7903443a40c038900c5001b00000000062d42a7062,0x6d6fa30802fa30b25ef50491199000052841300a062056,0x114b9d000000000800a36006a,0xa9279a00000000002583680a1,0x891a4c0374d6801a06800801d68000000004636001205a,0xe1dfc01a467109f0c5f0b836e702a446d04d323402342bc0613797050513d000007184300e062035,0x632a4605c12df00000000002543641a5,0xa103ed0a12a5b0a142420a167ef0d40337000000006525c35c0a5,0x2d657c00000000002580622e7,0x8600c36846f,0x9717f600000000002603a3327,0xcc00f1078033300007643212d42a5002,0x8e121000000000002580622a7,0xa33a6f0af70b30cb4595000000000025000105c],
 #[0xca339b000432175825401202d,0x78436000204f,0x5c3af7000000045724c0013e4,0xa3600a2,0xac224f0642e230a548e70000000002258368001,0xbf44a60cf51cf000000000025005a2a7,0xc33e4b01409d3000084321525c056001,0xa01f801c3d6605967a0000000000024c066010,0xa06ed40275b96000084321735c2a7001,0x905ffb0903e0600025a6000000005424c0013e8,0x2014c0c40c1b0024dab00c64e409a5aa60a1424205e734d000000000025c35c1a5,0x3e3d4800085432172603a3001,0x7e013702257ca0000000024258324001,0xb1135000000000025c05d328,0xb115ac04b189104b394904b489304b60cc0bb17540b14923000000000626000135c,0x25001202b,0x9442008340020640414085696f000784321536000104e,0x9e37bf09523560950f400bc15e60bc3d0e09e11fd079198500000000002d42a505c,0xa21a110246cf60244dae0486cf804845310c9076708f5d88000000000600a06235c,0xaa597c022297c000000000700e06405e,0x3a76b802206b8000000004600c05c06e,0x801d6802550c70257e380c81fcd06c0c0b00007621432d8012029,0xa8125a0c115ef02902490000000005254368001,0x1d49360000000003254056066],
 #[0xb12fa5000000000525c05e35f,0x566f1f0240a59091717504e43b5000008543225c0a500e,0x374d6805718f9033140f0801d68000076243101005205e,0xd61a5f000000000025c05605e,0x694b500af4a6b06952a30af5bfa0000057431258001037,0x44581d04547ff00007643212e03a3065,0x82310800000000002500663a3,0x6a083004a568707c15d90b7078c03169f305a70bb000000000424c225054,0x372ceb06d1ceb01f2e990800ceb0000000054360002052,0xbf44a60b63d40000000005700a2d8062,0x32275f0b41e7a05708ec0be2ebe0804e7a000065432100e04a056,0x412bc600087421353602a3001,0xb643e701b2dc902d53f009c072100428e60000006431360323125,0x830aa20673d6c00000004672e00013e8,0x2d82a406e,0x5f00ac0122f67073392703f40ac000021843601004e052,0xb927d700000000312502e80a5,0x933b3202e59d202e357e0401d3a07d2a7a0400c1107d41c10000564321250002035,0xb23a5f000000000726000e062,0x258066360,0x99013c0992466044581d000000000000a36846f,0x6f3c2f072686f06f2505072064400000864312dc125002,0x804e7a0bd4c6f0801d680bd10be000000432100c05a056,0xab48d200000000002d8001068],
 #[0x835e7002f6e7008d289402b098e0000000026258328001,0x15406605e234b05e040305e734d05e5b8301513dd000743215625c00135c,0x2503603ee,0x3d2f9708108af0ce5f9703d0f97081235000000000060100540e2,0x3126001002e,0x8903c10c70cfd0804e7a01e710008947e70800ceb01e19ad000000341200a05a04e,0x3a597c022297c0aa597c0961a10000000000600e0540ea,0x1600c70920f27094778a039383e02550c7000021843601005e323,0x2f6e700000000265258360001,0x600a35c327,0xd00c5e0000000000260360029,0x3f312e0ba278103f6df103c276b03c723d000004321726000105a,0x180bf40b00d3e000085432125c05d00e,0x25832406e,0x106e0e04766f000000000002d412505c,0x754dce00000432182d801202d,0x5d3b840a8257f00000000002503e4125,0x55174900043217682d401202d,0xd205b10d315390000000000260001360,0xcd08b3000000432125005e066]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows4 : Rows := #[
 #[0x32540013680a1,0x2502de3663e5,0x25c2252d41a5,0x400a05e3641a5,0x2e03a30a5002,0x2541a501002a,0x2d82a8001035,0x25801205e029,0x2d41a505c2a5,0x12d8068001065,0x364a7000000000024c066010069,0x2d40652a8001,0x25c1252d42a5,0xd0ae300d5b41000000000026000105605a,0x260012062045,0x24c0663a30a5,0x25c12504c0d5,0x26032301002d,0x1004e05a1a5,0x26000105c045,0x25c05600105a,0x85432125c05e35b001,0x1e5e8800000000002d80120663a1,0x2d40a500204a],
 #[0x25c05d00e02e,0x424c00105a066,0xc4610000000000036001205a04d,0x700c368423125,0x400a3640660a5,0x2092800000000002503e40a5001,0x1b3107000000000600c0620563a3,0x32e0002052045,0x12500020660e5,0x25000102d260,0xc05c06e0a1,0x10052045044,0x25c0a500e052,0xa05e32305e,0x25c225054125,0x1263f70000000000254066001052,0x2e000104a03d,0x40669000000000025436800102d,0x3010052045060,0x2258328001035,0x244594000000000025005e00102f,0x2583232252d6,0x103973000000000025036600204d,0x1258068001065],
 #[0x618e0003ba30000000000258066001052,0x35c0a5224055,0x4500c04a05e3e6,0xe04a066323,0x25c05e323125,0x1592500000000002541a500c062,0x2125005e01202d,0x100c04a066367,0x25c05e00e02d,0x1e64bf000000000000e04e062125,0xe04c0da055,0x25c22500e056,0x260001052045,0x162bca00000000000100540e205d,0x2d82a3001062,0x25800e02905e,0x2177ed00000000022500020350de,0x2e02a300105a,0x2d8012056029,0xa05a3640a5,0x25005a2a5010,0x250062325002,0x84a3b000000000025c0a500205a,0x25c12504c001],
 #[0x25c12500e052,0x175761023187f000000000000c05a04e062,0x2dc125054225,0x25c2252d8001,0x2e000104a05e,0xa05a02d060,0xe29d000000000002d412501002a,0x2541a5060001,0x978dc01a076501f48ad00b33f5019425b000000000400e04a04505c,0x626035c001029,0x2d41a505c225,0x435c3272a3001,0x25806600105e,0x25c01002d052,0xa06635c2a5,0x32e001005202d,0x2541a501002e,0xa3e43a70a1,0xa1581000008743235c0a52a4001,0x101005e2a3056,0x22541a52dc001,0x2541a52e00a1,0x152b73000007642125c00135c225,0x250012056059],
 #[0x62d42a7012055,0xa05a02d050,0x2d40662a3125,0x24c22535c125,0x12503e800102d,0x2d41a5060001,0x125c125002056,0x22583e800104d,0x2d806600103d,0x3600010470d6,0x24c225054225,0x2d4001061050,0x2d801202904a,0x100e0520663e7,0x400a05e0623a7,0x35c0a500204e,0x250002066365,0xf250500000763212d422505c001,0x2dc12500204a,0xe0560622a7,0x25c0a504c125,0x26000e02d3a3,0x31250066002035,0x2d4125060001],
 #[0x2d42a5002062,0x85432125c055054001,0x2580020ea0a5,0x2d412500204e,0x24c22505c125,0x104b6f0147c9b000000000025800203d0e2,0x25800e02a051,0x258062327001,0x4200a05a04e066,0x162bca0225f80000000000001005404d0da,0x2d80662a3001,0x12e000105e3e6,0xa35c1250a6,0x7222a000000000025000105e062,0x142182000000000036000232b225,0x2d806600104e,0x26000205a04d,0x500a05a04e3e6,0x25c0a500c02a,0x25800103505c,0x225001202905e,0x1250060001035,0x2d8062327001,0x2d42a7012051],
 #[0x258364001051,0x825c22500c02e,0x12500120663a1,0x25836800204d,0xa05605a066,0x2d42a505c225,0x1004c0e2045,0x2d80622a7001,0x25c1a504c0d5,0xa05a36846d,0x25c05635a2a5,0x52d400104a066,0xa3e83a31a5,0x26035c001051,0x25c055054065,0x125001006a03d,0x24c05e001066,0x25c2252d40a5,0x25c05600d05a,0x2e000104c0d5,0x2d4066011056,0x5024000000000002500013e80a1,0x4360001045360,0x360001045048],
 #[0x4133c00000000002580013641a5,0x2503e80a1001,0xe04c05e0d9,0x2600010540dd,0x12503e800104d,0x525c056010029,0x25806600e029,0x3600010470d2,0x25c05d00e02a,0x25c05635e001,0x212d801205202d,0x1029bf00000000002e000242b06d,0x126000205a055,0x1258066002065,0xc3683232a5,0x24c2250540dd,0x130c00032882000000000000a05a02d2dc,0x20734302029d800000000002582e80a5001,0x26000105205e,0x25c36000102d,0x25c055054225,0xa06204e3a3,0x11718c000000000500c04a05e062,0x25806201042d],
 #[0x25c05605a2a5,0x4133c00000000002580010352dc,0xa3e83a30a5,0x2d406600104e,0x25c1a52d41a5,0x43212d42a7062001,0x1d2a36000000000000c3e80a52a3,0xa05a04e368,0x260010029056,0x600a06235c0a5,0x1c495e000000000024c01002d062,0x225800106403d,0x2d42a5002066,0x13336101311250130fde0132eac000000000025005e066001,0xa0540660a1,0x2e03a3066001,0x260360029001,0x181438006360d0000000000258012029052,0x26000105605e,0x260360001029,0x432125c35c0a5001,0x2543640a5001,0x26035c02d001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows5 : Rows := #[
 #[0x25005e00106202d,0xc04a03d35c125,0x2503e40a500102d,0xa05203535c325,0x2541a52e000102d,0x2500013e80a102d,0x250010029062035,0x258001056062125,0x2d412500206205d,0xc06202d044035,0x35c0a5224001051,0xa05203505404d,0xc04a03d2e00a1,0x26000105605a1a5,0x2d40a501002a03d,0x2d41a505c001049,0x2e03e7002055129,0xe0620562a3225,0x25405600106202d,0x25005e066001035,0x2e00020452ab225,0x25c00135c2a50a1,0x100540660e1045,0xc05a0662a31a5],
 #[0x250010029062055,0x1005a03d04c04d,0xe04a04505c1a5,0xe06205e2a31a5,0x25401202d052225,0x2e001002d2a3225,0xa05e3231252d6,0x1005a03d04c1a5,0x2502e80a500102d,0x36000204d32f0a1,0xa05403d0da035,0xa06205605a065,0x2580660010370c5]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows6 : Rows := #[]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit5 := atlasRow g17frame 5 g17rows5 g17rows6 0 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x0 : Span g17audit5 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x8 : Span g17audit5 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x16 : Span g17audit5 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x24 : Span g17audit5 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x32 : Span g17audit5 32 37 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done5 : Region g17frame 5 37 g17rows5 :=
  atlas_sound g17proper g17frame g17vframe 5 37 0 g17rows5 g17rows6 g17rot (by intro j hj; omega) (join_span (join_span g17check5x0 g17check5x8) (join_span g17check5x16 (join_span g17check5x24 g17check5x32)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit4 := atlasRow g17frame 4 g17rows4 g17rows5 37 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x0 : Span g17audit4 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x8 : Span g17audit4 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x16 : Span g17audit4 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x24 : Span g17audit4 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x32 : Span g17audit4 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x40 : Span g17audit4 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x48 : Span g17audit4 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x56 : Span g17audit4 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x64 : Span g17audit4 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x72 : Span g17audit4 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x80 : Span g17audit4 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x88 : Span g17audit4 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x96 : Span g17audit4 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x104 : Span g17audit4 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x112 : Span g17audit4 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x120 : Span g17audit4 120 128 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x128 : Span g17audit4 128 136 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x136 : Span g17audit4 136 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x144 : Span g17audit4 144 152 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x152 : Span g17audit4 152 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x160 : Span g17audit4 160 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x168 : Span g17audit4 168 176 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x176 : Span g17audit4 176 184 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x184 : Span g17audit4 184 192 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x192 : Span g17audit4 192 200 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x200 : Span g17audit4 200 208 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x208 : Span g17audit4 208 215 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done4 : Region g17frame 4 215 g17rows4 :=
  atlas_sound g17proper g17frame g17vframe 4 215 37 g17rows4 g17rows5 g17rot g17done5 (join_span (join_span (join_span (join_span g17check4x0 (join_span g17check4x8 g17check4x16)) (join_span g17check4x24 (join_span g17check4x32 g17check4x40))) (join_span (join_span g17check4x48 (join_span g17check4x56 g17check4x64)) (join_span (join_span g17check4x72 g17check4x80) (join_span g17check4x88 g17check4x96)))) (join_span (join_span (join_span g17check4x104 (join_span g17check4x112 g17check4x120)) (join_span (join_span g17check4x128 g17check4x136) (join_span g17check4x144 g17check4x152))) (join_span (join_span g17check4x160 (join_span g17check4x168 g17check4x176)) (join_span (join_span g17check4x184 g17check4x192) (join_span g17check4x200 g17check4x208)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit3 := atlasRow g17frame 3 g17rows3 g17rows4 215 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x0 : Span g17audit3 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x8 : Span g17audit3 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x16 : Span g17audit3 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x24 : Span g17audit3 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x32 : Span g17audit3 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x40 : Span g17audit3 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x48 : Span g17audit3 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x56 : Span g17audit3 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x64 : Span g17audit3 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x72 : Span g17audit3 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x80 : Span g17audit3 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x88 : Span g17audit3 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x96 : Span g17audit3 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x104 : Span g17audit3 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x112 : Span g17audit3 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x120 : Span g17audit3 120 128 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x128 : Span g17audit3 128 136 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x136 : Span g17audit3 136 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x144 : Span g17audit3 144 152 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x152 : Span g17audit3 152 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x160 : Span g17audit3 160 164 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done3 : Region g17frame 3 164 g17rows3 :=
  atlas_sound g17proper g17frame g17vframe 3 164 215 g17rows3 g17rows4 g17rot g17done4 (join_span (join_span (join_span (join_span g17check3x0 g17check3x8) (join_span g17check3x16 (join_span g17check3x24 g17check3x32))) (join_span (join_span g17check3x40 g17check3x48) (join_span g17check3x56 (join_span g17check3x64 g17check3x72)))) (join_span (join_span (join_span g17check3x80 g17check3x88) (join_span g17check3x96 (join_span g17check3x104 g17check3x112))) (join_span (join_span g17check3x120 (join_span g17check3x128 g17check3x136)) (join_span g17check3x144 (join_span g17check3x152 g17check3x160)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit2 := atlasRow g17frame 2 g17rows2 g17rows3 164 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x0 : Span g17audit2 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x8 : Span g17audit2 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x16 : Span g17audit2 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x24 : Span g17audit2 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x32 : Span g17audit2 32 39 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done2 : Region g17frame 2 39 g17rows2 :=
  atlas_sound g17proper g17frame g17vframe 2 39 164 g17rows2 g17rows3 g17rot g17done3 (join_span (join_span g17check2x0 g17check2x8) (join_span g17check2x16 (join_span g17check2x24 g17check2x32)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit1 := atlasRow g17frame 1 g17rows1 g17rows2 39 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check1x0 : Span g17audit1 0 5 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done1 : Region g17frame 1 5 g17rows1 :=
  atlas_sound g17proper g17frame g17vframe 1 5 39 g17rows1 g17rows2 g17rot g17done2 g17check1x0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit0 := atlasRow g17frame 0 g17rows0 g17rows1 5 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check0x0 : Span g17audit0 0 1 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done0 : Region g17frame 0 1 g17rows0 :=
  atlas_sound g17proper g17frame g17vframe 0 1 5 g17rows0 g17rows1 g17rot g17done1 g17check0x0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g17bound : ¬Feasible g17X 12 1 (wires g17V) := by
  apply full_raw (positive_checked (v:=g17V) (by decide +kernel))
  exact whole g17done0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19X : Word := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19C : Charts g19X := ⟨unpack 0x10887a5d0e872791c2e0f0781c0d96c345a1d066b3196ca6532791c8e2b1589c4e231186c2e170984c1e0ee970b4592c154aa54aa150a4d228b45a25128541a0d028140a05028140a05028140a050281349a4ca6530984aa512592492452290c82412090482412090482412090482411c8d4622d168ac56271188c36190a8542613088442211088442211088442211088441e0d0681c0de8f0783a5d0e872385c0e06cb61b0d46a349a4d168b3598cb653298ac56231186c2612d164b2582c154aa54aa150a45128942a05028140a05028140a05028140a05026934994c2612c944a24d229147235188b45a190a854221108844221108844221108844221106833e1e0f0763a9c8e471361b0d46a349a4cc6532988c46130970b2582c158aa5529148a25126934984c2592894472310c84422110884422110884422110884421e0e874381c0d86c35198c45c2c160ac5229130984a2511884422110884422110884422110884421c0d06832180c06030180c06030180c06030180c0582c150a84c2211088442211088442211088442211070341a0c06030180c06030180c06030180c0602c1607030180c06030180c06030180c060301806030180c06030180c06030180c06039048241209048241209048084060c42031249206240a29006a81080d426114190420314092482112008844221108844221108844a2211321017118881818061601a068501a13080308908060308c45081110884422110884422110886060306030222110832108485030840d08830184210d002242108841821,unpack 0x8072590683259182c0b0700c0c96430581c064b2192c84532590c0e09158144e011182c0c170104c1604e87034190c1142a44a2050249220a4582112050120e4b031482c01a0c9451d0d045200c855141a4486510180a8510582092042280e4b031482c01a0c9451d0d045190a841148944229128a416251080c160902054041392c0c520b0068325147434114642a04416090281404e8d038325906832305806064b4190d02a34124d060b2590c96422982456011182c0410d12432480c1142a44a205024410890392c0c520ad064a29007434114642a1024914894822124900a249208145225108a44a090205c960629056832514803a1a08a321501104813a1c0d0743a1c0647034190d02a34124c86422980446020950925024150a84528048a0412491490442492014452210725818a415a0c9451d0d045200c854021a0c85430140d06434190c05428120a850091208848051164b031482b41928a3a1a08a32150800214090281392c0c520ad064a28e868228c854100405024140284b25818a415a0c9451d0d045190a82001050240b92c0c520ad064a28e868228c85408020281205c9606290568325147434114642a0200b25818a415a0c9451d0d045190a804018a45229148a45229148a450a8241960415148a0484822120ca03810560703018a02815018a453031412090482412090482412092040a0502424241202a0482810288009090241240124002440120901224008040201008040201008060209124100301008101004050900405008100802809000202808040801,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W0 : Wire g19C := ⟨inputColumn0,0xc4c10398cc00b1800001080000fc60004c4481d3200820001075b0003090d9a33c9400001c73fffe20001ffff600070003fff000000500fff3839bdfff3818ad,0xc4c10098c400b1a910010a91004c6a44444480d320082a841014b542100048a11c95510000112a222a88095116a8835441511000403712000401602fff3818ad,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W1 : Wire g19C := ⟨inputColumn1,0x210a52610c040200006430000b2180007c00061c3b30c0006249c00031632604c0fffff66a4c8000c0006400080007fffffff003014800000a5697000300a110,0x210a52610804024086643408c9219023180002040b30d04362494821a0210200402208762a44c118d0462608c90464823608e000a54860003a7c82000000a110,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W2 : Wire g19C := ⟨inputColumn2,0x1c01f2583c000181c00013c6000072081863c4010000038e7fffc98c38470f180008738f0001000078000ffff9fffc000001180008000c7d602000c55602,0x40052583c185181c18512c6061462080801440106140080130a498438470518c508508b18a1062858c50262893148c50fff1a808dffc18008d000c55602,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W3 : Wire g19C := ⟨inputColumn3,0x600607e0080c000000600001c07ffff8070e07c003e00007c0f80000e0fc0780fe0000f83f00001ffff80000ffffe0000000000e45e62000228000000c6d602,0x600002a0080c001a206001a4000a0698070a07c003e00c9340f8064820bc0280ae01a228370034860d2801a4c0d3606901a4000200860001c45602001028000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W4 : Wire g19C := ⟨inputColumn4,0x380c7f80031f000001f800001ff800000380ff8007c000007ff000000ff0007ff000000ffc000001fffffffff000000000000000a44820ffe18008d000200820,0x380c7f00031f005245f805249fb0149203805f0007c015124be00a890df00056e002a44d7c005491952576a4a15240a922a48ffe9c408d000200820000000000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W5 : Wire g19C := ⟨inputColumn5,0xc00f800003e0000001ffffffe000000003ff000007ffffff800000000fffff800000000ffffffffe000000000000000000000ffc1b808d001808000ffc18008d,0x3e0000066ae5006e000001b029900000553401b8000000d8fffb7000000066fffee80dc00360006c0036001b006c00183c000ffc18008d000804000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W6 : Wire g19C := ⟨inputColumn6,0x3ff0000003fffffffe0000000000000003fffffff8000000000000000ffffffffffffff000000000000000000000000000000002002110002000040000002150,0xe50000003e9d48378000037000000dc03fffdfbf000019c000000ce0fdefdffbfdc3780000006e001b80037001b800dc0370002000000000002110000000040,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W7 : Wire g19C := ⟨inputColumn7,0x3ffffffffc000000000000000000000003fffffffffffffffffffffff00000000000000000000000000000000000000000000000010000000401602000010000,0x3ffffbffac00006380000638000018e00166f7febaacb9e07f7fecf030000000000338000000670019c00338019c00ce03380000401602000010000000000000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W8 : Wire g19C := ⟨inputColumn8,0x3ffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000ffc5ab7df000182204002028040,0x31afffd5fc162b7c0151afc01fff5f007c00000000001e0000000f00000000000003c000000078001e0003c001e000f003c00ffc58379f002028040002500088,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19V := [g19W0,g19W1,g19W2,g19W3,g19W4,g19W5,g19W6,g19W7,g19W8]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19proper : proper g19X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19nd : (g19V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f0 : Basis g19X := basisFor g19X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g19V.map Wire.w) 12 (assignRows [9,1,6,5,0,4,2,3,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f0valid : (Price.mk g19f0 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f1 : Basis g19X := basisFor g19X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g19V.map Wire.w) 12 (assignRows [4,9,1,6,3,7,0,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f1valid : (Price.mk g19f1 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f2 : Basis g19X := basisFor g19X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g19V.map Wire.w) 12 (assignRows [6,1,9,4,3,5,2,0,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f2valid : (Price.mk g19f2 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f3 : Basis g19X := basisFor g19X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g19V.map Wire.w) 12 (assignRows [5,6,1,9,0,7,3,2,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f3valid : (Price.mk g19f3 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f4 : Basis g19X := basisFor g19X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g19V.map Wire.w) 13 (assignRows [0,4,7,3,9,5,1,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f4valid : (Price.mk g19f4 0).Valid 1 (wires g19V) :=
  initial_price g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f5 : Basis g19X := basisFor g19X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g19V.map Wire.w) 12 (assignRows [1,6,5,7,2,9,3,0,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f5valid : (Price.mk g19f5 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f6 : Basis g19X := basisFor g19X 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff (g19V.map Wire.w) 13 (assignRows [4,0,5,6,1,7,9,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f6valid : (Price.mk g19f6 0).Valid 1 (wires g19V) :=
  initial_price g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f7 : Basis g19X := basisFor g19X 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff (g19V.map Wire.w) 13 (assignRows [6,5,0,4,1,3,2,9,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f7valid : (Price.mk g19f7 0).Valid 1 (wires g19V) :=
  initial_price g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f8 : Basis g19X := basisFor g19X 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (g19V.map Wire.w) 12 (assignRows [7,5,6,1,2,4,0,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f8valid : (Price.mk g19f8 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19prices : List (Price g19X) := [⟨g19f0,0⟩,⟨g19f1,0⟩,⟨g19f2,0⟩,⟨g19f3,0⟩,⟨g19f4,0⟩,⟨g19f5,0⟩,⟨g19f6,0⟩,⟨g19f7,0⟩,⟨g19f8,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19valid : ∀ p ∈ g19prices, p.Valid 1 (wires g19V) := by
  intro p hp
  simp only [g19prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact g19f0valid
  · exact g19f1valid
  · exact g19f2valid
  · exact g19f3valid
  · exact g19f4valid
  · exact g19f5valid
  · exact g19f6valid
  · exact g19f7valid
  · exact g19f8valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootStep := Step.binary true g19W0 g19W2 true true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootV := rootStep.after g19V
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootPrices := g19prices.map (fun p => p.advance g19V rootStep)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootValid : ∀ p ∈ rootPrices, p.Valid 1 (wires rootV) := by
  intro p hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  exact advance_bin (g19valid r hr) (by simp [g19V] : g19W0 ∈ g19V) (by simp [g19V] : g19W2 ∈ g19V) true true true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19frame : Frame g19C := ⟨13,1,rootV,rootPrices⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19vframe : g19frame.Valid := ⟨by decide +kernel,rootValid⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19auto0 := autoFor g19X (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rot0 : Rotation g19frame := ⟨g19auto0,[extra,g19W0.w,g19W1.w,g19W2.w,g19W3.w,g19W4.w,g19W5.w,g19W6.w,g19W7.w,g19W8.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19auto1 := autoFor g19X (assignRows [2, 1, 0, 5, 7, 3, 6, 4, 8]) (assignRows [2, 1, 0, 5, 7, 3, 6, 4, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rot1 : Rotation g19frame := ⟨g19auto1,[extra,g19W2.w,g19W1.w,g19W0.w,g19W5.w,g19W7.w,g19W3.w,g19W6.w,g19W4.w,g19W8.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rot := #[g19rot0,g19rot1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawNo : ¬Feasible g19X 13 1 (wires g19V) := by
  apply full_raw (positive_checked (v:=g19V) (by decide +kernel))
  exact cut_sound g19nd g19f6valid (by decide +kernel)

end OneNot


namespace OneNot

-- The orbit and row checks specialize the atlas of L-meta-2161 to monotone suffixes.
def NoTailNeg {x : Word} {c : Charts x} (f : Frame c) := ¬Exact x f.b 0 (wires f.v)

lemma moreNeg {x b t S} (h : Exact x b 0 S) : Exact x b t S := by
  obtain ⟨n,hn,j,hj,v⟩ := h
  exact ⟨n,hn,j,by omega,v⟩

lemma tail_neg_forbidden {x : Word} {c : Charts x} {f : Frame c} (h : f.No) : NoTailNeg f :=
  fun he => h (moreNeg he)

def TailRegion {x : Word} {c : Charts x} (root : Frame c) (d num : ℕ) (r : Rows) :=
  ∀ i<num, ∀ g, root.replay d (tapeAt r d i)=some g → NoTailNeg g

lemma tail_orbit {x : Word} {c : Charts x} {root f : Frame c} {depth tape} {a : Rotation root}
    (good : ∀ g, root.replay depth tape=some g → NoTailNeg g) (hit : fromOrbit root depth tape a f=true) : NoTailNeg f := by
  obtain ⟨g,eg,h⟩ := (Option.any_eq_true ..).1 hit
  obtain ⟨⟨b,_⟩,pm⟩ := (Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
  have eq : (wires g.v).image a.R.p.q=wires f.v := by
    have words : bareReplay a.base depth tape=(g.v.map Wire.w).map a.R.p.q := by
      rw [a.eq,project_tape,←replay_words eg]
    ext z
    have p := (List.isPerm_iff.mp pm).mem_iff (a:=z)
    rw [words] at p
    simpa only [wires,List.mem_toFinset,List.mem_map,Finset.mem_image] using p
  intro he
  apply good g eg
  apply a.R.reflect
  rwa [eq,←beq_iff_eq.mp b]

lemma tail_links {x : Word} {c : Charts x} {root f : Frame c} {r : Rows} {rot} {d num key blob cnt}
    (good : TailRegion root d num r) (hit : linkBits root r rot d num key f cnt blob=true) : NoTailNeg f := by
  induction cnt generalizing blob with
  | zero => contradiction
  | succ n ih =>
    simp only [linkBits] at hit
    split at hit
    · contradiction
    rcases Bool.or_eq_true_iff.mp hit with use|go
    · obtain ⟨⟨_,idx⟩,q⟩ := (Bool.and_eq_true_iff.mp use).imp_left Bool.and_eq_true_iff.mp
      obtain ⟨a,_,h⟩ := (Option.any_eq_true ..).1 q
      exact tail_orbit (good _ (of_decide_eq_true idx)) h
    · exact ih go

lemma tail_local {x : Word} {c : Charts x} {root f : Frame c} {next : Rows} {rot d num links}
    (v : f.Valid) (gn : TailRegion root d num next) (h : localClose root next rot d num links f=true) : NoTailNeg f := by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · rcases Bool.or_eq_true_iff.mp h with h|h
    · exact tail_neg_forbidden (cheap_cut v h)
    · exact tail_neg_forbidden (shape_sound v h)
  · exact tail_links gn (Bool.and_eq_true_iff.mp h).2

lemma zero_step_include {x : Word} {c : Charts x} {s : Step c} {b t : ℕ} {v : List (Wire c)}
    (h : s ∈ Step.all b 0 v) : s ∈ Step.all b t v := by
  obtain ⟨a,ha,m⟩ := List.mem_flatMap.mp h
  apply List.mem_flatMap.mpr
  apply Exists.intro a
  refine ⟨ha,List.mem_append_right _ ?_⟩
  simpa only [ite_true,List.nil_append] using m

def tailAtlasRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows next : Rows)
    (num : ℕ) (rot : Array (Rotation root)) (i : ℕ) :=
  let pack:=fetchRow rows i >>> (12*d)
  (root.replay d (tapeAt rows d i)).all (fun f =>
    let g:Frame c:={f with ps:=selectPrices f.ps 10 (pack &&& 0xffffffffff)}
    !(g.v.any (fun w=>w.w==x)) && coveredScan g (fun child =>
      (d != 0 && child.t != g.t) || localClose root next rot (d+1) num (pack >>> 40) child))

lemma tail_atlas {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (v : root.Valid)
    (d n num : ℕ) (rows next : Rows) (rot : Array (Rotation root))
    (gn : TailRegion root (d+1) num next) (h : Span (tailAtlasRow root d rows next num rot) 0 n) : TailRegion root d n rows := by
  intro i hi f ef
  have good:=Frame.replay_valid v ef
  let pack:=fetchRow rows i >>> (12*d)
  let g:Frame c:={f with ps:=selectPrices f.ps 10 (pack &&& 0xffffffffff)}
  have gv : g.Valid:=⟨good.1,fun p hp=>good.2 p (prices_mem hp)⟩
  have ck:=h i (Nat.zero_le _) hi
  simp only [tailAtlasRow,ef,Option.all_some] at ck
  obtain ⟨none,run⟩ := Bool.and_eq_true_iff.mp ck
  intro he
  rcases descend c hx he with hm|⟨s,hs,el,nxt⟩
  · obtain ⟨w,hw,eq⟩:=Step.mem_wires.mp hm
    have found : f.v.any (fun z=>z.w==x)=true:=List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr eq⟩
    simp [found] at none
  · have hstep := zero_step_include (t:=f.t) hs
    cases s with
    | flip a ka =>
      have impossible := Step.all_legal hs
      exact (Nat.lt_irrefl 0 impossible.2).elim
    | binary d' a w ka kw =>
      have ok := covered_sound (f:=g) run gv.1 hstep el (moreNeg nxt)
      have close := (Bool.or_eq_true_iff.mp ok).resolve_left (by simp [Frame.child,Step.budget,g])
      exact tail_local (Frame.child_valid gv el (Step.all_legal hstep)) gn close nxt

end OneNot

namespace OneNot

def fixedRows0 : Rows := #[ #[0x100ad300d18cb005092700d05b40000645005179d0041efb00600170010d3700113ee00a09b400f001600c0b1400202f00040e8200a101400b059300800940090c8100707820091e1a007191b00e0ad800305d90296431785] ]

def fixedRows1 : Rows := #[ #[0x2605530080c9800817f704302cb0920a9403204340700a9307405940870edf019046106b0d6d04310c80321a910210b1108e064e07c0bcd049014f06300bb050063a05d0bb90690558053005901a0dac056032e0293645817258,0x2f0c45091072606a05d40190461052090f03a19bd04408980550725025049f0091ff4001049c03c120605e174308d12440331a8d0390f380661bac0161a390650ec00570b3403e09c10710c4a059074b02c0fed04b1e7a0496572381158,0x4e1ff304e0cdc06b0d6d028162602805ad0310cbb04807bc02403ac0400eaa02415450401046081031b0060e190964317852006,0x2b12df02b0fc5053005908f0a28059074b0591dff0610533075060f0140fee03400cd0141fdf03410be05b029606d03720964238751001,0xa1d900861b8806f0be404310c803501bb06c12d40091ff403a0e6e01f0c7101012d3051095205513d202805ad07a185003b135101e1f3e08b0d9501814950731f6e00296478530c6,0x1d03160880d76052115008007160270d7508c087606f0be40831d7300212f507e0df30150b7c07d167d02915c004700c1094213785600e,0x7702cd04b1e7a0880d760920a9404b04440881bec06c034d025049f0251b5306c12d400704de05a0fdc0361bd10360d6a07f077007806c1020027101c096806008b908204690130f2708f0a280496827351170,0xb0690064117104c020c049014f07d035a0361bd108d12440330fa80761af60161a390400eaa011076d00f06b00429631578056,0x68107f00f06b007e0df30210b11068011000f174107e1c6903b03ca05a0fdc03c120603c08ba0850c3d020027104807bc03b1351064293187506e,0x840b8f08e064e015185905e17430791a700380bd00390f3802403ac01e1f3e05f00d004a115004509d70230b94000069505c1baf0249361578058,0x1b08c200d06ba080071600403a30320434083058c00114f301f0c7106713820791a7005f1c0901208c706204710221bcc055072506e0ff4009641758213f,0x5c1baf00212f505c0c40002016b07a08c900704de067138204204e207f07700310cbb07a185006709df04a115004a02e903004a600c0fa40326498751070,0x410a22058181a08c08760580503074059408c16ec07206c002002710170e880161a39017154201600f30964321875127,0x2e0d1b056032e01d031600817f708608ea091072600403a3058050304b044404e0cdc00d1a00064117105c0c40046013100f17410050a3500e1f2302d053604d04c702b0fc50296874153270,0x4d17de04d04c7069055808b1e0e0130f270710c4a071130101208c70540f260370a2708b0d950121f2403004a600c0fa40230b9400006950231d2d000182e07b0a3204f0b0e03d04f009005cc03d14e109015bd02a079508908710964213785002,0x30f210270d750700a930271beb010034c01012d304204e20380bd00381d690540f260370a2707f07700390f3803915f20964327851128,0x26055300a0e0902f0c4502f12fc01b08c20030f210410a2200a1d9001b1f1f0840b8f00b06900841d2800b182903f007e08a0b7c0642317859014] ]

def fixedRows2 : Rows := #[ #[0x72006211c1157009194c0c706cb0d709fa03a0ad6089017a002042e11815c300421957680020de,0x8013aa0f9007411201220b81ffa12f1ea505416250ca1299038012607413af00000875630b6156,0x9b0a9b0c813f5000000001407000c,0xff0fca0fa025b0000000009128016,0x2113f270,0x36044900000000012700a3,0x291b1f029080807b08990580a790f3031403006cd0211f65030185a02100f50964318752006029,0x3709300920eef00000000210701f7,0x62171b09a06ac00000000192583f6,0x1260e8909601a7007170807f0bf00c61cf4084077a0ad10e7000002641714825e,0x6e01d905718cb098063304e00c902f125808713b400a0eb2091116300642751891d6014,0x7c005d12a115201b194707e025805b119b0631427589056014,0x11815c3118065404c02dd0920eef012018404c126410a09fa0900ad60991a980990a890150d3d00642187590020f6,0x2113f370,0x3700a2,0xe0009e0c3128809503a90221dd8096423158705606e,0x76071912e0609000000218612825e,0x98056070,0x7404060110b8405018fd02c03bb04003ac001189a0630976088063809643758120021c7,0x920eef0120184103037c0da0fd6113087b0ee026000000729130021f8,0x12809f006017f805a00270a90ad30350d8708e07150342965871001058,0x8c13160c40f8a0000000536048010,0x1b00010731e5209513c60d90f600432196875046127,0x68127058],
#[0xf2013a0640e9f00000968711d6070,0xad10e71350bc60ad0ee1100092d0d90f600d60bc00b20e72000000041714805e,0x12003d30000000000258078,0x80040102f0b7f09806330cf0e6a1051f59006417582913f014,0x370930103037c00000000121700a3,0xc304a311102980e71aad1080c6a0000000436270010,0x145604825e,0x2f0b7f01f19d30451eb41121f730110b8400709e20eb06eb04717c4068124400000785420c613f,0x9503a91090fd009513c61091e46096421385706e127,0xc917970bd0a5c100092d0c905940e0009e00b0138000000002706e258,0x24530b6048,0x9d0fd500000013860020e0,0x141ed50d112400000086312058008,0x1350bc608201250ba04670bf09a9013112913a0d410c00eb000000081631581f6,0x6e01d906e1fd307c005d0b00ac711a05fc0250e160000006497258016,0xe4150f13118770000000036128010,0x2607f00a708e30b31a7911505d804d1c570b516d700976845320c6006,0x8b09050a503be0e4051e0ea0a1b09b0a9b08c018c08d074601d126f0b61aa1000962785400a02a,0x1189a11009fa0010ef70000000312002040,0x10c0d3f09a120b02a1e550e21ab905c0d5e08e136d03e0e3601604490e811550b90c1e03f02310196428753001270,0x10e03090000000000158078,0x11102980ef06a804806900a00c5e06a151009216875342700a1,0x560c9d00000000002703a8,0x5718cb098063308013aa12a115201b194706908cf0441cee03219650000000029158016],
#[0xed0fd500000001390020f8,0x13607e71250a750000009312070008,0x451eb40a30746000000041213f258,0xd90f60041170a0000000008056148,0xe21ab90cc14e50be0acc06d151c0cb08f30f002ed04f08d4028120a01617f10429635871001056,0x4e00c91140d4b043060a0961c7a09601a712e0609007170804a03d300709e20a708e3049068703b00ce07a0caf07a112011f072f00009654870c61d6,0xbf106f09513c601810690000007325046170,0x1320a5d0d0051b0d0150c11009fa09c0ad60120184009194c009000600196487520021af,0x8620581af,0x9194c00000000180581a7,0x570d7c0df1bd009601a708215d61121f73061133d00409400650c6811704410460d810ad0ee100000872530c6147,0xc917970031f9f00d03150610e8907f0bf013b05e20b30af20490687000097518606e1d6,0x7f0bf00ba1b1b061133d100092d09513c60e31bb6000000013506e148,0xcd11760d709fa0000000361002060,0x6908cf12903b012c0599117164701311290c60c7e038012605d166306b15bd09e02c00a4134900f104c10f0c1400e091709463857121580a1,0x8713b40cf0e6a0ff0fca087033b0cf14ca0aa0c380aa1dd110b00770f80bac0fb054a0fb1a7c0ec0ff6000642785901402a,0xd508770221dd800c0dfb0750d3e0319647582056006,0x1b194701b000108101ab1340d590321648759127014,0x920701af,0x6e01d9062047d053171a07607190fe04e30051b650ad10e702619f31140d4b04507170c917970970d3e01e02c0010083f05501de00000541871d6257,0xb81ffa05905220000000001158226,0x65840480de,0x52700a6,0xe71aad07015100b708e703418a90231e9c06f190405f1ef70e50fa9039059f094231758600e029],
#[0x221dd80220e690b30af20b31a790930f420e10576031964875206e006,0x7c005d0d90f600d508770e0009e0642931758046056,0x19540480f6,0x84077a09513c6020174002a1e550000007651148076,0x548056228,0x1180654036044904b194811b173000000000130022f8,0x220e690a00c5e0290808024174900000003120062f8,0x4b0cf004b19480860e4405018fd1320a5d113087b0861dcb0500f5a0ed0fd50900ad60c706cb0c718640326418579002076,0x1e02c00ae059101e10bd0660b5a00000000002580a2,0x24530c6128,0xdf059503312fd0f900740ce1e19073061112c05990b7124206c1c13000000001415800c,0x9a06ac09a120b0b20e72116008f0a60def12809f00bc054d0be0acc0e60b600fd06bd11e0c3c10c0d3f0642937518001258,0x1220fd500000001320021b0,0x98063303312fd00709e20880638000076528113f056,0xe0009e130095210c0d3f0000000001258076,0x6517ba05905220ca12990af14330f611bf0b40a8a00000023811580a2,0x9513c602d07ff0000000000127270,0xb20e720c00eb00d307810cb123006017f812d0a4704f08d401a044d051069c03c152902a088e0429365871001158,0x60d3e0bd0a5c0061bb400d03150ba04670ba1b1b00d129c000085713206e16f,0xc109fb0d402cc0350d870351d7813702a006017f806007f50396487512001038,0x11806540000000051048076,0xb00ac7010083f0f1000b133000805e0b1010202e4010163c0b10e1f0dc05d100800dc02934875162580a1,0x12f0f0b0bb03d911c081a00000000120481cf,0x12f1ea5000000683205813e],
#[0x13a0d4110d01a400000007211700a2,0x8e071508e136d13702a005a002705a10180d402cc0364298571001070,0x792113f070,0x970d3e08500120971b3b0a20acc09f05db00000000172580a3,0xe0009e0830c450000000015046370,0x41b4605416250bb13cd05208d407117bf0a8154b03d0e1600000000211580a3,0x51480a6,0x93207013e,0x5406e228,0x5501de0551fd807200620a20acc1060fcb119013e00000001370022e0,0xf50d3300000000001582a8,0x2619f302607f00d5087710202e407b0899123076600000031720062e0,0x53171a084077a08201251260e89043060a00d0315000000768117025e,0x5c107805c0d5e0a60def01c0ad7078003a0de037c0dd159204f08d40dd058f04f18d10964218573001036,0x42113f048,0xdf1bd001f19d3033013400300b308b187d01918ad00972845360c600e,0x760719076151600000000021282e0,0x4618d0088063807413af11c1157009194c05208d40171dd30671a2800000006130021e0,0x79127070,0x31011400000468711d6228,0xd90f601270cf30000000051127258,0xc2074c01617f1116008f0c213a401604490d307810d31e3502b02d70de037c064293857100106e,0x25046128,0x7705e600000000001703a8],
#[0x71700a6,0x453204813e,0x4c02dd000000019607025e,0x10a09fa0000007139002078,0x5282580a6,0xce1e1907306110c3128802719be0f40901063192758405600a,0xc304a30060d3e1090fd000300b313909bb0fc0fec091432875606e00e,0x12018400000007210701a7,0xf9125501f19d30ea13af0ab150b1041064009417582613f00e,0x115165111505d813607e70141ed50140071121081308a146708a05f4000964785200602a,0x9401cb09410410791d51079049706491875321700a1,0x3312fd0a503be0ac07a9009675182413f00a,0xaa0c38124069a0000000089058016,0x7206e128,0x62047d07d03ac084077a00000000161d6270,0x51b6500509620e9064100000000002581a8,0x60d3e1090fd009401cb07015100c507b90000007326170010,0xba70da0fd606309761220fd509c0ad60001b2e0631fd30150d3d002042e00215c7113087b0171dd30170dd0096437851200203e,0x11a05fc00a0eb20441cee04403a500a1e3911d0b7513c06ad0d205130a1004b0d21a450a1157d1010fbf0db0af70642318759014029,0x551fd803b00ce0460d810110b8408812e504c12640861dcb04218890cd0f6102e00400001b2e096218375400214e,0x1090fd00731e520f717c70d80378032194875612700e,0x12a08150ce06690bf106f0000813752046147,0x720062000000051804805e,0x2a088e02a1e550c00eb00c0156706d151c06d050d0c109fb01c0ad713702a010707cc0de037c08f0c8213801b112b0d5e0642398517001170],
#[0x1060fcb02e125202c03bb0d0051b0171dd304218890401a180991a9809d0fd503a0ad6089132204b0cf0032491587600205e,0x7d03ac12903b00ef06a800000000011582f8,0x53171a1350bc605305170bd0a5c0f1000b00000072191702e0] ]

def fixedRows3 : Rows := #[ #[0x3a030c0a91a59000000003100203e25e,0x10020401c5,0x8612e00c0100a000000000800203e0de,0x3406e0c600e,0x10a4500000000000c6147123,0x6305e805f00c400000000000c62561a8,0x3206e16f010,0x3d114400000000010c613f056,0xa60fe70af052b053080400008654312580a105d,0x480bdf00000000050020ce1a7,0xa50282020197403c017204f1eab00000009181d6014031,0xb30dbb0b31bb80ac059c000000000006e258029,0x8205600602a,0xad06e201000ed05d0e51000000001806e16f25e,0x1580a1046,0xc18d309307270331cfb00007425131480a1065,0x9c02c2062125700000004811d6257121,0x671e860ab0e2c03a1c33000000003100214e1c7,0x9f023300b0d5d00000000070020f61a7,0x99045c0bd1ba601e153500000053211480a116e,0x5048008031,0xca0f9e09f023304e08430aa0919000000000000203e0f6,0x8b08650261653000621857300104606e,0x291ed50a9085308602ec0c819ac000000000300203e04e],
#[0x700cc200000000000561700a1,0x61d600a02a,0x11580a3,0xbb1eae0000000059046127014,0x89103c0890039000000319700103616e,0x5600e02a04e,0xc60d4000000000001d6257122,0x310cf70430eba00000000060b61d600a,0x1580760a1,0x6c05240a201350000968752006029046,0x7116cb000000005204606e006,0x371629034019202d0f84000062875400a02906e,0x3044804703eb00000000000063f80a1,0x750bbd055090a0000000000258016029,0x1b047607a01e900000000030c60062de,0x504600e02a,0x79001046070,0x6c052404719950000000000006029270,0x2600a90b10e960000000007001158076,0x700106e128,0x100205e1c7,0x1272700a1,0xae13760ab0e2c0a90853025050c0610a4e000000003500204e14d,0x761e8100000000000c613f014],
#[0x8006029058,0xbf0d9b000000000015825d2a8,0x7023109d1ee502f16f80000000000148016029,0x30b604600e,0xa029070,0x620010380de,0x1a144800000000000022f8121,0x701f7121,0x2a1da90b71d1f0be0aab098037900000561230b6156121,0x2d153103e0edb000094875600e029036,0x8612e0000000000800205e0dd,0x6a0c5e0ae050f0ae1376000000003100214e25e,0xf0eea094154500963187520011480a1,0x1580a304e,0x70012700a6,0x3f168001d0c4d00632187540012700a1,0x291ed50ab0e2c000000003100204e1c7,0x461580a1,0xae13760611c51000000003100204e25e,0x84019d0820b7e00000000000c617025e,0x200e2509b1ed30221569008035e02f16f80000000000148016031,0x20b61d6257,0x671e860a90853000000000100214e1cf,0xa179a00000000080b61d60a2],
#[0x2700a1127,0xb2021a000000000006e0c61d6,0x6e0f6300000000000c61d61a8,0xc318cc000000000700205e076,0x1f1e0c025171e00000000060020f625e,0x8600625e0a2,0x780c5903c017200000000070c61d6014,0xc90ad3089103c02600a90004953871001036056,0x7200207613e,0x20011580a2,0x5e08d307d11d30a11f5c00000001620021e0121,0x84019d00000000000c61702de,0x10a4502c0fc9000000000213f1c6123,0x6a0c5e0611c51000000007300225e2df,0x2700a23af,0x761e810200e2500000000020c6147014,0x6029070,0x1580a222d,0x7960010580f6,0x450a3605b0c4c0000628759046014029,0x2616530441dbc0000000000001036270,0x1480a106e,0x2580a1127,0x9182f03e18270371629000029578400a029056],
#[0x400103804e,0xc705b301000ed08111a5000000001806e15825d,0x1d62572ee,0x3a1c330291ed5000000371800203e1c5,0x11d607022f,0x500d6d00000000000c6147122,0x2580a2065,0x6510e101310e105610e100000000000021d00a1,0xc50da900000000620b61d60a1,0x1501ce00c0f5702f014e00000001921580a1014,0x3700a1046,0xb701cf0110b4a02110d100000000321480a105f,0xa01820016045b08801ac042039408a10bd0000000000148010029,0x8900390261653005156b0000000079001046170,0x780c590a5028200000000471d6257014,0x800a029058,0x34019202d0f840901c49000000007217000c031,0x7d0ce000000000011480a3065,0xcb0c3b00000000580020ce05e,0x870715000000008405612700a,0x671e860291ed500000000430021c724e,0x30144c00e0f620000948752056006029,0x12019c000000000012825e2df,0x1703a8121],
#[0x79001036070,0x1700a1046,0x4b084200000000050c61d60a3,0xa201350a30e150000000000006029258,0xc40b860000000589046056014,0xd0036000000000015825d2f0,0x805601402a,0x5d0e510c705b30280eec000000000006e14825e,0x761e81000000000013f1c6014,0x12701402a,0x4084c01000ed0bd0dac00000000181581f625d,0x463700a1,0x6114807625e,0x2580a31a7,0x1f1e0c000000007100207625e,0x230e6900000000030c6014032,0x310021c705e,0x7f0d53000000000800204e0de,0x5200602a04e,0x11d600a032,0x805800c031,0x400a02a076,0x7001058076,0xd3100000000090011700a3],
#[0x1f1e0c04e084301f0d9300000000070020760f5,0x5740c601402a,0xca0f9e04e084300000000920020f61f7,0x206e00602a,0x90069000000000261700a100e,0x8705606e127,0x8f077709e0b6700000000000c6147256,0x3207c100000000071d6257123,0x113f056014,0x25050c0691665000000000000204e0f6,0x40012583f6,0x107000c031,0x9f0233000000000700203e1ad,0x100205e0df,0x1501ce04d0cac02411a40741e9501e0a2500046518321580a105d,0x9a0fec00000000172580a3065,0x47199500000000020062f8121,0x3603a30220b0a00812540000428759014029056,0x960acb09a0fec00000000000022e0121,0x2113f2580a3,0xbe1dc4038074202110d100000000321480a1067,0x113f00a032,0xc90ad301c09cd0000000000001036258,0x1b04760350a0d0351ce700000000640c600625e],
#[0x2c0fc90a108d800000000011480a306d,0x640010480de,0x3907690000000008058016031,0x20b600a02a,0x213f00a02a,0x9e0b6705c064300000000000c6147056,0x2580a21a7,0x4106fc00000000001480a2065,0xa60fe7055090a00000000092580a1014,0x2580a106e,0xc90ad30b40a50000000000000114805e,0x9606e00625e,0x1580a204e,0x351ce7000007856200625e0a1,0x600e02a03e,0x90ee303e0edb08a10bd0000000000148010031,0x313f1c61a6,0x12700a2,0xa80b8e01000ed000000083106e1581f5,0x10481cf121,0x12580a6,0xad06e20a80b8e000000000006e16f2e0,0xc90ad308b08650002953871001046056,0x700cc200000000020561571ee],
#[0x89103c00000000960011581f6,0xd3100000000790010381f6,0x700106e328,0x9119da000000005604606e00e,0x6048010029,0x2e17da09006900000000000170010029,0x8f1904033030900000000010c6158121,0x8e02a700000000780020760de,0x6070010029,0xb2021a0b31bb8000000000006e0c6256,0x500d6d04106fc000000000313f1c6122,0xc90ad308c04d10000000004001056148,0x1046058,0x10020501d5,0x204614700e,0x49099b000000000113f014032,0x6b00f7000000000000205e1af,0x2048008029,0x5400440000000000014029058,0x2600a90401d89000000007600106e158,0x7920010380f6,0x7902680000000582046056006,0x5c184607e032805c0643027035d000000004714805e0a1,0x6002060165],
#[0x7c0b950661d0b000094875612700e029,0x58046056127,0xca0f9e09f0233000000072900203e1f6,0x81254008035e0000648759014029036,0x621257062005400000000002580a105f,0x4001036048,0x2600a90261653000648537100103606e,0x310cf70a00899000000000115825d00c,0x8504605606e,0xb608d50b613c8000064875206e006029,0x8b08650580c0d0000000000001046370,0x64122808111a5000000000006e158029,0x12800c031,0xe029038,0x12580a3,0x3716290600e5b000000000000a029370,0x13700a3,0x5f12c705f00c40cc0ddb00000000002581a8121,0x30b600a032,0x8d09ed00000000020c613f02b,0x201402a03e,0x10020760f7,0x68025f068125f0b8025f00000000290021f80a1,0x1582f8121],
#[0x1056128,0xaf052b00000000001702e0121,0x5a0dc1000000000015825d070,0x6c1de506c0524000064875200602906e,0xa41ba10061412000092875405600a029,0x1582a8121,0x1480a206d,0x12700a02a,0x231ee2049099b0730afb0230e690491ff803907690391902000026485901402a065,0x310cf700000000000b615600a,0x2128016029,0x601402a05e,0x571e460521f0c000042875606e00e029,0x12580a2,0x6e0f6300000000001d61a82df,0x730afb0000000000128016031,0xc705b30a80b8e0460a4a000000000006e14805e,0x770af00000000000014029038,0xa30e15053080400000000020062e0121,0xa7037b00000000920021f8121,0x430eba00000084520b600a029,0x20b601402a,0x611c510610a4e02b0ba7000000000000204e05e,0x70011700a6],
#[0x5104cf0601e4c0000000000270010029,0x971ce5000000007606e12700e,0x900207817d,0x1402a067,0x8b08650bc0b8b0000000000001258076,0x1700a205e,0x158078121,0x18089a0980379072051306d029f00000000121580a1048,0x2002040235,0x601e4c00000000062700a100e,0x7600300310cf700112ab0501f1c02a1da9067003508d14bb00a179a0c50da900000007580b61561d5,0x4e084306f0457000000000700203e076,0x780c59084019d012019c06e0f6306305e809e0b6701b04760b2021a03207c10c60d4009c02c206a0c5e04b084204b1cb000000095870c61d6255,0x30c6006032,0x8b08650590ed8000000000700106e258,0x8f07770bd1ba602a054603807420110b4a00000002530c6147121,0x4c023000000000050020ce076,0x83013d083113d002013d00000000000022e00a1,0xa502820a5107f092012d03603a3055090a0000000000258016031,0x17069e07b069e085169e00000000000023f80a1,0x8602ec00000000420020ce1cf,0x4f1eab04f0e32054004405415760770af0000064285901402905f,0xc20bc20b907ea00932187540012580a1,0x820b7e0950b780ba069200000068740c61d60a1],
#[0x258078121,0x200602a076,0x100203e1ae,0x7a13ec07a01e90b0029f0b500020a30e1500000000000062e00a1,0x6058016029,0x2070008029,0x5d0e51099045c004084c00000000001481f625e,0x1272580a1,0x104805e,0xd003604d0cac0800a3800000000001580a1270,0x2046147014,0x3b098b03b199900643187590011700a1,0x741e950931c2108a00cc00000002411580a100a,0x11580a6,0x12019c00000000000c613025e,0x20481c724d,0x2580760a1,0x412800c029,0xc1063900000000070020761af,0x2580a1128,0x191d4101902020000648759127014029,0x4084c0a80b8e07e0328000000000914805e1f6,0x70008031,0x79001038076],
#[0x790011700a2,0x306e00e02a,0x1581f6122,0x6e1d61a8,0x14081e092012d014115a09b081f09b1ed304a012b006423158901402905d] ]

def fixedRows4 : Rows := #[ #[0x10381f6121,0xc613f1c51a3,0x580022e00a102d,0x63f80a102d,0x708140210fab000000000014805e1f625d,0x90010561700a1,0x4600e029036,0x3148016029035,0x14801603102d,0x214801003104d,0x50c613f02a1c5,0x90020f61a70a1,0x1580a104d012,0x1580a11d5268,0x5056006029046,0x70011480a106e,0x70814000000001806e1581f525d,0x160c4f01b1b5100000000000c6147121057,0xc613025e2dd,0x10021e00a1045,0x1402905d328,0x21580a105d012,0x14801002906d,0x10023f80a1045],
#[0x190ffc00000000001580a104825d,0x127014029046,0x70023f81210a5,0x200e6c00000000000c600625e2dd,0x10362580a1,0x12700a1036,0x10066200000008311580a105d166,0x20760f514e,0xc6147014039,0x1b08cb00b03aa00000000001580a104f0dd,0x215801603105d,0x30c6014032065,0x1480a105d328,0x204e0f614d,0x700103605606e,0xf0ac2000000000014805e0a105d,0x230801000000000006e1480291d6,0xe01be000000000000203e05e13d,0x1f0003000075e01818470160c4f00000875210c613f1c51a1,0x900ca000000000000204e05e0a1,0x13f1c6123065,0x717000c03102d,0x17000c02902d,0x305c700602fe00000000211580a1014029],
#[0x4600602906e,0xb61561d500a,0x70c61d62551a3,0x1515f400000000000c615812104d,0x217000c031075,0xc60060291d6,0x25801603102d,0x527001003102d,0x18184701b1b5100000000000c614712105f,0x8058016031065,0xe01be000000000000203e13d1d6,0x11700a1056,0x1e0d0200000000000c61d6014039,0xb60461d60a1,0x3514801003102d,0x13700a1046,0x106e148029,0x13f1c612205d,0x14801002902d,0xb61d600a031,0x10363700a1,0x46014029056,0x1206d00240cab000000000006e14805e029,0x60293700a1],
#[0x20ce1a70a1,0x113f014032065,0x1402905d128,0x50c61d60a3255,0x20ce0760a1,0x1580a105d268,0x200203e0760f5,0xc601403105f,0xc613f1c51a2,0x27001002902d,0x706e00a029036,0x62e0121065,0x140290580e5,0x102eb00000000002580a1014029,0x80021e00a102d,0x806e00a029056,0x10463700a1,0x106e258029,0x22052600000000001580a11d5068,0x46014029036,0xa02c900000000000c6147056121,0x70814000000000006e1481f525e,0x21e01210a5,0x250d4700000000000c62561a81a1],
#[0xa0293700a1,0x1c06d4000000000000204e05e14d,0xc0cd700000000000c6256121057,0x250d4700000000000c61d6255228,0x230801000000005306e148029065,0x10021e00a1035,0x812700a029056,0xe01be000000000000213e1de25d,0x10021f80a1045,0x1a1ed8000000000000205e0f60a1,0x1c06d4000000000000214e25e2dd,0x205e1af029,0x500602904606e,0x1580a10480d5,0xc61d61a82dd,0x200203e0760a1,0x561571ee121,0x5606e006029,0x1580a10480e5,0x128016031065,0x1480a105d00e,0x8525801602902d,0xb61561d5012,0x140290380e5],
#[0x1e0d0200000000070c61d6255012,0x46056006029,0x200e6c00000000000c60062de0a1,0x10023f80a1035,0x12700e02906e,0x21d0121065,0x210fab00f0ac2000000000014805e0a116e,0x204e0de0a1,0x1580a104d268,0x1d089a000000000006e0c6147031,0xc617025e121,0x10022e00a1045,0xc617025e2dd,0x50022f80a102d,0x200203e04e0cd,0x5612700a029,0x3148010029035,0x900103604616e,0x814ff002149d00000000211580a100a029,0x700104605606e,0x1056148029,0xc613f02b1c5,0x20760de029,0xc61471211ce],
#[0x21700a100e029,0x5606e00a029,0x258016031065,0x31480a106500e,0x11580a1046,0xc61d60a1128,0x22e01210a5,0x6e12700a029,0x190ffc00000000000b6156121040,0x1480a116e1d6,0x22e0121065,0x158016031065,0xc0cd700000000000c61d62551a1,0x2815801602902d,0xa02c900000000000c6147056255,0x7900203e0f61a5,0x15825d00c031,0x21d012106d,0x58006029046056,0x130be800000000000060292580a1,0x4600e02906e,0x1e0d0200000000001d6257014039,0x2580a105d012,0x70021f81210a5],
#[0x708140240cab000000000006e14805e1f5,0xe1958000000000000203e04e14d,0x50b7a00408de00410de000000009200203e0f60a1,0xe1958000000000000204e14d1c7,0x6e25802905d,0x70814000000000006e16f25e2df,0x1c06d4000000000000205e14e25d,0x1702e0121065,0x62e00a1065,0x11580760a1,0x17083e000000000006e0c61d6255,0x17083e000000000006e1d6257031,0x114805e0a1,0x62e00a102d,0x806e006029056,0x160c4f00b11d6000000000213f1c6121057,0x70021f80a102d,0x12580a1036,0xc61d60a1127,0x56127014029,0x12580760a1,0x1580a116e1d5,0x18073100b03aa00000000010b6156121047,0x11050000000000001580a11d5228],
#[0x200203e0ce0a1,0x20761af029,0x12580a106e,0x204e0760a1,0x46056014029,0xb61561d5121,0xc61d62551a2,0x7081401206d0000000000006e14805e25d,0x1402ae00d103a000000001200203e05e0a1,0x1036046056,0x50b7a000000000000203e0f61f5,0x20ce05e0a1,0x2581a8121065] ]

def fixedRows5 : Rows := #[ #[0xc613f1c51a10c8,0x2580a101402905d,0x1480a100e029065,0x1580a101402905d,0x203e0f60a1065,0x203e0f60a116d,0x1580a101402904d,0x10931000000000006e14805e1f525d,0x1480a100e02905d,0x204e05e0a105d,0xc61470561211cd,0x3000000000000b61561210470d5,0xc61d62551a104f,0x203e04e0a1065,0x203e05e13d1d5,0x14805e0a105d166,0x1580a105d1660a1,0xb615612114d1a8,0x10931000000000006e14805e0291d5,0x60292580a105d,0x203e05e0a105d,0x1480a10651d6029,0x1c5600000000000c613f1c51a104f,0x6e0c61d6255039],
#[0x3000000000000b61561210471cd,0xb61561210401d5,0x204e0f60a1065,0x3000000000001580a104f0dd255,0x204e05e14d255,0x6e0c6147031165,0xc61d6255012041,0xc613f1c51a10e0,0xc600625e2dd121,0x14805e0a116e1d5,0xb615612114d060,0x6e1480290651d6,0x10931000000000006e14805e02916d,0xc61d6255228221] ]

def fixedRows6 : Rows := #[ #[0xb61561210470d51cd,0x6e14805e02916d1d5] ]

def fixedRows7 : Rows := #[  ]

def fixedAudit6 := tailAtlasRow g19frame 6 fixedRows6 fixedRows7 0 g19rot

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk6x0 : Span fixedAudit6 0 2 := check_block (by decide +kernel)

lemma fixedDone6 : TailRegion g19frame 6 2 fixedRows6 :=
  tail_atlas g19proper g19frame g19vframe 6 2 0 fixedRows6 fixedRows7 g19rot (by intro i hi; omega) fixedChunk6x0

def fixedAudit5 := tailAtlasRow g19frame 5 fixedRows5 fixedRows6 2 g19rot

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk5x0 : Span fixedAudit5 0 8 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk5x8 : Span fixedAudit5 8 16 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk5x16 : Span fixedAudit5 16 24 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk5x24 : Span fixedAudit5 24 32 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk5x32 : Span fixedAudit5 32 38 := check_block (by decide +kernel)

lemma fixedDone5 : TailRegion g19frame 5 38 fixedRows5 :=
  tail_atlas g19proper g19frame g19vframe 5 38 2 fixedRows5 fixedRows6 g19rot fixedDone6 (join_span (join_span fixedChunk5x0 fixedChunk5x8) (join_span fixedChunk5x16 (join_span fixedChunk5x24 fixedChunk5x32)))

def fixedAudit4 := tailAtlasRow g19frame 4 fixedRows4 fixedRows5 38 g19rot

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x0 : Span fixedAudit4 0 8 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x8 : Span fixedAudit4 8 16 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x16 : Span fixedAudit4 16 24 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x24 : Span fixedAudit4 24 32 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x32 : Span fixedAudit4 32 40 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x40 : Span fixedAudit4 40 48 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x48 : Span fixedAudit4 48 56 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x56 : Span fixedAudit4 56 64 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x64 : Span fixedAudit4 64 72 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x72 : Span fixedAudit4 72 80 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x80 : Span fixedAudit4 80 88 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x88 : Span fixedAudit4 88 96 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x96 : Span fixedAudit4 96 104 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x104 : Span fixedAudit4 104 112 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x112 : Span fixedAudit4 112 120 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x120 : Span fixedAudit4 120 128 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x128 : Span fixedAudit4 128 136 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x136 : Span fixedAudit4 136 144 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x144 : Span fixedAudit4 144 152 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x152 : Span fixedAudit4 152 160 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x160 : Span fixedAudit4 160 168 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x168 : Span fixedAudit4 168 176 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x176 : Span fixedAudit4 176 184 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x184 : Span fixedAudit4 184 192 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x192 : Span fixedAudit4 192 200 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk4x200 : Span fixedAudit4 200 205 := check_block (by decide +kernel)

lemma fixedDone4 : TailRegion g19frame 4 205 fixedRows4 :=
  tail_atlas g19proper g19frame g19vframe 4 205 38 fixedRows4 fixedRows5 g19rot fixedDone5 (join_span (join_span (join_span (join_span fixedChunk4x0 (join_span fixedChunk4x8 fixedChunk4x16)) (join_span fixedChunk4x24 (join_span fixedChunk4x32 fixedChunk4x40))) (join_span (join_span fixedChunk4x48 (join_span fixedChunk4x56 fixedChunk4x64)) (join_span (join_span fixedChunk4x72 fixedChunk4x80) (join_span fixedChunk4x88 fixedChunk4x96)))) (join_span (join_span (join_span fixedChunk4x104 (join_span fixedChunk4x112 fixedChunk4x120)) (join_span fixedChunk4x128 (join_span fixedChunk4x136 fixedChunk4x144))) (join_span (join_span fixedChunk4x152 (join_span fixedChunk4x160 fixedChunk4x168)) (join_span (join_span fixedChunk4x176 fixedChunk4x184) (join_span fixedChunk4x192 fixedChunk4x200)))))

def fixedAudit3 := tailAtlasRow g19frame 3 fixedRows3 fixedRows4 205 g19rot

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x0 : Span fixedAudit3 0 8 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x8 : Span fixedAudit3 8 16 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x16 : Span fixedAudit3 16 24 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x24 : Span fixedAudit3 24 32 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x32 : Span fixedAudit3 32 40 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x40 : Span fixedAudit3 40 48 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x48 : Span fixedAudit3 48 56 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x56 : Span fixedAudit3 56 64 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x64 : Span fixedAudit3 64 72 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x72 : Span fixedAudit3 72 80 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x80 : Span fixedAudit3 80 88 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x88 : Span fixedAudit3 88 96 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x96 : Span fixedAudit3 96 104 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x104 : Span fixedAudit3 104 112 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x112 : Span fixedAudit3 112 120 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x120 : Span fixedAudit3 120 128 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x128 : Span fixedAudit3 128 136 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x136 : Span fixedAudit3 136 144 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x144 : Span fixedAudit3 144 152 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x152 : Span fixedAudit3 152 160 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x160 : Span fixedAudit3 160 168 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x168 : Span fixedAudit3 168 176 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x176 : Span fixedAudit3 176 184 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x184 : Span fixedAudit3 184 192 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x192 : Span fixedAudit3 192 200 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x200 : Span fixedAudit3 200 208 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x208 : Span fixedAudit3 208 216 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x216 : Span fixedAudit3 216 224 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x224 : Span fixedAudit3 224 232 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x232 : Span fixedAudit3 232 240 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x240 : Span fixedAudit3 240 248 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x248 : Span fixedAudit3 248 256 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x256 : Span fixedAudit3 256 264 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x264 : Span fixedAudit3 264 272 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x272 : Span fixedAudit3 272 280 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x280 : Span fixedAudit3 280 288 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x288 : Span fixedAudit3 288 296 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x296 : Span fixedAudit3 296 304 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x304 : Span fixedAudit3 304 312 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk3x312 : Span fixedAudit3 312 317 := check_block (by decide +kernel)

lemma fixedDone3 : TailRegion g19frame 3 317 fixedRows3 :=
  tail_atlas g19proper g19frame g19vframe 3 317 205 fixedRows3 fixedRows4 g19rot fixedDone4 (join_span (join_span (join_span (join_span (join_span fixedChunk3x0 fixedChunk3x8) (join_span fixedChunk3x16 (join_span fixedChunk3x24 fixedChunk3x32))) (join_span (join_span fixedChunk3x40 fixedChunk3x48) (join_span fixedChunk3x56 (join_span fixedChunk3x64 fixedChunk3x72)))) (join_span (join_span (join_span fixedChunk3x80 fixedChunk3x88) (join_span fixedChunk3x96 (join_span fixedChunk3x104 fixedChunk3x112))) (join_span (join_span fixedChunk3x120 fixedChunk3x128) (join_span fixedChunk3x136 (join_span fixedChunk3x144 fixedChunk3x152))))) (join_span (join_span (join_span (join_span fixedChunk3x160 fixedChunk3x168) (join_span fixedChunk3x176 (join_span fixedChunk3x184 fixedChunk3x192))) (join_span (join_span fixedChunk3x200 fixedChunk3x208) (join_span fixedChunk3x216 (join_span fixedChunk3x224 fixedChunk3x232)))) (join_span (join_span (join_span fixedChunk3x240 fixedChunk3x248) (join_span fixedChunk3x256 (join_span fixedChunk3x264 fixedChunk3x272))) (join_span (join_span fixedChunk3x280 fixedChunk3x288) (join_span fixedChunk3x296 (join_span fixedChunk3x304 fixedChunk3x312))))))

def fixedAudit2 := tailAtlasRow g19frame 2 fixedRows2 fixedRows3 317 g19rot

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x0 : Span fixedAudit2 0 8 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x8 : Span fixedAudit2 8 16 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x16 : Span fixedAudit2 16 24 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x24 : Span fixedAudit2 24 32 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x32 : Span fixedAudit2 32 40 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x40 : Span fixedAudit2 40 48 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x48 : Span fixedAudit2 48 56 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x56 : Span fixedAudit2 56 64 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x64 : Span fixedAudit2 64 72 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x72 : Span fixedAudit2 72 80 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x80 : Span fixedAudit2 80 88 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x88 : Span fixedAudit2 88 96 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x96 : Span fixedAudit2 96 104 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x104 : Span fixedAudit2 104 112 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x112 : Span fixedAudit2 112 120 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x120 : Span fixedAudit2 120 128 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x128 : Span fixedAudit2 128 136 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x136 : Span fixedAudit2 136 144 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk2x144 : Span fixedAudit2 144 147 := check_block (by decide +kernel)

lemma fixedDone2 : TailRegion g19frame 2 147 fixedRows2 :=
  tail_atlas g19proper g19frame g19vframe 2 147 317 fixedRows2 fixedRows3 g19rot fixedDone3 (join_span (join_span (join_span (join_span fixedChunk2x0 fixedChunk2x8) (join_span fixedChunk2x16 fixedChunk2x24)) (join_span (join_span fixedChunk2x32 fixedChunk2x40) (join_span fixedChunk2x48 (join_span fixedChunk2x56 fixedChunk2x64)))) (join_span (join_span (join_span fixedChunk2x72 fixedChunk2x80) (join_span fixedChunk2x88 (join_span fixedChunk2x96 fixedChunk2x104))) (join_span (join_span fixedChunk2x112 fixedChunk2x120) (join_span fixedChunk2x128 (join_span fixedChunk2x136 fixedChunk2x144)))))

def fixedAudit1 := tailAtlasRow g19frame 1 fixedRows1 fixedRows2 147 g19rot

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk1x0 : Span fixedAudit1 0 8 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk1x8 : Span fixedAudit1 8 16 := check_block (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk1x16 : Span fixedAudit1 16 17 := check_block (by decide +kernel)

lemma fixedDone1 : TailRegion g19frame 1 17 fixedRows1 :=
  tail_atlas g19proper g19frame g19vframe 1 17 147 fixedRows1 fixedRows2 g19rot fixedDone2 (join_span fixedChunk1x0 (join_span fixedChunk1x8 fixedChunk1x16))

def fixedAudit0 := tailAtlasRow g19frame 0 fixedRows0 fixedRows1 17 g19rot

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

lemma fixedChunk0x0 : Span fixedAudit0 0 1 := check_block (by decide +kernel)

lemma fixedDone0 : TailRegion g19frame 0 1 fixedRows0 :=
  tail_atlas g19proper g19frame g19vframe 0 1 17 fixedRows0 fixedRows1 g19rot fixedDone1 fixedChunk0x0

end OneNot

namespace OneNot

def rawTestPairs : List (Fin 512 × Fin 512) := [(21,20),(3,1),(13,9),(12,4),(17,1),(33,1),(66,2),(132,4),(264,8)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_test_pairs : ∀ a ∈ wires g19V, ∃ q ∈ rawTestPairs,
    bit target q.1 = true ∧ bit target q.2 = false ∧
    (∀ z ∈ start.toFinset, distinguishes 0 z q.1 q.2 → z = a) ∧
    (∀ z ∈ insert (0 : Word) start.toFinset, ¬distinguishes 0 (~~~z) q.1 q.2) := by
  let rise (z : Word) (q : Fin 512 × Fin 512) := bit z q.1 && !bit z q.2
  let ok (a : Word) (q : Fin 512 × Fin 512) :=
    rise target q &&
    start.all (fun z => (!rise z q || z==a)) &&
    ((0 : Word) :: start).all (fun z => !rise (~~~z) q)
  have table : (g19V.map Wire.w).all (fun w => rawTestPairs.any (ok w)) = true := by
    dsimp only [ok,rise]
    decide +kernel
  intro a ha
  have passes := List.all_eq_true.mp table a (List.mem_toFinset.mp ha)
  obtain ⟨q,present,accept⟩ := List.any_eq_true.mp passes
  obtain ⟨⟨val,only⟩,anti⟩ := (Bool.and_eq_true_iff.mp accept).imp_left Bool.and_eq_true_iff.mp
  obtain ⟨yes,hn⟩ := Bool.and_eq_true_iff.mp val
  have no : bit target q.2 = false := by simpa using hn
  refine ⟨q,present,yes,no,?_,?_⟩
  · intro z hz h
    have block := List.all_eq_true.mp only z (List.mem_toFinset.mp hz)
    change bit z q.1 = true ∧ bit z q.2 = false at h
    simpa [rise,h.1,h.2] using block
  · intro z hz h
    have mem : z ∈ (0 : Word)::start := by simpa using hz
    have block := List.all_eq_true.mp anti z mem
    change bit (~~~z) q.1 = true ∧ bit (~~~z) q.2 = false at h
    simp [rise,h.1,h.2] at block

lemma fixed_all_raw {a : Word} {n : ℕ} {T : Finset Word}
    (ha : a ∈ insert (0 : Word) start.toFinset)
    (sub : T ⊆ insert (~~~a) start.toFinset) (live : Live target n 0 T) : wires g19V ⊆ T := by
  intro w hw
  obtain ⟨q,_,yes,no,only,anti⟩ := raw_test_pairs w hw
  obtain ⟨z,hz,use⟩ := distinguishes_live live yes no
  rcases Finset.mem_insert.mp (sub hz) with rfl|base
  · exact (anti a ha use).elim
  · exact only z base use ▸ hz

lemma generic_first_flip_no {x : Word} {c : Charts x} (root : Frame c) (v : root.Valid)
    (rows next : Rows) (rot : Array (Rotation root)) (num : ℕ)
    (gn : TailRegion root 1 num next) (h : tailAtlasRow root 0 rows next num rot 0 = true)
    (s : Step c) (hs : s ∈ Step.all root.b root.t root.v) (el : eligible root.v s) :
    NoTailNeg (root.child s) := by
  let pack := fetchRow rows 0 >>> (12*0)
  let g : Frame c := {root with ps:=selectPrices root.ps 10 (pack &&& 0xffffffffff)}
  have gv : g.Valid := ⟨v.1,fun p hp => v.2 p (prices_mem hp)⟩
  have run := (Bool.and_eq_true_iff.mp h).2
  intro he
  have ok := covered_sound (f:=g) run gv.1 hs el (moreNeg he)
  have close := (Bool.or_eq_true_iff.mp ok).resolve_left (by simp)
  exact tail_local (Frame.child_valid gv el (Step.all_legal hs)) gn close he

lemma fixed_bank_split {x pivot : Word} {R S : Finset Word}
    (set : S = insert pivot R) (hx : proper x)
    (prior : ¬Feasible x 13 1 R) (base : ¬Exact x 13 0 S)
    (flip : ∀ a∈S, ∀ U, S = insert a U → ¬Exact x 13 0 (insert (~~~a) U))
    (fresh : ∀ w∈S, ~~~w ∉ S)
    (a : Word) (ha : a ∈ insert (0 : Word) S)
    (force : ∀ {n : ℕ} {T : Finset Word}, T ⊆ insert (~~~a) S → Live x n 0 T → R ⊆ T) :
    ¬Feasible x 13 0 (insert (~~~a) S) := by
  rintro ⟨n,hn,j,hj,T,sub,live⟩
  obtain rfl : j = 0 := by omega
  have allRaw := force sub live
  have full {U : Finset Word} (us : U ⊆ S) (all : R ⊆ U) (hit : pivot ∈ U) : U = S := by
    apply Finset.Subset.antisymm us
    rw [set]
    exact Finset.insert_subset hit all
  have smaller {U : Finset Word} (us : U ⊆ S) (miss : pivot ∉ U) : U ⊆ R := by
    intro w hw
    have inc := us hw
    rw [set] at inc
    exact (Finset.mem_insert.mp inc).resolve_left (by rintro rfl; exact miss hw)
  by_cases used : ~~~a ∈ T
  · rcases Finset.mem_insert.mp ha with rfl|present
    · exact (live.good hx _ used).2 BitVec.not_zero
    · let U := T.erase (~~~a)
      have us : U ⊆ S := by
        intro w hw
        obtain ⟨ne,inT⟩ := Finset.mem_erase.mp hw
        exact (Finset.mem_insert.mp (sub inT)).resolve_left ne
      have all : R ⊆ U := by
        intro w hw
        have inS : w ∈ S := set.symm ▸ Finset.mem_insert_of_mem hw
        exact Finset.mem_erase.mpr ⟨fun e => fresh a present (e ▸ inS),allRaw hw⟩
      let V := insert a U
      have vs : V ⊆ S := Finset.insert_subset present us
      have allV : R ⊆ V := all.trans (Finset.subset_insert ..)
      have rebuild : insert (~~~a) U = T := Finset.insert_erase used
      by_cases hit : pivot ∈ V
      · have eq : S=insert a U := (full vs allV hit).symm
        apply flip a present U eq
        exact ⟨n,hn,0,le_rfl,rebuild.symm ▸ live⟩
      · have toRaw := smaller vs hit
        apply prior
        apply unary_pull hx (toRaw (Finset.mem_insert_self a U))
        refine ⟨n,hn,0,le_rfl,T,?_,live⟩
        rw [←rebuild]
        exact Finset.insert_subset_insert _ ((Finset.subset_insert a U).trans toRaw)
  · have ts : T ⊆ S := by
      intro w hw
      exact (Finset.mem_insert.mp (sub hw)).resolve_left (by rintro rfl; exact used hw)
    by_cases hit : pivot ∈ T
    · apply base
      exact ⟨n,hn,0,le_rfl,full ts allRaw hit ▸ live⟩
    · exact prior ⟨n,hn,0,by decide,T,smaller ts hit,live⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fixedFresh : ∀ w∈start.toFinset, proper (~~~w) ∧ ~~~w ∉ start.toFinset := by
  have table : start.all (fun w => decide (proper (~~~w)) && !start.contains (~~~w)) = true := by decide +kernel
  intro w hw
  have ok := Bool.and_eq_true_iff.mp (List.all_eq_true.mp table w (List.mem_toFinset.mp hw))
  exact ⟨of_decide_eq_true ok.1,by simpa using ok.2⟩

lemma fixed_inputs_no
    (base : NoTailNeg g19frame)
    (first : ∀ w∈rootV, ∀ keep, eligible rootV (.flip w keep) →
        NoTailNeg (g19frame.child (.flip w keep)))
    (a : Word) (ha : a ∈ insert (0 : Word) start.toFinset) :
    ¬Feasible target 13 0 (insert (~~~a) start.toFinset) := by
  have rootSet : start.toFinset = wires rootV := by decide +kernel
  have rootParts : start.toFinset = insert extra (wires g19V) := by decide +kernel
  apply fixed_bank_split rootParts targetProper rawNo (rootSet.symm ▸ base) _
    (fun z hz => (fixedFresh z hz).2) a ha (fun sub live => fixed_all_raw ha sub live)
  intro z hz U eq
  obtain ⟨w,hw,hwv⟩ := Step.mem_wires.mp (rootSet ▸ hz)
  subst z
  let keep := decide (w.w ∈ U)
  have el : eligible rootV (.flip w keep) := ⟨(fixedFresh w.w hz).1,rootSet ▸ (fixedFresh w.w hz).2⟩
  have after := Step.next_flip (a:=w) (rootSet.symm.trans eq)
  intro he
  apply first w hw keep el
  exact after.symm ▸ he

end OneNot

namespace OneNot

lemma fixedStartNo (a : Word) (ha : a ∈ insert (0 : Word) start.toFinset) :
    ¬Feasible target 13 0 (insert (~~~a) start.toFinset) := by
  apply fixed_inputs_no (fixedDone0 0 (by decide) g19frame rfl) _ a ha
  intro w hw keep el
  apply generic_first_flip_no g19frame g19vframe fixedRows0 fixedRows1 g19rot 17 fixedDone1
    (fixedChunk0x0 0 (by decide) (by decide)) _ _ el
  exact Step.mem_flip (by decide) hw keep

end OneNot
end
end PEqualNP.Outside.L_meta_3024

namespace PEqualNP.Outside.L_meta_3024
section
namespace OneNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma fixedOnly (bound : ∀ a ∈ insert (0 : Word) start.toFinset,
    ¬ Feasible target 13 0 (insert (~~~a) start.toFinset))
    (pins : List (Fin 11)) (D : Circuit) (fan : FanInTwo D) (size : D.size ≤ 13)
    (legal : FanInTwo (⟨⟨.or,[0,2]⟩ :: ⟨.not,pins.map Fin.val⟩ :: D.gates,D.output⟩ : Circuit))
    (only : ∀ g ∈ D.gates, g.op ≠ .not)
    (computes : ∀ x : Fin 9 → Bool,
      (⟨⟨.or,[0,2]⟩ :: ⟨.not,pins.map Fin.val⟩ :: D.gates,D.output⟩ : Circuit).eval
        (List.ofFn x) = edgeF x) : False := by
  let C : Circuit := ⟨⟨.or,[0,2]⟩ :: ⟨.not,pins.map Fin.val⟩ :: D.gates,D.output⟩
  let a : Word := (pins.map (fun j => start.getD j.val 0)).headD 0
  have ha : a ∈ insert (0 : Word) start.toFinset := by
    cases pins with
    | nil => exact Finset.mem_insert_self ..
    | cons j js =>
      change start.getD j.val 0 ∈ insert 0 start.toFinset
      rw [List.getD_eq_getElem?_getD]
      cases h : start[j.val]? with
      | none => exact Finset.mem_insert_self ..
      | some v => exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_of_getElem? h))
  have first : gv raw ⟨.or,[0,2]⟩ = extra := by decide +kernel
  have second : gv start ⟨.not,pins.map Fin.val⟩ = ~~~a := by simp [gv,a,List.map_map,Function.comp_def]
  have hm := target_mem C legal computes
  change target ∈ execute D.gates ((raw ++ [gv raw ⟨.or,[0,2]⟩]) ++
    [gv (raw ++ [gv raw ⟨.or,[0,2]⟩]) ⟨.not,pins.map Fin.val⟩]) at hm
  rw [first] at hm
  change target ∈ execute D.gates (start ++ [gv start ⟨.not,pins.map Fin.val⟩]) at hm
  rw [second] at hm
  have zero : D.gates.filter negative = [] :=
    List.filter_eq_nil_iff.mpr fun g hg hn => only g hg ((neg_iff g).mp hn)
  have h := extract targetProper D.gates _ fan hm
  rw [zero] at h
  have hb := (List.length_filter_le (fun g => !negative g) D.gates).trans size
  have hs : pool (start ++ [~~~a]) = insert 0 (insert top (insert (~~~a) start.toFinset)) := by
    ext w
    simp [pool,or_comm,or_left_comm,or_assoc]
  rw [hs] at h
  exact bound a ha (ignore targetProper
    (ignore targetProper (weaken h hb (by decide) (by rfl)) (Or.inr fun q => q.1 rfl))
    (Or.inr fun q => q.2 rfl))

end OneNot
end
end PEqualNP.Outside.L_meta_3024

namespace PEqualNP.Outside.L_meta_3024.Bridge
open PEqualNP.Outside.L_meta_3024.OneNot
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 9 → Bool
def edge (x : X) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def Two := ∀ (C : Circuit), FanInTwo C → C.size ≤ 15 →
    (∀ x : X, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
    ∀ i j : Fin C.gates.length, i ≠ j → (C.gates.get i).op = .not → (C.gates.get j).op = .not →
    circuitFun 9 C = edge → False

theorem solve (h1 : ∀ a ∈ insert (0 : Word) start.toFinset, ¬ Feasible target 13 0 (insert (~~~a) start.toFinset)) (h2 : Two) : ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins bound D legal size
  by_contra! hc
  let gateA : Gate := ⟨.or,[0,2]⟩
  let gateB : Gate := ⟨.not,pins.map Fin.val⟩
  let C : Circuit := ⟨gateA :: gateB :: D.gates,D.output⟩
  have fan : FanInTwo C := by
    intro k hk
    change k ∈ gateA :: gateB :: D.gates at hk
    simp only [List.mem_cons] at hk
    rcases hk with rfl|rfl|mem
    · simp [gateA]
    · exact ⟨by simp [gateB],by simpa [gateB] using bound⟩
    · exact legal k mem
  have sz : C.size ≤ 15 := by
    simp only [C,Circuit.size,List.length_cons] at size ⊢
    omega
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have firstValue (x : X) : gateA.op.eval (gateA.inputs.map fun i => (List.ofFn x).getD i false) =
      (x 0 || x 2) := by simp [gateA,GateOp.eval]
  have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have first (x : X) : (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2) := by
    change ((gateB :: D.gates).foldl step (step (List.ofFn x) gateA)).getD 9 false = _
    rw [preserve _ _ _ (by simp [step])]
    simp [step,gateA,GateOp.eval]
  have computes : circuitFun 9 C = edge := by
    funext x
    change (D.gates.foldl step (step (step (List.ofFn x) gateA) gateB)).getD D.output false = _
    simp only [step,firstValue,gateB,List.map_map]
    exact not_ne_iff.mp (hc x)
  let i : Fin C.gates.length := ⟨1,by simp [C]⟩
  have ni : (C.gates.get i).op = .not := rfl
  by_cases multiple : ∃ j : Fin C.gates.length, j ≠ i ∧ (C.gates.get j).op = .not
  · obtain ⟨j,ne,nj⟩ := multiple
    exact h2 C fan sz first j i ne nj ni computes
  · have only (g : Gate) (hg : g ∈ D.gates) : g.op ≠ .not := by
      intro hn
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
      have idx : j.succ.succ ≠ i := by
        intro eq
        have k := congrArg Fin.val eq
        change j.val + 1 + 1 = 1 at k
        omega
      exact multiple ⟨j.succ.succ,idx,by change (D.gates.get j).op = .not; rw [hj,hn]⟩
    exact fixedOnly h1 pins D legal size fan only (fun x => congrFun computes x)

end PEqualNP.Outside.L_meta_3024.Bridge

theorem PEqualNP.Outside.L_meta_3024 : ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  apply PEqualNP.Outside.L_meta_3024.Bridge.solve PEqualNP.Outside.L_meta_3024.OneNot.fixedStartNo
  intro C legal size first i j different ni nj computes
  apply PEqualNP.Outside.L_meta_3024.Theta.no15 2 (Or.inl rfl) C legal size first _ computes
  exact PEqualNP.Outside.L_meta_3024.Theta.nc_two i j different ni nj
