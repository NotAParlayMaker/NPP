import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_182_aux

open PEqualNP.MetaComplexity

def MM : Nat := 2 ^ 64 - 1

def V : Fin 6 → Nat
  | 0 => 0xaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000
  | 5 => 0xffffffff00000000

def FT : Nat := 0xfefcfaf8eeeceae8

def litT (i : Fin 6) (b : Bool) : Nat := if b then V i else MM ^^^ V i

def tt : DMFormula 6 → Nat
  | .lit i b => litT i b
  | .and p q => tt p &&& tt q
  | .or p q => tt p ||| tt q

def lits : List Nat := (List.finRange 6).flatMap fun i => [litT i true, litT i false]

def subB (a b : Nat) : Bool := ((a &&& (MM ^^^ b)) &&& MM) == 0

def supB (a b : Nat) : Bool := subB b a

def inB (g lo hi : Nat) : Bool := subB lo g && subB g hi

def flp (i : Fin 6) (v : Nat) : Nat :=
  ((v >>> (2 ^ i.val)) &&& (MM ^^^ V i)) ||| ((v <<< (2 ^ i.val)) &&& V i)

def cnt (P : Fin 6 → Bool) : Nat :=
  (P 0).toNat + (P 1).toNat + (P 2).toNat + (P 3).toNat + (P 4).toNat + (P 5).toNat

def forced (lo hi : Nat) : Nat := cnt fun i => ((lo &&& (MM ^^^ flp i hi)) &&& MM) != 0

def addD (R : Nat → Nat → Bool) (acc : List Nat) (v : Nat) : List Nat :=
  if acc.any (fun y => R v y) then acc else acc.filter (fun y => !R y v) ++ [v]

def foldD (R : Nat → Nat → Bool) : List Nat → List Nat → List Nat
  | [], acc => acc
  | v :: l, acc =>
    if (addD R acc v).length == 0 then foldD R l (addD R acc v) else foldD R l (addD R acc v)

def Raw : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, a =>
    lits ++ (List.range (a / 2)).flatMap fun j =>
      (Raw fuel (j + 1)).flatMap fun g1 =>
        (Raw fuel (a - (j + 1))).flatMap fun g2 => [g1 ||| g2, g1 &&& g2]

def Up : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, a, hi =>
    foldD subB ((lits.filter fun g => subB g hi) ++
      (List.range (a / 2)).flatMap fun j =>
        ((Up fuel (j + 1) hi).flatMap fun g1 =>
          (Up fuel (a - (j + 1)) hi).map fun g2 => g1 ||| g2) ++
        ((Raw (j + 1) (j + 1)).flatMap fun g1 =>
          (Up fuel (a - (j + 1)) (hi ||| (MM ^^^ g1))).map fun g2 => g1 &&& g2)) []

def Dn : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, a, lo =>
    foldD supB ((lits.filter fun g => subB lo g) ++
      (List.range (a / 2)).flatMap fun j =>
        ((Dn fuel (j + 1) lo).flatMap fun g1 =>
          (Dn fuel (a - (j + 1)) lo).map fun g2 => g1 &&& g2) ++
        ((Raw (j + 1) (j + 1)).flatMap fun g1 =>
          (Dn fuel (a - (j + 1)) (lo &&& (MM ^^^ g1))).map fun g2 => g1 ||| g2)) []

def Q : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | fuel + 1, k, lo, hi =>
    if k < forced lo hi then false else
    lits.any (fun g => inB g lo hi) ||
    (List.range (k / 2)).any fun j =>
      (Up (j + 1) (j + 1) hi).any (fun g => Q fuel (k - (j + 1)) (lo &&& (MM ^^^ g)) hi) ||
      (Dn (j + 1) (j + 1) lo).any (fun g => Q fuel (k - (j + 1)) lo (hi ||| (MM ^^^ g)))

set_option maxRecDepth 100000 in
theorem key : Q 8 8 FT FT = false := by decide +kernel

theorem mmBit (t : Nat) : MM.testBit t = decide (t < 64) := Nat.testBit_two_pow_sub_one 64 t

def Le64 (a b : Nat) : Prop := ∀ t, t < 64 → a.testBit t = true → b.testBit t = true

def Mem (g lo hi : Nat) : Prop := Le64 lo g ∧ Le64 g hi

theorem le_refl64 (a : Nat) : Le64 a a := fun _ _ h => h

theorem le_trans64 {a b c : Nat} (h1 : Le64 a b) (h2 : Le64 b c) : Le64 a c :=
  fun t ht h => h2 t ht (h1 t ht h)

theorem subB_iff (a b : Nat) : subB a b = true ↔ Le64 a b := by
  unfold subB Le64
  rw [beq_iff_eq]
  constructor
  · intro h t ht ha
    have := congrArg (fun n => n.testBit t) h
    simp only [Nat.testBit_and, Nat.testBit_xor, mmBit, Nat.zero_testBit, ht, ha] at this
    cases hb : b.testBit t <;> simp_all
  · intro h
    apply Nat.eq_of_testBit_eq
    intro t
    simp only [Nat.testBit_and, Nat.testBit_xor, mmBit, Nat.zero_testBit]
    by_cases ht : t < 64
    · cases ha : a.testBit t
      · simp
      · simp [ht, h t ht ha]
    · simp [ht]

theorem subB_refl (a : Nat) : subB a a = true := (subB_iff a a).2 (le_refl64 a)

theorem subB_trans (a b c : Nat) (h1 : subB a b = true) (h2 : subB b c = true) :
    subB a c = true :=
  (subB_iff a c).2 (le_trans64 ((subB_iff a b).1 h1) ((subB_iff b c).1 h2))

theorem supB_refl (a : Nat) : supB a a = true := subB_refl a

theorem supB_trans (a b c : Nat) (h1 : supB a b = true) (h2 : supB b c = true) :
    supB a c = true := subB_trans c b a h2 h1

def Dmn (R : Nat → Nat → Bool) (l : List Nat) (x : Nat) : Prop := ∃ y ∈ l, R x y = true

theorem addD_new (R : Nat → Nat → Bool) (hr : ∀ a, R a a = true) (acc : List Nat) (v : Nat) :
    Dmn R (addD R acc v) v := by
  unfold addD
  split_ifs with h
  · rw [List.any_eq_true] at h
    obtain ⟨y, hy, hr'⟩ := h
    exact ⟨y, hy, hr'⟩
  · exact ⟨v, List.mem_append_right _ (List.mem_singleton_self v), hr v⟩

theorem addD_old (R : Nat → Nat → Bool)
    (htr : ∀ a b c, R a b = true → R b c = true → R a c = true)
    (acc : List Nat) (v x : Nat) (hx : Dmn R acc x) : Dmn R (addD R acc v) x := by
  unfold addD
  split_ifs with h
  · exact hx
  · obtain ⟨y, hy, hxy⟩ := hx
    by_cases hyv : R y v = true
    · exact ⟨v, List.mem_append_right _ (List.mem_singleton_self v), htr _ _ _ hxy hyv⟩
    · refine ⟨y, List.mem_append_left _ (List.mem_filter.2 ⟨hy, ?_⟩), hxy⟩
      simpa using hyv

theorem foldD_old (R : Nat → Nat → Bool)
    (htr : ∀ a b c, R a b = true → R b c = true → R a c = true) :
    ∀ (l acc : List Nat) (x : Nat), Dmn R acc x → Dmn R (foldD R l acc) x := by
  intro l
  induction l with
  | nil => intro acc x h; exact h
  | cons v l ih =>
    intro acc x h
    simp only [foldD, ite_self]
    exact ih _ x (addD_old R htr acc v x h)

theorem foldD_mem (R : Nat → Nat → Bool) (hr : ∀ a, R a a = true)
    (htr : ∀ a b c, R a b = true → R b c = true → R a c = true) :
    ∀ (l acc : List Nat) (x : Nat), x ∈ l → Dmn R (foldD R l acc) x := by
  intro l
  induction l with
  | nil => intro acc x h; simp at h
  | cons v l ih =>
    intro acc x h
    simp only [foldD, ite_self]
    rcases List.mem_cons.1 h with rfl | h
    · exact foldD_old R htr l _ x (addD_new R hr acc x)
    · exact ih _ x h

theorem foldD_dom (R : Nat → Nat → Bool) (hr : ∀ a, R a a = true)
    (htr : ∀ a b c, R a b = true → R b c = true → R a c = true)
    {l : List Nat} {c x : Nat} (acc : List Nat) (hc : c ∈ l) (hxc : R x c = true) :
    Dmn R (foldD R l acc) x := by
  obtain ⟨y, hy, hcy⟩ := foldD_mem R hr htr l acc c hc
  exact ⟨y, hy, htr _ _ _ hxc hcy⟩

def pt (t : Nat) : Fin 6 → Bool := fun i => t.testBit i.val

theorem vBitF : ∀ i : Fin 6, ∀ t : Fin 64, (V i).testBit t.val = t.val.testBit i.val := by
  decide +kernel

theorem vBit (i : Fin 6) (t : Nat) (ht : t < 64) : (V i).testBit t = t.testBit i.val :=
  vBitF i ⟨t, ht⟩

theorem xorLtF : ∀ i : Fin 6, ∀ t : Fin 64, t.val ^^^ 2 ^ i.val < 64 := by decide +kernel

theorem shiftF : ∀ i : Fin 6, ∀ t : Fin 64,
    (t.val.testBit i.val = false → 2 ^ i.val + t.val = t.val ^^^ 2 ^ i.val) ∧
    (t.val.testBit i.val = true → 2 ^ i.val ≤ t.val ∧ t.val - 2 ^ i.val = t.val ^^^ 2 ^ i.val) := by
  decide +kernel

theorem ttBit (φ : DMFormula 6) (t : Nat) (ht : t < 64) : (tt φ).testBit t = φ.eval (pt t) := by
  induction φ with
  | lit i b =>
    cases b
    · simp [tt, litT, DMFormula.eval, Nat.testBit_xor, mmBit, ht, pt, vBit i t ht]
    · simp [tt, litT, DMFormula.eval, pt, vBit i t ht]
  | and p q ihp ihq => simp [tt, DMFormula.eval, Nat.testBit_and, ihp, ihq]
  | or p q ihp ihq => simp [tt, DMFormula.eval, Nat.testBit_or, ihp, ihq]

theorem leaves_pos (φ : DMFormula 6) : 1 ≤ φ.leaves := by
  induction φ with
  | lit i b => simp [DMFormula.leaves]
  | and p q ihp ihq => simp only [DMFormula.leaves]; omega
  | or p q ihp ihq => simp only [DMFormula.leaves]; omega

def occ : DMFormula 6 → Fin 6 → Bool
  | .lit j _, i => decide (j = i)
  | .and p q, i => occ p i || occ q i
  | .or p q, i => occ p i || occ q i

theorem cnt_lit : ∀ j : Fin 6, cnt (fun i => decide (j = i)) = 1 := by decide

theorem cnt_or (P R : Fin 6 → Bool) : cnt (fun i => P i || R i) ≤ cnt P + cnt R := by
  have h : ∀ a b : Bool, (a || b).toNat ≤ a.toNat + b.toNat := by decide
  have := h (P 0) (R 0); have := h (P 1) (R 1); have := h (P 2) (R 2)
  have := h (P 3) (R 3); have := h (P 4) (R 4); have := h (P 5) (R 5)
  simp only [cnt]; omega

theorem cnt_mono (P R : Fin 6 → Bool) (h : ∀ i, P i = true → R i = true) : cnt P ≤ cnt R := by
  have k : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have := k _ _ (h 0); have := k _ _ (h 1); have := k _ _ (h 2)
  have := k _ _ (h 3); have := k _ _ (h 4); have := k _ _ (h 5)
  simp only [cnt]; omega

theorem cnt_occ (φ : DMFormula 6) : cnt (occ φ) ≤ φ.leaves := by
  induction φ with
  | lit j b => simp only [occ, DMFormula.leaves, cnt_lit j]; exact le_rfl
  | and p q ihp ihq =>
    simp only [DMFormula.leaves]
    exact (cnt_or (occ p) (occ q)).trans (by omega)
  | or p q ihp ihq =>
    simp only [DMFormula.leaves]
    exact (cnt_or (occ p) (occ q)).trans (by omega)

theorem eval_indep (φ : DMFormula 6) (i : Fin 6) (ho : occ φ i = false) (x y : Fin 6 → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) : φ.eval x = φ.eval y := by
  induction φ with
  | lit j b =>
    have hj : j ≠ i := by simpa [occ] using ho
    simp [DMFormula.eval, hxy j hj]
  | and p q ihp ihq =>
    simp only [occ, Bool.or_eq_false_iff] at ho
    simp [DMFormula.eval, ihp ho.1, ihq ho.2]
  | or p q ihp ihq =>
    simp only [occ, Bool.or_eq_false_iff] at ho
    simp [DMFormula.eval, ihp ho.1, ihq ho.2]

theorem flipInv {φ : DMFormula 6} {i : Fin 6} (ho : occ φ i = false) (t : Nat) (ht : t < 64) :
    (tt φ).testBit (t ^^^ 2 ^ i.val) = (tt φ).testBit t := by
  rw [ttBit φ _ (xorLtF i ⟨t, ht⟩), ttBit φ t ht]
  apply eval_indep φ i ho
  intro j hj
  have hv : j.val ≠ i.val := fun h => hj (Fin.ext h)
  simp [pt, Nat.testBit_xor, Ne.symm hv]

theorem flpBit (i : Fin 6) (v t : Nat) (ht : t < 64) :
    (flp i v).testBit t = v.testBit (t ^^^ 2 ^ i.val) := by
  have hf := shiftF i ⟨t, ht⟩
  simp only [flp, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, mmBit, vBit i t ht] at hf ⊢
  cases hb : t.testBit i.val
  · rw [← hf.1 hb]; simp [ht]
  · obtain ⟨h1, h2⟩ := hf.2 hb
    rw [← h2]; simp [ht, h1]

theorem forced_le {φ : DMFormula 6} {lo hi : Nat} (hm : Mem (tt φ) lo hi) :
    forced lo hi ≤ φ.leaves := by
  refine le_trans ?_ (cnt_occ φ)
  apply cnt_mono
  intro i hc
  by_contra hne
  have ho : occ φ i = false := by simpa using hne
  have hz : ((lo &&& (MM ^^^ flp i hi)) &&& MM) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro t
    simp only [Nat.testBit_and, Nat.testBit_xor, mmBit, Nat.zero_testBit]
    by_cases ht : t < 64
    · rw [flpBit i hi t ht]
      cases hl : lo.testBit t
      · simp
      · have h1 := hm.1 t ht hl
        rw [← flipInv ho t ht] at h1
        have h2 := hm.2 _ (xorLtF i ⟨t, ht⟩) h1
        simp [ht, h2]
    · simp [ht]
  simp [hz] at hc

theorem inB_of_Mem {g lo hi : Nat} (h : Mem g lo hi) : inB g lo hi = true := by
  simp [inB, (subB_iff lo g).2 h.1, (subB_iff g hi).2 h.2]

theorem le_or_left {x y hi : Nat} (h : Le64 (x ||| y) hi) : Le64 x hi := by
  intro t ht hx
  exact h t ht (by simp [Nat.testBit_or, hx])

theorem le_or_right {x y hi : Nat} (h : Le64 (x ||| y) hi) : Le64 y hi := by
  intro t ht hy
  exact h t ht (by simp [Nat.testBit_or, hy])

theorem le_and_left {x y lo : Nat} (h : Le64 lo (x &&& y)) : Le64 lo x := by
  intro t ht hl
  have := h t ht hl
  simp only [Nat.testBit_and, Bool.and_eq_true] at this
  exact this.1

theorem le_and_right {x y lo : Nat} (h : Le64 lo (x &&& y)) : Le64 lo y := by
  intro t ht hl
  have := h t ht hl
  simp only [Nat.testBit_and, Bool.and_eq_true] at this
  exact this.2

theorem le_or_or {x y g1 g2 : Nat} (h1 : Le64 x g1) (h2 : Le64 y g2) :
    Le64 (x ||| y) (g1 ||| g2) := by
  intro t ht h
  simp only [Nat.testBit_or, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (h1 t ht h)
  · exact Or.inr (h2 t ht h)

theorem le_and_and {x y g1 g2 : Nat} (h1 : Le64 x g1) (h2 : Le64 y g2) :
    Le64 (x &&& y) (g1 &&& g2) := by
  intro t ht h
  simp only [Nat.testBit_and, Bool.and_eq_true] at h ⊢
  exact ⟨h1 t ht h.1, h2 t ht h.2⟩

theorem le_cut_or {lo p q g : Nat} (h : Le64 lo (p ||| q)) (hg : Le64 p g) :
    Le64 (lo &&& (MM ^^^ g)) q := by
  intro t ht h1
  have := h t ht
  have hpg := hg t ht
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, mmBit, ht] at h1 this
  cases hp : p.testBit t <;> cases hq : q.testBit t <;> cases hl : lo.testBit t <;>
    cases hgg : g.testBit t <;> simp_all

theorem le_cut_and {hi p q g : Nat} (h : Le64 (p &&& q) hi) (hg : Le64 g p) :
    Le64 q (hi ||| (MM ^^^ g)) := by
  intro t ht h1
  have := h t ht
  have hpg := hg t ht
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, mmBit, ht] at this ⊢
  cases hp : p.testBit t <;> cases hh : hi.testBit t <;>
    cases hgg : g.testBit t <;> simp_all

theorem lit_mem (i : Fin 6) (b : Bool) : litT i b ∈ lits := by
  simp only [lits, List.mem_flatMap, List.mem_finRange, true_and]
  exact ⟨i, by cases b <;> simp⟩

theorem Raw_complete : ∀ fuel a (φ : DMFormula 6), a ≤ fuel → φ.leaves ≤ a →
    tt φ ∈ Raw fuel a := by
  intro fuel
  induction fuel with
  | zero =>
    intro a φ ha hl
    have := leaves_pos φ
    omega
  | succ fuel IH =>
    intro a φ ha hl
    rw [Raw]
    cases φ with
    | lit i b => exact List.mem_append_left _ (lit_mem i b)
    | or p q =>
      apply List.mem_append_right
      simp only [DMFormula.leaves] at hl
      have hp1 := leaves_pos p
      have hq1 := leaves_pos q
      rcases le_total p.leaves q.leaves with hpq | hqp
      · rw [List.mem_flatMap]
        refine ⟨p.leaves - 1, List.mem_range.2 (by omega), ?_⟩
        have e : p.leaves - 1 + 1 = p.leaves := by omega
        rw [e, List.mem_flatMap]
        refine ⟨tt p, IH _ p (by omega) le_rfl, ?_⟩
        rw [List.mem_flatMap]
        exact ⟨tt q, IH _ q (by omega) (by omega), by simp [tt]⟩
      · rw [List.mem_flatMap]
        refine ⟨q.leaves - 1, List.mem_range.2 (by omega), ?_⟩
        have e : q.leaves - 1 + 1 = q.leaves := by omega
        rw [e, List.mem_flatMap]
        refine ⟨tt q, IH _ q (by omega) le_rfl, ?_⟩
        rw [List.mem_flatMap]
        exact ⟨tt p, IH _ p (by omega) (by omega), by simp [tt, Nat.lor_comm]⟩
    | and p q =>
      apply List.mem_append_right
      simp only [DMFormula.leaves] at hl
      have hp1 := leaves_pos p
      have hq1 := leaves_pos q
      rcases le_total p.leaves q.leaves with hpq | hqp
      · rw [List.mem_flatMap]
        refine ⟨p.leaves - 1, List.mem_range.2 (by omega), ?_⟩
        have e : p.leaves - 1 + 1 = p.leaves := by omega
        rw [e, List.mem_flatMap]
        refine ⟨tt p, IH _ p (by omega) le_rfl, ?_⟩
        rw [List.mem_flatMap]
        exact ⟨tt q, IH _ q (by omega) (by omega), by simp [tt]⟩
      · rw [List.mem_flatMap]
        refine ⟨q.leaves - 1, List.mem_range.2 (by omega), ?_⟩
        have e : q.leaves - 1 + 1 = q.leaves := by omega
        rw [e, List.mem_flatMap]
        refine ⟨tt q, IH _ q (by omega) le_rfl, ?_⟩
        rw [List.mem_flatMap]
        exact ⟨tt p, IH _ p (by omega) (by omega), by simp [tt, Nat.land_comm]⟩

theorem Up_complete : ∀ fuel a hi (φ : DMFormula 6), a ≤ fuel → φ.leaves ≤ a →
    Le64 (tt φ) hi → Dmn subB (Up fuel a hi) (tt φ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a hi φ ha hl _
    have := leaves_pos φ
    omega
  | succ fuel IH =>
    intro a hi φ ha hl hs
    rw [Up]
    cases φ with
    | lit i b =>
      refine foldD_dom subB subB_refl subB_trans [] (c := tt (.lit i b)) ?_ (subB_refl _)
      exact List.mem_append_left _ (List.mem_filter.2 ⟨lit_mem i b, (subB_iff _ _).2 hs⟩)
    | or p q =>
      simp only [DMFormula.leaves] at hl
      have hp1 := leaves_pos p
      have hq1 := leaves_pos q
      rcases le_total p.leaves q.leaves with hpq | hqp
      · obtain ⟨g1, hg1, s1⟩ := IH _ hi p (by omega) le_rfl (le_or_left hs)
        obtain ⟨g2, hg2, s2⟩ := IH (a - p.leaves) hi q (by omega) (by omega) (le_or_right hs)
        refine foldD_dom subB subB_refl subB_trans [] (c := g1 ||| g2) ?_ ?_
        · apply List.mem_append_right
          rw [List.mem_flatMap]
          refine ⟨p.leaves - 1, List.mem_range.2 (by omega), ?_⟩
          have e : p.leaves - 1 + 1 = p.leaves := by omega
          rw [e]
          apply List.mem_append_left
          rw [List.mem_flatMap]
          exact ⟨g1, hg1, List.mem_map.2 ⟨g2, hg2, rfl⟩⟩
        · exact (subB_iff _ _).2 (le_or_or ((subB_iff _ _).1 s1) ((subB_iff _ _).1 s2))
      · have hs' : Le64 (tt q ||| tt p) hi := by rw [Nat.lor_comm]; exact hs
        obtain ⟨g1, hg1, s1⟩ := IH _ hi q (by omega) le_rfl (le_or_left hs')
        obtain ⟨g2, hg2, s2⟩ := IH (a - q.leaves) hi p (by omega) (by omega) (le_or_right hs')
        refine foldD_dom subB subB_refl subB_trans [] (c := g1 ||| g2) ?_ ?_
        · apply List.mem_append_right
          rw [List.mem_flatMap]
          refine ⟨q.leaves - 1, List.mem_range.2 (by omega), ?_⟩
          have e : q.leaves - 1 + 1 = q.leaves := by omega
          rw [e]
          apply List.mem_append_left
          rw [List.mem_flatMap]
          exact ⟨g1, hg1, List.mem_map.2 ⟨g2, hg2, rfl⟩⟩
        · have := le_or_or ((subB_iff _ _).1 s1) ((subB_iff _ _).1 s2)
          rw [Nat.lor_comm] at this
          exact (subB_iff _ _).2 this
    | and p q =>
      simp only [DMFormula.leaves] at hl
      have hp1 := leaves_pos p
      have hq1 := leaves_pos q
      rcases le_total p.leaves q.leaves with hpq | hqp
      · have hr := Raw_complete p.leaves p.leaves p le_rfl le_rfl
        obtain ⟨g2, hg2, s2⟩ := IH (a - p.leaves) (hi ||| (MM ^^^ tt p)) q (by omega) (by omega)
          (le_cut_and hs (le_refl64 _))
        refine foldD_dom subB subB_refl subB_trans [] (c := tt p &&& g2) ?_ ?_
        · apply List.mem_append_right
          rw [List.mem_flatMap]
          refine ⟨p.leaves - 1, List.mem_range.2 (by omega), ?_⟩
          have e : p.leaves - 1 + 1 = p.leaves := by omega
          rw [e]
          apply List.mem_append_right
          rw [List.mem_flatMap]
          exact ⟨tt p, hr, List.mem_map.2 ⟨g2, hg2, rfl⟩⟩
        · exact (subB_iff _ _).2 (le_and_and (le_refl64 _) ((subB_iff _ _).1 s2))
      · have hs' : Le64 (tt q &&& tt p) hi := by rw [Nat.land_comm]; exact hs
        have hr := Raw_complete q.leaves q.leaves q le_rfl le_rfl
        obtain ⟨g2, hg2, s2⟩ := IH (a - q.leaves) (hi ||| (MM ^^^ tt q)) p (by omega) (by omega)
          (le_cut_and hs' (le_refl64 _))
        refine foldD_dom subB subB_refl subB_trans [] (c := tt q &&& g2) ?_ ?_
        · apply List.mem_append_right
          rw [List.mem_flatMap]
          refine ⟨q.leaves - 1, List.mem_range.2 (by omega), ?_⟩
          have e : q.leaves - 1 + 1 = q.leaves := by omega
          rw [e]
          apply List.mem_append_right
          rw [List.mem_flatMap]
          exact ⟨tt q, hr, List.mem_map.2 ⟨g2, hg2, rfl⟩⟩
        · have := le_and_and (le_refl64 (tt q)) ((subB_iff _ _).1 s2)
          have h2 : Le64 (tt p &&& tt q) (tt q &&& g2) := by rw [Nat.land_comm]; exact this
          exact (subB_iff _ _).2 h2

theorem Dn_complete : ∀ fuel a lo (φ : DMFormula 6), a ≤ fuel → φ.leaves ≤ a →
    Le64 lo (tt φ) → Dmn supB (Dn fuel a lo) (tt φ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a lo φ ha hl _
    have := leaves_pos φ
    omega
  | succ fuel IH =>
    intro a lo φ ha hl hs
    rw [Dn]
    cases φ with
    | lit i b =>
      refine foldD_dom supB supB_refl supB_trans [] (c := tt (.lit i b)) ?_ (supB_refl _)
      exact List.mem_append_left _ (List.mem_filter.2 ⟨lit_mem i b, (subB_iff _ _).2 hs⟩)
    | and p q =>
      simp only [DMFormula.leaves] at hl
      have hp1 := leaves_pos p
      have hq1 := leaves_pos q
      rcases le_total p.leaves q.leaves with hpq | hqp
      · obtain ⟨g1, hg1, s1⟩ := IH _ lo p (by omega) le_rfl (le_and_left hs)
        obtain ⟨g2, hg2, s2⟩ := IH (a - p.leaves) lo q (by omega) (by omega) (le_and_right hs)
        refine foldD_dom supB supB_refl supB_trans [] (c := g1 &&& g2) ?_ ?_
        · apply List.mem_append_right
          rw [List.mem_flatMap]
          refine ⟨p.leaves - 1, List.mem_range.2 (by omega), ?_⟩
          have e : p.leaves - 1 + 1 = p.leaves := by omega
          rw [e]
          apply List.mem_append_left
          rw [List.mem_flatMap]
          exact ⟨g1, hg1, List.mem_map.2 ⟨g2, hg2, rfl⟩⟩
        · exact (subB_iff _ _).2 (le_and_and ((subB_iff _ _).1 s1) ((subB_iff _ _).1 s2))
      · have hs' : Le64 lo (tt q &&& tt p) := by rw [Nat.land_comm]; exact hs
        obtain ⟨g1, hg1, s1⟩ := IH _ lo q (by omega) le_rfl (le_and_left hs')
        obtain ⟨g2, hg2, s2⟩ := IH (a - q.leaves) lo p (by omega) (by omega) (le_and_right hs')
        refine foldD_dom supB supB_refl supB_trans [] (c := g1 &&& g2) ?_ ?_
        · apply List.mem_append_right
          rw [List.mem_flatMap]
          refine ⟨q.leaves - 1, List.mem_range.2 (by omega), ?_⟩
          have e : q.leaves - 1 + 1 = q.leaves := by omega
          rw [e]
          apply List.mem_append_left
          rw [List.mem_flatMap]
          exact ⟨g1, hg1, List.mem_map.2 ⟨g2, hg2, rfl⟩⟩
        · have := le_and_and ((subB_iff _ _).1 s1) ((subB_iff _ _).1 s2)
          have h2 : Le64 (g1 &&& g2) (tt p &&& tt q) := by rw [Nat.land_comm (tt p)]; exact this
          exact (subB_iff _ _).2 h2
    | or p q =>
      simp only [DMFormula.leaves] at hl
      have hp1 := leaves_pos p
      have hq1 := leaves_pos q
      rcases le_total p.leaves q.leaves with hpq | hqp
      · have hr := Raw_complete p.leaves p.leaves p le_rfl le_rfl
        obtain ⟨g2, hg2, s2⟩ := IH (a - p.leaves) (lo &&& (MM ^^^ tt p)) q (by omega) (by omega)
          (le_cut_or hs (le_refl64 _))
        refine foldD_dom supB supB_refl supB_trans [] (c := tt p ||| g2) ?_ ?_
        · apply List.mem_append_right
          rw [List.mem_flatMap]
          refine ⟨p.leaves - 1, List.mem_range.2 (by omega), ?_⟩
          have e : p.leaves - 1 + 1 = p.leaves := by omega
          rw [e]
          apply List.mem_append_right
          rw [List.mem_flatMap]
          exact ⟨tt p, hr, List.mem_map.2 ⟨g2, hg2, rfl⟩⟩
        · exact (subB_iff _ _).2 (le_or_or (le_refl64 _) ((subB_iff _ _).1 s2))
      · have hs' : Le64 lo (tt q ||| tt p) := by rw [Nat.lor_comm]; exact hs
        have hr := Raw_complete q.leaves q.leaves q le_rfl le_rfl
        obtain ⟨g2, hg2, s2⟩ := IH (a - q.leaves) (lo &&& (MM ^^^ tt q)) p (by omega) (by omega)
          (le_cut_or hs' (le_refl64 _))
        refine foldD_dom supB supB_refl supB_trans [] (c := tt q ||| g2) ?_ ?_
        · apply List.mem_append_right
          rw [List.mem_flatMap]
          refine ⟨q.leaves - 1, List.mem_range.2 (by omega), ?_⟩
          have e : q.leaves - 1 + 1 = q.leaves := by omega
          rw [e]
          apply List.mem_append_right
          rw [List.mem_flatMap]
          exact ⟨tt q, hr, List.mem_map.2 ⟨g2, hg2, rfl⟩⟩
        · have := le_or_or (le_refl64 (tt q)) ((subB_iff _ _).1 s2)
          have h2 : Le64 (tt q ||| g2) (tt p ||| tt q) := by rw [Nat.lor_comm (tt p)]; exact this
          exact (subB_iff _ _).2 h2

theorem Q_sound : ∀ fuel k lo hi, Q fuel k lo hi = false →
    ∀ φ : DMFormula 6, φ.leaves ≤ k → ¬ Mem (tt φ) lo hi := by
  intro fuel
  induction fuel with
  | zero => intro k lo hi hQ; simp [Q] at hQ
  | succ fuel IH =>
    intro k lo hi hQ φ hl hm
    have hfor := forced_le hm
    rw [Q] at hQ
    split_ifs at hQ with hc
    · omega
    rw [Bool.or_eq_false_iff] at hQ
    obtain ⟨hlit, hQ⟩ := hQ
    rw [List.any_eq_false] at hQ
    cases φ with
    | lit i b =>
      rw [List.any_eq_false] at hlit
      exact hlit _ (lit_mem i b) (inB_of_Mem hm)
    | or p q =>
      simp only [DMFormula.leaves] at hl
      have hp1 := leaves_pos p
      have hq1 := leaves_pos q
      rcases le_total p.leaves q.leaves with hpq | hqp
      · have h := hQ (p.leaves - 1) (List.mem_range.2 (by omega))
        have e : p.leaves - 1 + 1 = p.leaves := by omega
        rw [e, Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_true,
          List.any_eq_false] at h
        obtain ⟨g, hg, s⟩ := Up_complete _ _ hi p le_rfl le_rfl (le_or_left hm.2)
        have h2 := h.1 g hg
        rw [Bool.not_eq_true] at h2
        exact IH _ _ _ h2 q (by omega)
          ⟨le_cut_or hm.1 ((subB_iff _ _).1 s), le_or_right hm.2⟩
      · have h := hQ (q.leaves - 1) (List.mem_range.2 (by omega))
        have e : q.leaves - 1 + 1 = q.leaves := by omega
        rw [e, Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_true,
          List.any_eq_false] at h
        have hm' : Mem (tt q ||| tt p) lo hi := by
          constructor
          · rw [Nat.lor_comm]; exact hm.1
          · rw [Nat.lor_comm]; exact hm.2
        obtain ⟨g, hg, s⟩ := Up_complete _ _ hi q le_rfl le_rfl (le_or_left hm'.2)
        have h2 := h.1 g hg
        rw [Bool.not_eq_true] at h2
        exact IH _ _ _ h2 p (by omega)
          ⟨le_cut_or hm'.1 ((subB_iff _ _).1 s), le_or_right hm'.2⟩
    | and p q =>
      simp only [DMFormula.leaves] at hl
      have hp1 := leaves_pos p
      have hq1 := leaves_pos q
      rcases le_total p.leaves q.leaves with hpq | hqp
      · have h := hQ (p.leaves - 1) (List.mem_range.2 (by omega))
        have e : p.leaves - 1 + 1 = p.leaves := by omega
        rw [e, Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_true,
          List.any_eq_false, List.any_eq_false] at h
        obtain ⟨g, hg, s⟩ := Dn_complete _ _ lo p le_rfl le_rfl (le_and_left hm.1)
        have h2 := h.2 g hg
        rw [Bool.not_eq_true] at h2
        exact IH _ _ _ h2 q (by omega)
          ⟨le_and_right hm.1, le_cut_and hm.2 ((subB_iff _ _).1 s)⟩
      · have h := hQ (q.leaves - 1) (List.mem_range.2 (by omega))
        have e : q.leaves - 1 + 1 = q.leaves := by omega
        rw [e, Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_true,
          List.any_eq_false, List.any_eq_false] at h
        have hm' : Mem (tt q &&& tt p) lo hi := by
          constructor
          · rw [Nat.land_comm]; exact hm.1
          · rw [Nat.land_comm]; exact hm.2
        obtain ⟨g, hg, s⟩ := Dn_complete _ _ lo q le_rfl le_rfl (le_and_left hm'.1)
        have h2 := h.2 g hg
        rw [Bool.not_eq_true] at h2
        exact IH _ _ _ h2 p (by omega)
          ⟨le_and_right hm'.1, le_cut_and hm'.2 ((subB_iff _ _).1 s)⟩

def phi9 : DMFormula 6 :=
  .or (.or (.and (.lit 0 true) (.or (.lit 1 true) (.or (.lit 2 true) (.lit 3 true))))
    (.and (.lit 1 true) (.or (.lit 2 true) (.lit 4 true)))) (.and (.lit 2 true) (.lit 5 true))

theorem phi9_leaves : phi9.leaves = 9 := rfl

theorem phi9_eval : ∀ x : Fin 6 → Bool, phi9.eval x =
    ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4) ||
      (x 2 && x 5)) := by
  intro x
  simp only [phi9, DMFormula.eval, ↓reduceIte]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl

theorem ftBit : ∀ t : Fin 64, FT.testBit t.val =
    ((pt t.val 0 && pt t.val 1) || (pt t.val 0 && pt t.val 2) || (pt t.val 1 && pt t.val 2) ||
      (pt t.val 0 && pt t.val 3) || (pt t.val 1 && pt t.val 4) || (pt t.val 2 && pt t.val 5)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_182_aux

open PEqualNP.Outside.L_meta_182_aux in
theorem PEqualNP.Outside.L_meta_182 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) s ↔ 9 ≤ s := by
  intro s
  constructor
  · rintro ⟨φ, hl, he⟩
    by_contra hs
    apply Q_sound 8 8 FT FT key φ (by omega)
    have hb : ∀ t, t < 64 → (tt φ).testBit t = FT.testBit t := by
      intro t ht
      rw [ttBit φ t ht, he (pt t)]
      exact (ftBit ⟨t, ht⟩).symm
    exact ⟨fun t ht h => by rw [hb t ht]; exact h, fun t ht h => by rw [← hb t ht]; exact h⟩
  · intro hs
    exact ⟨phi9, by rw [phi9_leaves]; exact hs, phi9_eval⟩
