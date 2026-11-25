import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- The checker of live-state certificates with cofactor cuts (the generic part, up to the data) is the one of the checked
-- V_meta_9945__k9 (same repository, Apache-2.0); the certificates below are new.

namespace PEqualNP.Outside.L_meta_12925_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

theorem availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

theorem andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

theorem orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

theorem negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD d1 T s ws) {roots p bank}
    (hp : NatReach d roots p bank) (hs : ∀ w ∈ ws, Avail d bank w) :
    ∃ q next, NatReach d roots q next ∧ Avail d next T ∧
      q + ws.countP (isConstB d) ≤ p + s := by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false := by
      cases hc : isConstB d T with
      | false => rfl
      | true => exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p, bank, hp, hs T (by simp), by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q, next, hq, ht, hle⟩ := ih hp (fun w hw => hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q, next, hq, ht, hle⟩
  | @one s a r save _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    by_cases hca : IsConst d a
    · have hc_neg : IsConst d (negD d1 a) := by
        have e := negD_and_sub hd hsub a
        rcases negD_const hd hca with h0 | h1
        · exact Or.inl (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h0))
        · exact Or.inr (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h1))
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact Or.inl hc_neg
        · exact hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw])
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have h1 : isConstB d (negD d1 a) = true := (isConstB_iff _ _).2 hc_neg
      have h2 : isConstB d a = true := (isConstB_iff _ _).2 hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h1, h2, ite_true] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hreach' : NatReach d roots (p + 1) (negD d a :: bank) := Or.inl ⟨bank, a, rfl, hp, ha⟩
      have hneg_av : Avail d (negD d a :: bank) (negD d1 a) :=
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD, Nat.and_assoc, Nat.and_self]⟩
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d (negD d a :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hneg_av
        · exact avail_cons _ _ (hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw]))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have h2 : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd ((isConstB_iff _ _).1 h) hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h2, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
  | @two s a b r conj ka kb _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := if conj then andD d1 a b else orD d1 a b
    set z0 := binD d (!conj) a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      cases conj
      · simp only [z1, z0, Bool.false_eq_true, ite_false, Bool.not_false, binD, ite_true]
        rw [orD_and_sub hsub]; simp [orD, Nat.and_assoc, Nat.and_self]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD, Nat.and_assoc, Nat.and_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases binD_const_left (!conj) hca with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
        · dsimp only [z0]; rw [binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0) := by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true := (isConstB_iff _ _).2 hca
          rcases binD_const_left (!conj) hca with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by
              simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = binD d (!conj) b a &&& d := by rw [hz_eq, binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by
              simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach d roots (p + 1) (z0 :: bank) := Or.inr ⟨bank, a, b, !conj, rfl, hp, ha, hb⟩
      have hz_av : Avail d (z0 :: bank) z1 := Or.inr ⟨z0, List.mem_cons_self, hz_eq.symm⟩
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d (z0 :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons, hna, hnb, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩

-- Backward extraction: NatReach d roots p bank + Avail d bank T -> RunD d (T &&& d) s ws!
theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

-- Essential variable lemma + lower_slice + lower_base + lower_iso!
theorem runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem lower_base {d : Nat} {roots : List Nat} {T : Nat} (h : availB d roots T = false) :
    Lower d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

-- moveBits & lower_iso!
def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK256 (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) && (moveBits p.1 p.2 mask256 == mask256)

theorem applyMoves_hom (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b, applyMoves ms (a &&& b) = applyMoves ms a &&& applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ||| b) = applyMoves ms a ||| applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ^^^ b) = applyMoves ms a ^^^ applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256 := by
  induction ms with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    obtain ⟨⟨hz, hm⟩, hps⟩ := hok
    obtain ⟨hand, hor, hxor, h0, h256⟩ := ih hps
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves, List.foldl_cons, move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves, List.foldl_cons, hm]; exact h256

theorem move_invol (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1, ite_true, moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false := by
      have htd := congrArg (fun v : Nat => v.testBit (d + i)) h
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at htd
      have hge : d ≤ d + i := Nat.le_add_right d i
      have hsub : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [hge, hsub, h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
    simp [h2, h3, Nat.add_sub_cancel_left]
  · simp only [h1, ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp [h2.2, Nat.add_sub_of_le h2.1]
    · simp [h1, h2, moved tag d i w h]

theorem applyMoves_inj (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms) := by
  induction ms with
  | nil => intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves, List.foldl_cons] at h
    have h1 := ih hok.2 h
    have := congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1, move_invol p.1 p.2 b hok.1.1] at this

theorem applyMoves_runD {d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD d Y s ws) :
    RunD d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  have hneg : ∀ a, applyMoves ms (negD d a) = negD d (applyMoves ms a) := fun a => by
    simp only [negD, hand, hxor, h256, hd]
  have hand' : ∀ a b, applyMoves ms (andD d a b) = andD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [andD, hand, hd]
  have hor' : ∀ a b, applyMoves ms (orD d a b) = orD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [orD, hand, hor, hd]
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @one s a r save hne0 hned hnm _ ih =>
    have e1 : (negD d a :: kept save a r).map (applyMoves ms) =
        negD d (applyMoves ms a) :: kept save (applyMoves ms a) (r.map (applyMoves ms)) := by
      simp [kept_map, hneg]
    rw [e1] at ih
    refine Run.one save ?_ ?_ ?_ ih
    · intro e; rw [← hneg] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← hneg] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← hneg, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)
  | @two s a b r conj ka kb hne0 hned hnm _ ih =>
    have eop : applyMoves ms (if conj then andD d a b else orD d a b) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) := by
      cases conj <;> simp [hand', hor']
    have e1 : ((if conj then andD d a b else orD d a b) :: kept ka a (kept kb b r)).map (applyMoves ms) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two conj ka kb ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach d2 roots2 p bank →
      ∃ bank', NatReach d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail d1 b' (applyMoves ms v)) →
      Avail d2 b w → Avail d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha
      refine ⟨negD d1 (applyMoves ms a) :: b', Or.inl ⟨b', applyMoves ms a, rfl, hrb', ha'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨negD d1 (applyMoves ms a), List.mem_cons_self, by simp only [negD, hand, hxor, h256, hd]⟩
      · exact avail_cons _ _ (hbb v hv)
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha; have hc' := hav hbb hc
      refine ⟨binD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
        Or.inr ⟨b', applyMoves ms a, applyMoves ms c, op, rfl, hrb', ha', hc'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨binD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
          cases op <;> simp only [binD, andD, orD, hand, hor, hd, ite_true, ite_false, Bool.false_eq_true]⟩
      · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower d1 roots1 T1 L) : Lower d2 roots2 T2 L := by
  obtain ⟨hand, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)

-- lower_slice!
def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

theorem countP_ge_sublist (p : Nat → Bool) {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) (hall : ∀ a ∈ xs, p a = true) :
    xs.length ≤ ys.countP p := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have ham : a ∈ ys := hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a) := List.perm_cons_erase ham
    rw [hperm.countP_eq, List.countP_cons, hall a List.mem_cons_self]
    have ih' := ih hnd' (fun x hx => by
      have hne : x ≠ a := fun e => hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true, List.length_cons]
    omega

theorem lower_slice {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower dSub rootsSub TSub L) :
    Lower d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail dSub next TSub := avail_of_eq (by
    rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht
  have hL : L ≤ q := hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst, a ∈ ws := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok (a', r1, r2) hm
    simp only [Bool.and_eq_true, essOK, pairOK, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨_, ⟨⟨hr1, hr2⟩, hdiff⟩, hiso⟩ := hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst, isConstB dSub a = true := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt := countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega

-- poolCut (compact 52-bit hint!) + covers + eval6 + bar!
def runChoices (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if ia < pool.length && (op == 2 || ib < pool.length) then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      let w := if op == 2 then negD d a else binD d (op == 1) a b
      runChoices d (pool ++ [w]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach d roots q bank →
      (∀ v ∈ pool, Avail d bank v) →
      runChoices d pool p bits = some result →
      ∃ bank', NatReach d roots (q + p) bank' ∧ ∀ v ∈ result, Avail d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨hia, hopb⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := if op == 2 then negD d a else binD d (op == 1) a b
      have ha : Avail d bank a := hsup a (getD_mem hia)
      have hr1 : NatReach d roots (q + 1) (w :: bank) := by
        by_cases h2 : op = 2
        · simp only [w, h2, beq_self_eq_true, ite_true]
          exact Or.inl ⟨bank, a, rfl, hr, ha⟩
        · have hib : ib < pool.length := hopb.resolve_left h2
          have hb : Avail d bank b := hsup b (getD_mem hib)
          simp only [w, h2, beq_iff_eq, ite_false]
          exact Or.inr ⟨bank, a, b, (op == 1), rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB dSub pool)

theorem checkCutEntry_sound {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry dSub rootsSub LSub s ws hint = true) :
    ¬ RunD d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail dSub rootsSub v := fun v hv => Or.inr ⟨v, hv, rfl⟩
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail dSub bank w := by
      intro w hw
      have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

-- covers, eval6, hw256, hk, bsr, bar, bar_all!
def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u, v⟩ hm
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

-- Fast bitmask-decorated covers (150x faster than per-pair testBit!)
def maskP (m : Nat) : Nat := 2 ^ m - 1

def projBit (rs : List Nat) (w : Nat) : Nat :=
  rs.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0

theorem projBit_testBit (rs : List Nat) (w : Nat) (i : Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false := by
  induction rs generalizing i with
  | nil => simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one, decide_false, Bool.false_and, Bool.false_or,
        List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i), decide_true, Bool.true_and, Nat.add_sub_cancel,
        List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false := by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1, Bool.or_false]; exact ih i

theorem projBit_negD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (w : Nat) :
    projBit rs (negD dm w) = projBit rs w ^^^ maskP rs.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_xor, projBit_testBit, maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    simp [hi, negD, hdr, hmr]
  · simp [hi]

theorem projBit_andD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (andD dm a b) = projBit rs a &&& projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_and, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, andD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem projBit_orD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (orD dm a b) = projBit rs a ||| projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_or, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, orD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def coversD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  if dws.length == s + 1 then
    dws.foldl (fun acc d => acc ||| ((d.2.1 ^^^ mp) &&& d.2.2)) 0 == mp
  else
    dws.foldl (fun acc d => acc ||| (d.2.1 ^^^ d.2.2)) 0 == mp

theorem coversD_eq (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) :
    coversD (maskP pairs.length) s (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP pairs s ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  simp only [List.length_map]
  split
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
        Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
            Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true, r1s, r2s, List.getElem_map]
          exact hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Nat.testBit_two_pow_sub_one, decide_false, Bool.xor_false, Bool.and_false, not_false_eq_true, Bool.false_eq_true]
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s, bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true, r1s, r2s, List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Bool.xor_false, Bool.false_eq_true, not_false_eq_true]

theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x == f a) = false := beq_false_of_ne (fun e => h (hinj e))
      have hx : (x == a) = false := beq_false_of_ne h
      simp [hf, hx, ih]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, andD, Nat.testBit_and, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, orD, Nat.testBit_and, Nat.testBit_or, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih => rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]; omega

def scoreCheck (dm y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code &&& 255
  let b := (code >>> 8) &&& 255
  let c := (code >>> 16) &&& 255
  let d := (code >>> 24) &&& 255
  let e := (code >>> 32) &&& 255
  let f := (code >>> 40) &&& 255
  dm.testBit a && dm.testBit b && dm.testBit c && dm.testBit d && dm.testBit e && dm.testBit f &&
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)

theorem scoreCheck_no {dm y s ws} (h : RunD dm y s ws) (code : Nat) :
    scoreCheck dm y s ws code = false := by
  unfold scoreCheck
  by_cases hok : dm.testBit (code &&& 255) = true ∧ dm.testBit ((code >>> 8) &&& 255) = true ∧
      dm.testBit ((code >>> 16) &&& 255) = true ∧ dm.testBit ((code >>> 24) &&& 255) = true ∧
      dm.testBit ((code >>> 32) &&& 255) = true ∧ dm.testBit ((code >>> 40) &&& 255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hok
    simp only [ha, hb, hc, hd, he, hf, hl, beq_self_eq_true, Bool.true_and]
    by_contra hbad
    have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht := Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1, ht.1.1.1.1.1.1.2, ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2, ht.1.2⟩

def scr (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD dm y s zs) : scr dm y s pool zs = false := by
  unfold scr; rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
  intro x _; rw [scoreCheck_no h x]; simp

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat :=
  (T >>> (w * i)) &&& (if w == 32 then 4294967295 else if w == 52 then 4503599627370495 else if w == 256 then mask256 else 2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w % 170141183460469231731687303715884105727) ^^^ seed) * 0x9e3779b97f4a7c15f39cc0605cedc835) &&& 0xffffffffffffffffffffffffffffffff
  let y := ((x ^^^ (x >>> 61)) * 0xc2b2ae3d27d4eb4f165667b19e3779f9) &&& 0xffffffffffffffffffffffffffffffff
  y >>> 96

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  let i := idxH s h
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

def nextD_decor (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
         let dw := (w, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
         (f (dw :: ra) || (slack ≥ 2 && f (dw :: da :: ra))))) ||
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := if conj then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                      else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hneg : ∀ a, (negD dm a, (dec a).2.1 ^^^ mp, (dec a).2.2 ^^^ mp) = dec (negD dm a))
    (hbin : ∀ (c : Bool) a b,
      (if c then (if c then andD dm a b else orD dm a b, (dec a).2.1 &&& (dec b).2.1, (dec a).2.2 &&& (dec b).2.2)
       else (if c then andD dm a b else orD dm a b, (dec a).2.1 ||| (dec b).2.1, (dec a).2.2 ||| (dec b).2.2)) =
      dec (if c then andD dm a b else orD dm a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor dm mp slack (ws.map dec) g = nextD dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hneg, hbin, List.map_cons]

theorem nextD_decor_eq {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor dm (maskP pairs.length) slack (ws.map dec) g =
      nextD dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro a
    simp only [dec, projBit_negD hd hr1, projBit_negD hd hr2, List.length_map]
  · intro c a b
    cases c <;> simp only [dec, ↓reduceIte, Bool.false_eq_true, projBit_andD hr1, projBit_andD hr2,
      projBit_orD hr1, projBit_orD hr2]

def colB (mp : Nat) (d : Bool) (p : Nat × Nat) : Nat :=
  if d then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def addC (x : Nat) (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (c.1 ||| x, c.2.1 ||| (c.1 &&& x), c.2.2 ||| (c.2.1 &&& x))

def cov3 (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  dws.foldl (fun c dw => addC (colB mp d dw.2) c) (0, 0, 0)

def takeOne (c : Nat × Nat × Nat) (x : Nat) : Nat := (c.1 ^^^ x) ||| c.2.1
def takeTwo (c : Nat × Nat × Nat) (x y : Nat) : Nat :=
  (c.1 ^^^ (x ||| y)) ||| (c.2.1 &&& (x ^^^ y)) ||| c.2.2

theorem cov3_bit (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) (i : Nat) :
    let k := dws.countP (fun dw => (colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k) := by
  have hgen : ∀ (xs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (k0 : Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k := k0 + xs.countP (fun dw => (colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k) := by
    intro xs
    induction xs with
    | nil => intro c k0 ⟨h1, h2, h3⟩; simp [h1, h2, h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1, h2, h3⟩
      simp only [List.foldl_cons, List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) := by
        simp only [addC, Nat.testBit_or, Nat.testBit_and, h1, h2, h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb, Nat.le_add_left]
      have ih' := ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using ih'
  simpa only [cov3, Nat.zero_testBit, Nat.zero_add] using hgen dws (0, 0, 0) 0 (by simp)

theorem cov3_perm (mp : Nat) (d : Bool) {xs ys : List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys := by
  have heq : ∀ i, (cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i := by
    intro i
    obtain ⟨a1, a2, a3⟩ := cov3_bit mp d xs i
    obtain ⟨b1, b2, b3⟩ := cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i => (heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.2)

theorem takeOne_eq (mp : Nat) (d : Bool) (a : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, _⟩ := cov3_bit mp d (a :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeOne, Nat.testBit_or, Nat.testBit_xor, h1, h2, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, decide_true, Bool.xor_false, Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 1 ≤ k + 3 by omega,
      decide_true, Bool.xor_true, Bool.or_true, Bool.or_false]

theorem takeTwo_eq (mp : Nat) (d : Bool) (a b : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, h3⟩ := cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeTwo, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2, h3, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega, show 2 ≤ k + 3 + 1 + 1 by omega, show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true, Bool.xor_true, Bool.xor_false, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false])

theorem cov3_coversD (mp s : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    let d := (dw :: rest).length == s + 1
    ((cov3 mp d rest).1 ||| colB mp d dw.2 == mp) = coversD mp s (dw :: rest) := by
  intro d
  have e : ∀ b : Bool, ((cov3 mp b rest).1 ||| colB mp b dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp b x.2) 0 := by
    intro b; apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp b rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp b dw.2).testBit i)) =
        rest.any (fun x => (colB mp b x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  have hf : ∀ b : Bool, (cov3 mp b rest).1 ||| colB mp b dw.2 =
      (dw :: rest).foldl (fun acc x => acc ||| (if b then (x.2.1 ^^^ mp) &&& x.2.2 else x.2.1 ^^^ x.2.2)) 0 := by
    intro b; simpa only [colB] using e b
  unfold coversD
  dsimp only [d]
  cases (dw :: rest).length == s + 1
  · simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg (· == mp) (hf false)
  · simpa only [↓reduceIte] using congrArg (· == mp) (hf true)

def nextD_cov (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let len := dws.length
  let covF := cov3 mp false dws
  let covT := cov3 mp true dws
  let du0 := len == s + 1
  let du1 := len + 1 == s + 1
  let db0 := len - 1 == s + 1
  let db1 := len == s + 1
  let db2 := len + 1 == s + 1
  dws.any fun da =>
    let a := da.1
    (slack ≥ 1 &&
      (let pneg := (da.2.1 ^^^ mp, da.2.2 ^^^ mp)
       let uok0 := (takeOne (if du0 then covT else covF) (colB mp du0 da.2) ||| colB mp du0 pneg) == mp
       let uok1 := slack ≥ 2 && (((if du1 then covT.1 else covF.1) ||| colB mp du1 pneg) == mp)
       (uok0 || uok1) &&
       (let w := negD dm a
        w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
          let dw := (w, pneg)
          let ra := dws.erase da
          ((uok0 && f (dw :: ra)) || (uok1 && f (dw :: da :: ra)))))) ||
    (dws.erase da).any fun db =>
      let b := db.1
      a ≤ b &&
        [false, true].any fun conj =>
          let pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                    else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
          let ok0 := (takeTwo (if db0 then covT else covF) (colB mp db0 da.2) (colB mp db0 db.2) ||| colB mp db0 pz) == mp
          let ok1a := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 db.2) ||| colB mp db1 pz) == mp)
          let ok1b := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 da.2) ||| colB mp db1 pz) == mp)
          let ok2 := slack ≥ 2 && (((if db2 then covT.1 else covF.1) ||| colB mp db2 pz) == mp)
          (ok0 || ok1a || ok1b || ok2) &&
          (let w := if conj then andD dm a b else orD dm a b
           w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
             let dw := (w, pz)
             let r := (dws.erase da).erase db
             ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) || (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r))))

theorem nextD_cov_eq (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov dm mp s slack dws g =
      nextD_decor dm mp slack dws (fun dzs => coversD mp s dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      refine ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra
        rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 :
          (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra)
        rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hu0, hf0⟩ | ⟨⟨hsl2, hu1⟩, hf1⟩
      · left; exact ⟨hcov0 ▸ hu0, hf0⟩
      · right; exact ⟨hsl2, hcov1 ▸ hu1, hf1⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw]
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r
      rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r)
      rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r)
      rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r)
      rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
      · left; left; exact ⟨hcov0' ▸ hu0, hf0⟩
      · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a' ▸ hu1a, hf1a⟩⟩
      · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b' ▸ hu1b, hf1b⟩⟩
      · right; exact ⟨hsl2, hcov2' ▸ hu2, hf2⟩
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra; rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra); rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hc0, hg0⟩ | ⟨hsl2, hc1, hg1⟩
      · have hu0 : ((takeOne _ _ ||| _) == mp) = true := hcov0.symm ▸ hc0
        exact ⟨hsl, Or.inl hu0, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl ⟨hu0, hg0⟩⟩
      · have hu1 : ((_ ||| _) == mp) = true := hcov1.symm ▸ hc1
        exact ⟨hsl, Or.inr ⟨hsl2, hu1⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, hu1⟩, hg1⟩⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw] at hfx
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r; rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r); rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r); rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r); rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
      · have u0 : ((takeTwo _ _ _ ||| _) == mp) = true := hcov0'.symm ▸ hc0
        exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
      · have u1a : ((takeOne _ _ ||| _) == mp) = true := hcov1a'.symm ▸ hc1a
        exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
      · have u1b : ((takeOne _ _ ||| _) == mp) = true := hcov1b'.symm ▸ hc1b
        exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
      · have u2 : ((_ ||| _) == mp) = true := hcov2'.symm ▸ hc2'
        exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [bar, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runD {dm Y u} (seed : Nat) (orig : List Nat) (h0 : RunD dm Y u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD dm Y u best →
      RunD dm Y u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

-- Bridge: HasCircuitSize 8 fG s -> Lower mask256 xs256 (enc256 fG) lb -> lb <= s!
def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : mask256.testBit r = true := by simp [mask256_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach mask256 roots p bank →
      (∀ v ∈ w, Avail mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail mask256 bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    -- Use gvN_step directly on roots=roots:
    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases mask256.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD mask256 (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def xs256 : List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def pt8 (r : Nat) : Fin 8 → Bool := fun i => r.testBit i.val

theorem xs256_bits : ∀ r : Fin 256, xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val) := by
  decide +kernel

theorem lower_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hlow : Lower mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := hlow p bank hr (avail_of_eq hout hav_out)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def dom_0 : Nat := 0x333300003333
def goal_0 : Nat := 0x322200002220
def roots_0 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (1, 33), (4, 5), (8, 9), (12, 13), (12, 44), (32, 33), (36, 37), (36, 44), (40, 41), (40, 44)]
def r1sG : List Nat := [1, 1, 1, 4, 8, 12, 12, 32, 36, 36, 40, 40]
def r2sG : List Nat := [5, 9, 33, 5, 9, 13, 44, 33, 37, 44, 41, 44]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x96d781175fd96f7a383fd74e1ba39e6d18fb680e
  | 4, 0 => 0x96d7811761e0065050253a17467e268340f14df3347d9e1e2b55f9c60a8683ff01745ddd
  | 5, 0 => 0x96d78117
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3030000000000000300000003000000022220000222200002222000000000000220000002200000011110000111100000033000000330000000000003333
  | 0, 1 => 0x3333000030300000333300002222000033330000220000003333000000000000333000003330000033220000000000003300000033000000303000003030
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc9854cb654d9854a9854e9844
  | 4, 0, 0 => 0xc9854c98755ec9855c98525fc98550c9824c98515098504c98535
  | 5, 0, 0 => 0xc9854
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x300060007000000ff838f07f
  | 0, 1 => 0xfe8f87f80f80f78c00c70368
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb40a605bf584432a4018d03b
  | 0, 1 => 0xfedfffff6fc4f7bfc4e72b69
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 16 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 16 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 16 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 16 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_0 == dom_0) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_0 goalM u ys) : RunD dom_0 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 9 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 8 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 9 → Z 4 i = true := range_split z4_0 (z4_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_0 roots_0 goal_0 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_0 goal_0 := by
    have h0 : isConstB dom_0 goal_0 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_0

theorem low_0 : Lower dom_0 roots_0 goal_0 6 := S_0.noCircuit

def dom_1 : Nat := 0x505000005050
def goal_1 : Nat := 0x504000004000
def roots_1 : List Nat := [0x404000004040, 0x500000005000, 0x505000000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(6, 14), (6, 38), (12, 14), (12, 44), (36, 38), (36, 44)]
def r1sG : List Nat := [6, 6, 12, 12, 36, 36]
def r2sG : List Nat := [14, 38, 14, 44, 38, 44]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xffbcba87
  | 3, 0 => 0xffbcba87
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50500000000000005000000050000000404000004040
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x30303
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ab57
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 6 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 6 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 3 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_1 == dom_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_1 goalM u ys) : RunD dom_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_1 roots_1 goal_1 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_1 goal_1 := by
    have h0 : isConstB dom_1 goal_1 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_1

theorem low_1 : Lower dom_1 roots_1 goal_1 4 := S_1.noCircuit

def dom_2 : Nat := 0x555500005555
def goal_2 : Nat := 0x544400004000
def roots_2 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x505000005050, 10, 14)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xcccc
def goal_3 : Nat := 0xc880
def roots_3 : List Nat := [0x8888, 0xc0c0, 0xcc00]

theorem low_3 : Lower dom_3 roots_3 goal_3 4 :=
  lower_iso [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_4 : Nat := 0xcccc0000cccc
def goal_4 : Nat := 0xcccc0000c880
def roots_4 : List Nat := [0x888800008888, 0xc0c00000c0c0, 0xcc000000cc00, 0xcccc00000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc00000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xf0f00000f0f0
def goal_5 : Nat := 0xf0e00000e0a0
def roots_5 : List Nat := [0xa0a00000a0a0, 0xc0c00000c0c0, 0xf0000000f000, 0xf0f000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xff000000ff00
def goal_6 : Nat := 0xfe000000ea00
def roots_6 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0xffff
def goal_7 : Nat := 0xeaa0
def roots_7 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc, 12, 14)] (by decide +kernel) (by decide +kernel) low_3

def dom_8 : Nat := 0xf0f00000f0f
def goal_8 : Nat := 0xe0e00000a00
def roots_8 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]

namespace S_8
def pairsG : List (Nat × Nat) := [(1, 9), (1, 33), (2, 34), (3, 11), (3, 35), (8, 9), (10, 11), (10, 42), (32, 33), (32, 34), (40, 41), (40, 42)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 8, 10, 10, 32, 32, 40, 40]
def r2sG : List Nat := [9, 33, 34, 11, 35, 9, 11, 42, 33, 34, 41, 42]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_8.map (· &&& dom_8)
def goalM : Nat := goal_8 &&& dom_8
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x12562096
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f0000000f0000000c0c00000c0c00000a0a00000a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf00ce00dc01b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf96ce9adc57b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_8 == dom_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_8 goalM u ys) : RunD dom_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_8 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_8 roots_8 goal_8 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_8 goal_8 := by
    have h0 : isConstB dom_8 goal_8 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_8

theorem low_8 : Lower dom_8 roots_8 goal_8 4 := S_8.noCircuit

def dom_9 : Nat := 0xff000000ff
def goal_9 : Nat := 0xee000000a0
def roots_9 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xffff0000ffff
def goal_10 : Nat := 0xfeee0000eaa0
def roots_10 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_10
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (1, 33), (2, 34), (3, 7), (3, 11), (3, 35), (4, 5), (6, 7), (6, 14), (6, 38), (8, 9), (10, 11), (10, 14), (10, 42), (12, 13), (12, 14), (12, 44), (32, 33), (32, 34), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 6, 6, 6, 8, 10, 10, 10, 12, 12, 12, 32, 32, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [5, 9, 33, 34, 7, 11, 35, 5, 7, 14, 38, 9, 11, 14, 42, 13, 14, 44, 33, 34, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10
def NN : Nat → Nat
  | 3 => 20
  | 4 => 77
  | 5 => 235
  | 6 => 177
  | 7 => 20
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe63840b7937b96658592d5937d4547bf711422b970c4f7a46bf5d83567c4574c63b8dd5060b4905757715116485bdeea3aa2fe633817a3892585e0012166f10d159d38321443b9c013d9ec5e087d3f5d
  | 4, 0 => 0x8751c1e0845bb62883a768248066742a802c5dd57e4568f27ca23b1f7c68c5c97b9c30b57b589d367a318c8477da021276f8b921756e03fe732fcd1172c1fea965470c3f5dfbc4ed57332c075052a6d4501442f35013041b4b44489a4a36e5db4828de3044918a68441d2cf642a6fdf0416d36904068c7033fd89b8d3f49fe9a3b79fda93a52ecf7391c29bc35c32ee12e8880542d371cb62d04aef62c70a9a62b8f5aa72b34bedf2824a1f2280a4e5a2717a657257ef3802219908f20d798331c047bb11ad27d7919c537f1192ee58515db6bd613aaa69f0ece41040a76c1790a10ff3307784d9a053ab12e053a16ad05232ceb04c5669203048829021bc62f
  | 4, 1 => 0xfeb8195df450a049d39f90aece56fc4dcb5438f9b9f8843baa2facd1a61f67de953a82b290feccd48e3432078c38064c8858455b
  | 5, 0 => 0x2fc73ac72f77bd082e9c610c2d3feb842ce817ae2ce05d762cda9d9b2cade0302bfe08e12bcb016d2b69386e2b4f95472a404c4a29bde7a8293c5012286a923627a349ba26ec230f2593969721ce392c214a53a52071c3a41faf13761f997ca71da574181d3147fc1ca0d95b1c5f4b161b993fe71b5072e31b0c3aa21a9e6cad1a94717b1a2ea5cd19a1be771955899117d2457f1761702a169e26fd15ea327514ee45e8147ef64e13557876102c32d1102bb16b102236070ddc6dcc0d272c780d11957f0c7f030f0ae8f58b0a8c8ae3098b9f95084dae50083247eb0806af7b07b9063707932729077ce4510753ebba070585160615cd6903d488a8024a8d64
  | 5, 1 => 0x61eb6a73602b62e35fa5c9f45eeaed085c29e13d5c14cb205bfd61255a4c90a159e8a4b5577c4a3f5723b5e0563aeaf85626a3a355054229545d95db53ef3e295313e22d513157fc510143c550316dca4ff2325b4f5f80134ef488984eb608604ea85bd14db367e74c4b01eb4852222d4645ba4d460c1b7c44be7810436929d442cea36342c1d77f42829c104209718940cdc37340a415794094391b407c713d4001a9113fee32863fd89b8d3f96c4c43f1b44b23e0e1f743dcee4053db9f6cb3daffb993ada8b763a82c52f3a680dbf39e84e8937a1247235c7eb3233b8e883332728f032ac34bf32a35fca32691c6f323af20731efdabb3185218930bbdcd3
  | 5, 2 => 0xa1ca86109e1adc539c6edc609c6b12ca9bef1128994cc9a49927696098902bdf9807bc6d96ab46e595baac0f92f281ba91d7f25090a64fff8f0342038e929da58e0650568cccd4978c65fb0b8c5e4fdb8bd8c5dd8b82f3df8b350f0988e2183d874aa95c842e603282e9bc0381747ea28145bb7c8003bc3d7f6875937f4c7a937f30553e7df0050b7d5304ef7d193cfe7c8aaddd7b2bd17679a499a37970b2bb788a381e77974d5e771e0baa7595a9717379b4b071d779ec71631c7a710eb81b6e467e2d6d1e8b116c8fee1e6b56d8cd69d015c068bfed2d67ace89f6798dc7b676a9463676144bc6695b78f6692046265f7e3b46568174462e019c262934835
  | 5, 3 => 0xf9c5145af84e125df28a7ce2f0f748ecee021f3ced3be1e0eba8e591e9f8c2fde4152e2fe24e8d55e1b7f040dfba0224dda43e41d92dfe35d7759c55d562be30d339121cd0d5b72ace05b724ccebeb0fc9161bcbc2755e80bf8a667ebf330337bf2f2950bc7f3d8ebc2a4ca6bbabb5fdb91eb561b5c89896b49f6311b3011602b2d36ee6b07a353badac63aea9e82aa3a71fc0a1a6054621a5d4577ea56ea90ca3c3fbb4a2734473a1f99583
  | 6, 0 => 0x3f2fe7c93e548bcd3d5c70f23916f65f3666694e362fac123588d347354997d83499db3e346384283412153c33cafe5432ea57673234260c318663ed3147287e308db4e42f73b0202e76e1ef2e1b67d12e1b47802db92d382d3feb842c21c6632acab2b2290acf4c289d02bc2760d706270b03de26aa9c5025a509332592baa524c110fc246ba9d9235e67ac21428e212071c3a4203288351c4b186b1b2929df1ad9a3b2175f758d17108ead13645f70133a607611ea638f10f68b1e10af74360e2c67630d3657590cfff1a80c1f3c870b6e94320afba44c09d78a7509063c4506e68d66064ff05105d51b1b05c687990581789e03b0c7d70366aa4100f3632b
  | 6, 1 => 0x9f3b309b9d95886498c851bd9674c193913e7e27910d9f0a8efb7c7f8d0b2fb08cad58428c30dc8c89d5516188e2183d88929210884b7b288469a56483bbed1f836c66f28325500a81c2784781352dad8059d1b17fed28667d0eb13b7bf68f677a9c0dc477a6a4ab77571e7e74dbfda0737f75f7734c6e626fa9a6b36ee798d96d1e8b116c9f26ad6bec16726ad259566a837b956991ce24686e9bda6692046265c68e1f63f1beb46280fe876241c3185ba073fa5b61388b5a282ac15788170a5758cfc4545902464fada6a44f8fff5f4c002e804b5a61c14a4616bf4a2b96a84a21a97049c6266e492f895945c6b42943767a4442e7b68d42c1d77f42829c10
  | 6, 2 => 0xfcf0f3d1fbeade87fb544172fb0f828bfa78e576f9c5145af80d9fc1f359f987f18d7981f0f748ecee021f3ced6b8227ebdc5388e6883c41e5ace045e2b26cfde1d71101e0195e6adf376d53d8cf5469d7f3f86dd54d9339d4c9adb2d3f11db1d385f72ed1d9f73bd109eb38cbfec521cae6951ec6fe0e4cc6e0ece0c66d58e4c0871139bcfdd44cb9abea8fb91eb561b9154d7ab5ec5618b5acf684b58b625ab4b0065eaebaa387ae8ffcf9a871c0faa7a2a188a6c7458ca60109aca1c0b4b8a0737905
  | 7, 0 => 0xe505bdfad3f11db1a1c0b4b8a1712e8ba12a17a395fc1c0b8c5e12728888432e7ea52a9a7445a6b56949f7d6686e9bda5ba073fa5b61388b4d7877b92fef2b28270b03de160058940f1fce070da784ce
  | 8, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000f0f0000000000000eeee000000000000aaaa0000000000005f5f00000000000055ff00000000000055550000000000000fff
  | 0, 1 => 0x5ff000005ff0000055500000555000000ff000000ff0000005500005555000000000000ffff000000000000fff0000000000000ffcc000000000000ffaa
  | 0, 2 => 0x5050000050500000444400004444000033330000333300001f1f00001f1f000011110000111100000fff00000fff00000ff000000ff000000f0f00000f0f
  | 0, 3 => 0xa0a00000a0a00000555500005555000055550000505000005555000044440000555500000000000055500000555000005544000055440000550000005500
  | 0, 4 => 0xaf0f0000af0f0000aaff0000aaff0000aaff000000ff0000aaaa0000fafa0000aaaa0000aaaa0000aaaa000055550000aaaa000000000000aa000000aa00
  | 0, 5 => 0xecec0000ec000000e0e00000e0e00000e0000000e0000000cfcf0000cfcf0000cccc0000eeee0000cccc0000cccc0000cccc0000c0000000afaf0000afaf
  | 0, 6 => 0xeeee0000e0000000eeee0000cccc0000eeee0000aaaa0000eeee000000000000eee00000eee00000eecc0000eecc0000ee000000ee000000ecec0000ecec
  | 0, 7 => 0xf0f00000a0a00000f0f0000000000000f0a00000f0a00000f0000000f0000000eeee0000eeee0000eeee0000ee000000eeee0000eaaa0000eeee0000e0e0
  | 0, 8 => 0xfaaa0000f0000000fa000000fa000000f0ff0000f0ff0000f0f00000f0f00000f0f00000f0a00000f0f00000f0000000f0f00000e0e00000f0f00000c0c0
  | 0, 9 => 0xfafa0000fafa0000fafa0000f0f00000fafa0000c8c80000fafa0000aaaa0000faf00000faf00000faea0000faea0000fac80000fac80000faaa0000faaa
  | 0, 10 => 0xff00000000000000fefe0000f0f00000fcfc0000fcfc0000fcfc0000fc000000fcfc0000a8a80000fcec0000fcec0000fccc0000fccc0000fc000000fc00
  | 0, 11 => 0xffaa0000aaaa0000ffa00000ffa00000ffa00000a0a00000ff000000ff000000ff000000fa000000ff000000cc000000ff000000aa000000ff000000a000
  | 0, 12 => 0xfff00000ccc00000fff00000aaa00000ffcc0000ffcc0000ffaa0000ffaa0000ffaa0000ff000000ffaa0000faaa0000ffaa0000f0a00000ffaa0000eeaa
  | 0, 13 => 0xffff0000aaaa0000ffff0000aa000000ffff0000a0a00000ffff000055000000ffff00000f0f0000ffff000000ff0000ffff000000000000fff00000fff0
  | 0, 14 => 0xffff0000f0a00000ffff0000f0000000ffff0000eeee0000ffff0000eecc0000ffff0000ee000000ffff0000e0e00000ffff0000e0000000ffff0000cccc
  | 0, 15 => 0xffff0000ffaa0000ffff0000ffa00000ffff0000ff000000ffff0000fafa0000ffff0000faaa0000ffff0000fa000000ffff0000f0f00000ffff0000f0c0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xdf722374d319fbb4fb767aa4e77e23b4d3661bb4b931c2a4b311d234d39a42a4d3724384fdb642a4b931db84d3219aa4f3ba42a4dfa23aa4df11e3a4d399e3b4
  | 3, 0, 1 => 0xd321db3401726383b931c234df6623a4
  | 4, 0, 0 => 0xd319dae46bbedc4548577dc88d18ae9d121da35dfa1e2a42bbee41548574bc66a91a80d2a91914f971faa42b71f3b708d74dc9efddaefb911db85f3a6e4876be6e3e648d7cee78a91ae9b2f55235
  | 4, 0, 1 => 0xf3bee3c76bbf4e878ed74dc88bd1ae9ccf15235f9a6e3f76bbb4c888a977dc8f1152e9c3115205e37223b46be6e4c76a974dc88dd1ae9b8f1c23501a7448769fb6bc548d74e6b911dafdbb115235
  | 4, 0, 2 => 0xdf7223846a03cdc98ed34c65ca91a80dd2222a4dfa6e4470be6e4c768d74e48d11daf3af11da35e5bee4476bef4dc88ed74c88d11dadc7ce15235dfa6e3d76bbee4470a974dc9111daefd36e23b5
  | 4, 0, 3 => 0xdf72b3b46bf6cc4768d74dc90ed72e9d121e3b5fd6222a46ba6edc9ea974e2b911dafdd32151f5d2f55230ebe77dc90a977e9d12152e9bf11db15f391f2a40a02e3e708d006fb911c269d0f1b235
  | 4, 0, 4 => 0x76df7223b5d3a243b54ba5e3b668d7b69b911cae9d11d5235fb7e7c454bf77d988ed77dc88a91280df72b3b4d3661aa46a02e44548934bc548c52f2b911a235
  | 5, 0, 0 => 0xd37244476a98069b8c11905f3bee4476a9b4dc9b115236d38e22a4641b4dc88c918b6f3a6e42548db4dc88a91806d372242768d8069768c80d5017221e2c2d406988ecf0d5df7223b688d806db911195501a644454814044465468b5
  | 5, 0, 1 => 0xf3bf4dc88edbaefb9115216017222a460d406988d918d5ffa6cc4548d806fd3722135d37293d548db4e4b93222a601bee4476d14069d0f1da3501f6fc4548d406996a918d5d37223b461db4dc88a91886d39622a461dbcdc7ced5236
  | 5, 0, 2 => 0xd3727aa4619b4dc88a919c6e1a743c548d806fb8a9090501a6e1e2a414069b8ed1905d396e4e548db4e4b3115236d3a28bc548db4dc93115236f3bae44548db4dc88f9923601a6e3d768d7cdc7ca91a06d37223b748db76988f15236
  | 5, 0, 3 => 0xf3bee44768db7e8b9115216df7223c5485b4dc88f1da3601a672a463574dc95115236eda6e44528db869b8f55236edbee44548dbce9c91152060172232462d77e98d11523601a6e44708d7869bd115236f3a6e40548db4dc88cd5236
  | 5, 0, 4 => 0x1e77dc88ed406988a918f5017151e202d7969b9115236d9a6e44548db9e9b911da36dfa6e4476d5b4dc88ed1926d376e44548dbfefb9115216efa6e44548dbce9b9215236d37223b4651b4dc9111da36eda743c548db4dc88d918d6
  | 5, 0, 5 => 0xd37264476a98069548c80d501a622a3c357ed788a919e6d3722324641b4e888a9198601a6e2a4e8d74e8b5115236d382e44548d8079b8f9da3501a6e4888ed76dcb1115236fdb6e44548d8069b88c990501a6e443c4d406e88f15235
  | 5, 0, 6 => 0xdfa6e4478ed806988a92a35f1a6e44548d807daea9190501f6bc4547974e6b9115236d37222a4631806fb9110955017222b462d4044768c68b501a6e56768d406eb8a9190501bf4dc764174dc88a918e6d37223b508dbd698d115236
  | 5, 0, 7 => 0xd37222a4625b75c88a9182601a6344547977e9c97223b6df72ac45485b4dc9ea8f8b601a621e2c3574d788ed8a36d37222a46658069c8a90105ffbf4dc88edb4dc88e9523601a742a46497ce5b8f9523601a7448548d77e9d17223b6
  | 5, 0, 8 => 0xd37222a4669b4dc91115236dfa6dc4548db75c88a918b6fba5e2a467dbcefb8f15236d372644768db7e9d0f15236017221e2a2d405c88a90815db96e44548d805c88ed18b501a6e4f3e5577e9b9055236f3a6e2a465db86db9115236
  | 5, 0, 9 => 0x1727aa3e2d74dc88ed1816df7222a4241807daf111955e9bae44548d805c88ec5845f371f2a4635b4dc88ed1856d392344548dbce9b8f55236d37223d768d8069b93223b5d37222a4609bde9b9115236d322344548db4dc78ed7236
  | 5, 0, 10 => 0xd3a1e2a467980698d11195501bee44762d74e8b911b23601a6e44760574dc88f1b236db7222a46358044548c68b5d5a6e44768d805c888c98b5d31a22a462db4e7b9115236d372a44548db4dc88ed6a36dd7223e548db7dc88a90816
  | 5, 0, 11 => 0xdfa6e447641bee9a1115236fba6cc4548dbed79f11523601a743c547974dca7115236d37244478edb4dc96a918b6df72cc45485b4dcb311da36d386e44548db7e9b92222a6d392ac45481b7e9b911db1601a551e203574e488f95206
  | 5, 0, 12 => 0x1725aa462d74dc88a91816eda6e44768db4dc88a91856d39222a4041805c88ecf0b5d3727bb5c8db4e890f15236d38ae44548d806988c118d5011a22a462d74dc88a918a6d31a23b548db7e9b911d81601a6e4b46557ee9b9118236
  | 5, 0, 13 => 0xd392e4f88edb4dcaaf5523601b6e2a46417eefb311523600a91901a2d74dc88a919d6d372234628db4dc88a92236d3a1e2a46858069d0f11955e1a6e4f547d807db3115235d3a1e2a462d8069b9391955dfa6e5988ed8069465480d5
  | 5, 0, 14 => 0x6fd37223b5fbe74bc548dbce9b8f1da36eda6e44548d805c88a8f0b5d37223b668db4dc9eb95236edc2e44548db4dc8f11523601a1e2a462d74e878ed5236
  | 6, 0, 0 => 0x1bf4c4548c6b6fd37223f548df4e4b93e22a46e034dc88f9195601a62c4548c6b0001a724454817ce9cb7222a46ff77e9b91152370192e44548c5b69c97223b548dfcf0d37222a46e034dc888d0956d372ac4548c5b8001f6bc4548d4069b91151e20dbf4e5b9115237
  | 6, 0, 1 => 0xd37223e76a91b80d37162a4641b869b9115233ce034dc9f11195600034dc768c828001a6e44767974e4b91152320e0005c888ca8b501a6e44467cab69b93e22a462dc079d3115231ac000698d115235d372ac4548d0bfdf3a6e44548df4dc88a919f16fa6e4476a918b7
  | 6, 0, 2 => 0x1a6e444654837dd37222a4679fce9b9115231ae035e9b911523601a745c88ed1b00f3a6e3c548d8069b911e3b46c03eefb911523601a6e4688a91b0001a6e4b548d405cab1152316da72dc88a919e701bf4dc88a91b69b911523202dc069bf7222a46dbf4dc88a918d7
  | 6, 0, 3 => 0xe1a745c88a91bf0d37223c548dc07dd37222a3cc034e4b911da36d3728c478a91be9b95622a4681c069cb7152320c034e5b91151e601a622a46786b69b9115234241c05c88a919f16c02e4476a918b6d37223e548d038001a6e446c8d4070d37152320c03869b91151e6
  | 6, 0, 4 => 0xd37222a468083e9b95e22a4679c000d3a1e2a46a034c478a918d6d37222a46786b80d37222a461dbb69b911e2a46fc34e4b911523701a6e445478c300b911523202db4dc88ed52320e00069b939523501a6e44768c5b00d372242548d8000d2a91901aa0006988a8f0d5
  | 6, 0, 5 => 0x1a6e4888a91b69cb7223e548dfaefd37222a46e034dc88ed8a3601f74dc888cab00dba6e44548d8069b911e2a46c0005c88ed18b501a622a46345b00d372240548d8069b95d52320c034dcaf1151e600034dc548c828001a6e4454794069b8a91901ac034dc88f9da36
  | 6, 0, 6 => 0xfba6e44548cfbfdd37223b548df4e5b93e22a46fbf4e8b9115237dfa6e4478a91b80d37222a508d805c88a918b0cc034dc88ed190601af4dc548c8300e17222a462db869b9115233ee00069b910f16501a622a46846b00dfa6e4454798000d3111951aa034dc88a91926
  | 6, 0, 7 => 0x1a6e3c548cfb00d37222a465d8000d37223246a034c4548d00d6d37223e548c6be9cb7222a4641c0699f115231adc34dc88a9190700036dc88a91aefd392e44548dfee9b93e22a46e00044548c68b501a622a467c6b00d311daa4635bfefd37222a46e03edc88a918b6
  | 6, 0, 8 => 0xd37222a46785b80df7222a462d8069b91152302dbf4dc88ed523701f74dc88ed1b69b9115232035c069d17222a3cc034dc88f151e6d372bcf88a91b80d3115264635805c88a918b08da745c88a919e7d37223c548cf380d372231548d8000b91152316a037e9b9111956
  | 6, 0, 9 => 0x17222a46785b00d371f2a4641b4e8b91152316fa6e4478a918b700037dc88a90a8001a6e443c554000d37223b46a034dca111523601a6e5988a91b6fd37222a4605c069b911db446c034dc88a8f0b601bf4dc88ed5300d3722233c55b4dc9111e2a46e034e4b91151e6
  | 6, 0, 10 => 0x1a2e44548c5b69d17223b548dc05c88f152316da6e4478ed523700037e9b911da80d3722232a2d8069b91151e36c00069b911193501db4dc88a91b00017222a3c2d4069b911daa3cc037e9b911da36d3a2e44548d0be9b911e2a4685c069d1722232ac034dc88f11956
  | 6, 0, 11 => 0x1c37e9b9115237
  | 7, 0, 0 => 0xd37223b548db4dcab115236d37222a46858069b9111955d37222a462db4e4b9115236d3a2e44548db4dc88f1523601a6e2a46414069b91151e5d37222a4679bce9b9115236dfa6e44548db4dcaf11523601a6e44548d74dc88a918d6
  | 7, 0, 1 => 0xe1a6e44548d8069b911da35017222a462d74dc88a919f6
  | 8, 0, 0 => 0x69b9115235
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 32
  | 4 => 39
  | 5 => 46
  | 6 => 53
  | 7 => 46
  | 8 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfe000038780001ddfc00007700ffffc03ffff00ffe20007fff
  | 0, 1 => 0xff1fffffc7f881f01ffc7fff8800ffffc03ff8000ffde003f877
  | 0, 2 => 0x1ce1e00007708ffe221ffff8ffffe2203fc7ffffc1fe038c787f
  | 0, 3 => 0x3ffff88ffe1e03fc7708ff00003f3ff80e0ffc2383f800
  | 0, 4 => 0xe31e1fc7c07ff1f01ffc0387f700001dc03ff880000000000000
  | 0, 5 => 0x1c00000070000000038c7f7f001ddfc00777800000038c787f
  | 0, 6 => 0x777800001dc000000001dc00007778001c000007778
  | 0, 7 => 0x1c0000070000000e0000038000001ddfc00700000001dc000700
  | 0, 8 => 0xe00000380001fe1ffc7387801ce00007380001c01c00700700
  | 0, 9 => 0x1ce1fdc7387801c01dc07000771ce1e0003877700e1dc0038077
  | 0, 10 => 0xe0000007387801cfdfe073f0001c001c003f77800fdde003f000
  | 0, 11 => 0xe0001df83f800e00000383f800e0e0003807000e000003800000
  | 0, 12 => 0xfc1dc03f00000e0ffde383f877e0fe003838077e0e0003807077
  | 0, 13 => 0xff001dffc0000ff00003fff800ff1e1fffc07ffff00003f3ff80
  | 0, 14 => 0xffe0003ff8000ff1ddfffc7778ff1c003fc0700ff00003fc7778
  | 0, 15 => 0xfffe1dffff800fffe003ff87f7ffe01dfff8000ffe1e03ff8700
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x6e88801a391006eecc0099b3004e88801239100488000019b3
  | 0, 1 => 0x4f117752844080f01774292608006eecc01bbb3006ecc801bbb3
  | 0, 2 => 0x98c9801296608b5a221fce586e9080001bc5dff6c176cd8c586e
  | 0, 3 => 0x4206476b6608dad98236b6608da91023636600dad9823436200
  | 0, 4 => 0x63361b8bc9dff2f0177495bbf725267dc9522442500110809822
  | 0, 5 => 0x4e7d9a031a7910068801ad7f7e4a7ffed2977784a599219cd9ff
  | 0, 6 => 0x6f79931bd777c6f377fdbc444c6c7fecda9ff7a607e88939f7f9
  | 0, 7 => 0x9ca164672040094e8e4643a2006f7fffdbdfe6e6f7fffdbde7dd
  | 0, 8 => 0xb5e8912c3ba229fe9f7673a7919ce9e4673a6009ce9e46732710
  | 0, 9 => 0xbdeffdef7a7d5bdcddd2f69df7bcefecef7bff7b8efdcad7bbf7
  | 0, 10 => 0xf090003ffe7dddefdfe77bf668deb57e77bf7f9dafdde343f220
  | 0, 11 => 0xf5b67dfd3fbb3f4b0647c3fa22f0fe88bc37220f0b608bc2c000
  | 0, 12 => 0xfcddcc3f2ddb3faffdebd7fbf7f5fe99bd7fbf7f5f8f57d7fbf7
  | 0, 13 => 0xffb77fffedc6effb1777ff664cff971bbfe45ddff91133f3ffb3
  | 0, 14 => 0xfff9f77ffe64cfffffffffff7effff9bbffe7ddfff9933ff777c
  | 0, 15 => 0xfffffffffffffffff9bbffffffffffffffffe6efff9f77ffe75c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 128 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 128 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 128 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 128 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 7 0) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 7 0) :: stateWiresS n (ids >>> 7)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 6
  | 3 => 47
  | 4 => 232
  | 5 => 716
  | 6 => 359
  | 7 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0xdb4f1a199b707a8c937b966562dfd0b3107337f208272e64
  | 3, 0 => 0xec7f8168eb49b9bee4cdf5f9c8b66a10b50ccbbea283d1709b41faa79b205c4797fac90a953a82b294737dd8931979da8b3adcd5868aed9e84d79cb27f6fd3127c0f7cd6783ae99b775f8d9f756e03fe732fcd116bbb60d25efb1c5d5dfbc4ed595bbf5a5052a6d44e0b96564984653444f8fd253d6030492f1da5d32dc692222c134b2e2c0942a02b03b191290bf9782717a6571fb0f7391e10bfcc1ceb04ad1c4b122217128fbe1661b287129dfc9e1027fefa0ea22c6700f8ea04
  | 4, 0 => 0x349ba87a32d10ef3329a5c2b328471e3326dc2623234260c312ceb8d2f616adf2ddc54a72d40d1b02ac72ba62a404c4a290acf4c289a931c26c71f32264971412475cb9322b3a764229d4e5b215cd5622093b6fa200c83931fc6b21f1fb85afe1f2756cf1ddcb55b1dbf89ed1d2b8cec1cf5b56f1ceb04ad1bf668ca1b993fe718a9475f14ee45e8147ef64e13b5b0c313884b3d13645f70135578761344971713430b0912a4bb54126527ab124e3117106c3e930f7c064f0f3c35d30f1fce070f0243db0e6a90200dd409410cb481310afba44c074f0a8305add39b051c158f04a848aa03d488a803b0c7d7038f4631028b4675026382fb013734fb003d48b3
  | 4, 1 => 0x65c2292f63cbc54162b26fb9605169955e954e575e5d16745db14b255b0c81a65af562755ae04c275a6845d7599450a957c6642f5651e8fc54a4b847545d95db53c3e79053632838525279e051ba59d4517ea7ec4fada6a44eb6fb934d8d076a4d7ce16d4c9b5c4b4c626c544c4b01eb4b83fd114b7caade4b56af504b0322b64a29f913499101a647a6ae2c4655ef2545c6b429455bcff6452dadd5451e2ffb44049cc74399bc0d437c6f814269e602419b2c574156667a3ef7e25f3ebdc1103e7df9993e73e4c63db9f6cb3daffb993d340f1a3cc6b8323cbe72753be81beb3ae03acf39220cde390b565c382227c037d25b6e37382cb436fd7a3d35750a43
  | 4, 2 => 0xab9efcdcab484146a9b1d4a7a9a174a7a9556c5aa7435342a580d91fa4a57d23a1f11837a190c118a153439fa0273ed09eb95ac29d8040789cd086d29a1ee2e399eb2b3d98c851bd95a1d16a93ff2a328de06b708d482a228cad58428b91956b8b90fb538a5012a08779b241868aed9e863838c785fa7d2c856596318557b20481ea538081b2e52081164cda7fcb623e7f8837707d92ead678a22ccc786fd070778d8d2a77529e9576ca54b876a5304e76389c37762be2bc7595a97174acede274a501dc742486ef723eeca9721ef89472020f587195b3096f9ed7516ecce0876dc90c816d2fe2996c14a2ec6c06da2069286bb969077dda6775cb7a6685049e
  | 4, 3 => 0xff820722ff807faafe6a472bfce18f29fc097c5ef9c5145af999ffc7f8a5b4fdf1cf896beec00fe1e88aeac5e6e08a88e252bb42e192be46e0b5176dd54d9339d3f11db1d1eb189ed0b37e53cc5428f9cbafba69cacab937c7c50ee0c6f90ceec6698d2bbeec05e7bed6187abe2102c2bc818238bc1635b4bc077520bbb13f47b98090b0b8996acab880cc59b641b725b308b268b2fe05b1b281e36bb160be37
  | 5, 0 => 0x11ec163711dd3ed211d702f011b3f48d11913a7410f85c07109dce4c0ff3f4890fbbf6a10fb4012b0f63dd930f1fce070ef7e3300ed8adca0ed6e3680dfb06f10dda1e500da784ce0d58ac670ce589fa0c91eeb00c3fc7a00c1c85590bf4795b0be990840b704ed00b370f270b34fa1e0b26d9e40b22ae770b0607b30aae55c10a9803d30a95cb830a51b2b909eb9cad094e0773094190f8083a533808248e21081a15ff07e8b2a407e6cd7f07e08729074b012c06f7a1970645e4250548be7804fbbd8d0494f17f047aa46403abdb8402ff958002f32e9902b206c70282f269026f10e001bb35de00f16dea00ce926c00a59ee700755bc90068da6800089faa
  | 5, 1 => 0x1cc7848d1c12e0cc1c05ff651bfa53aa1bef02521baca41c1b9bfdae1b2929df1b139dc81af35d971af20ba71a8516cf1a44e9fd1a2886eb19f97c8419cf3c9519cb622219818360194d2aef1933651b191e585418d6438a18d2304518bcf94418a9e6db18a9475f18a8188d184174e0183c1ca8182ceb3f17d0aa5f1784c3401782a15e173fac4e167434d7165fab271649cdbb1634af3a160696281600589415ea5ccb15ded6ee15d81e4815d1737615d0da4915a5cd9015273ce215204693150c08e214800daa147cd8a2142f5e7313c271cc13bcb2111389a64613645f7013128aaa129ff6c4127ff820125878621249c76312349f59122558021209bd7c
  | 5, 2 => 0x2be549902b9c38162b19b2412ad29b592acab2b22ac939b02abbcbb82a6c2f9f2a4daf132a41cd7c2a277ead2a178af4297010be290acf4c28fd3b4928c30e5e289a931c287926cb28086d602806e15227c1ec9027928613278ebc78272249e3270b03de2690342b26757788263e3b7d25a666be25a509332567a335252435ca2512ddb624e6a591248024f82472ae4d245cf5a923aea0852366326d2315f32c22f003952225ff2221cb970c215cd562212e4a5620d699ff2044c631203288352017fd131fa49fc11f8041b51f5c34cf1efeb8c61eb7a1de1e5e7fc81e3d20651e35565d1de6e42c1ddcb55b1db9534e1da53b691ce122ff1cd2a8681cc8bad6
  | 5, 3 => 0x3f1a46533ea626ee3de953c23dbc91c73d9dc1363d24fcf53c482b803b6e8d2c3b2ff8f63b19f8c53af457613ac2181b3a736be73a2a25ec3962b1b7393608c1392a59d439224a6f3916f65f391565853914b09938fbe1c438e30f00381dbe0c3778b05d37382cb4372650b93633d32a35d3301c357f57553514d9db34b2c9f83433bc9133fb61d333ee9a8633937de63359f38d3330dda633136549320c3b35319f45d5314fbf3731298a2230cfcba630b04f8a2fef2b282feb59d92fb0c16a2fa98d622f7b1da92f7abb902f3d01952e631dce2e1b67d12e1b47802e0678a42e029e322dc057022db92d382d4f60b52d2d78882d016c202ce0e8492c21c663
  | 5, 4 => 0x51a1f9c5517ea7ec512f621c5102d2cf50d791b550d47de6503a0635501cf63e5019bfb04fd51de24fada6a44fab88f84fa10d254f1735644f0a70104e9e7ff64e207f504d7877b94ca73eb64b9204294b757d384b5a61c14b22a4df4b0fa96b4b0322b64a5236f04a3628d04a30f4314a1f5be34a0593be499101a649271b7e48adeb7d4812e6be47cf95ce473d183247016eaa46daab2046ce4d5d469eff26457d6c27456577b645534e7d44b5b3f74458a95b43d8c273439556754381664643767a444315ba4b4304606842e7b68d4279b1824272eb534234356c41f60d7f418d14994187382640f6052340c3311b406a81c3406683733fab172f3f4f9110
  | 5, 5 => 0x640c8045633fb3d262ef3db36266d80e620ec18b6202ec7b61dd21f460f97cc3600de4a660027a735f83eb5a5f172b8f5f0c569b5e8896445e1cc52c5de298b85dc622ca5db1ea005da87aca5d6efb9c5d45a6f55d33b67b5d18e3ac5c30efa35ba073fa5b7376875b61388b5b19c56e5ab882425a4fdb2e5a05ce895a050718598d301e5972e34559156e53590b65b158b8a80f5894339158232ed658166dbd581079fb5810475858081cb55788170a566309645620bbfd5616c6f655fba60955f635c855824086554fa704552f3f0755204a0d540dd7f2540d0eb65400e09b53ef433553d6c8e352a3c682525fae7c52466e1551bd092251b5473b51a2e52d
  | 5, 6 => 0x754c39d074dbfda0747e6e2f7445a6b574317c7173e0c0257358786872d8abbd72c1be8072b1489872064f1070f69b8870effa0d70ec489670ae07ab708ccfbe6fd98a676fb6120c6fac3e656fa9a6b36ee798d96eae41b06d8e893f6d69a25d6d6038c26cb32d436c7e6f8d6c07cd466bc3e91d6bbd71646b7180a36b50c6b06b3e4af76ad259566a1cf8c869d9514b69c398f96991ce24694a70ed6949f7d6691ba2ae691160cd69084d076897ab3e688714a4688315b7686e9bda685c28de685a45d268262a536816ba736803ced2676378fe6757dcd56713f9e666f33cce664dfca066427e3566014baf65febd8665fd0af665ab0b6b64f919d664a568be
  | 5, 7 => 0x8c5e12728c507ea18c3622118c1674de8c06420b8bdb3ddb8bacf19989df40a58959b60f88efd49188ee25b888d42c788888432e887dec96872cd7c3872103d986f4929986ad7bb18685d775850c53b3841f5ddb8397c31d838657878364a8328334f91b82d7257f82c4bceb81ecc90a81e960ef811a189a80cd741e80ac79e080a1625e80959a3480917a67804bb4117fed28667f99c54c7f7fc1277f428b2d7ed58e197ea52a9a7e99b8297e7590907e61b46b7ce1a1257cd822f77c5db9cc7bf88df67bf68f677ac38a2479fa5c0c79e14bcf79b44b4e795f15d4795075c278d4955b787ea386787c5af678517490782d0233770358c576ca54b876aa0ec5
  | 5, 8 => 0xa4cd00e3a451f089a3eb1fd2a37e8bbba377fd65a2622cd9a1f11837a1e8eb25a1c0b4b8a1b9829fa1712e8ba14f52f5a13b3f42a12a17a3a0273ed09ff0ddf89f3b309b9f1581fc9e7236929e55ed0d9d9588649c3ba6049c02f90e9b8265029b72fe499b3ccaa89ae2d4e69a1ee2e399f9c44e9967b37098d0888c98c851bd985bf669985746d8981fefaf9763b6539759feba96e885c1964f15bd964d6d5e95fc1c0b957b40f79572c41194a42802948bc72d937a48ae9360205692f51485923e7dfe92081ead91ae53c8917d30599162568390a2a3db903936ee9011e7358f58912c8f4940f58e7be31a8e30a7fa8e09fd168d42dc528cad58428c682342
  | 5, 9 => 0xc43e6fa8c3105b70c304f894bf37ce6ebe935888be05d5d5bd99f6a1bc1635b4bb87dd3bbb3b79cdbb326c93bb1518e8baf7c76fba9e98a7b9740234b924fb97b8fdd063b8ed2823b748cba0b5ec5618b5c3e4b7b5917c08b54c10bcb4f27f76b47f2618b3d0dd22b3b94fecb397ef77b35bb289b2b7792ab232091bb1f05c1db160be37b0b38794b0b16c77afb63436af757176af726a77ae76c657adc84a71ad7cb563ac3d6871ac2f5188ac1eaa63ac1af8ecab33832caaec8cd7aaebea9eaa310abaa9fc4b5ca96bb9c6a94875d8a91bc92ca90c637ea7f6cf31a7bc4376a79da85da71ccf31a7188f03a654a5c0a64913b7a622987fa5b5bff4a591a80e
  | 5, 10 => 0xee0168b4eca1a47cec00a0f1ebdc5388eb8769d0eb15af4deb1109bbeaac0dd4e88aeac5e5fa4430e5c4917ce505bdfae2273fdae1b272a9e1796761e117aaf5e0ff3f70e02f7d43dfc7d2efdf51759ddf264082de9f3bb1dd9eaa85dd6f11d1dd179b7bdced5d87dc53f108dbeddbafdaa229f3d92fa932d8679adad80e0994d7e3da54d7d61f4ad7d0fdc5d729c80cd720fb6fd5e0e074d54d9339d4c9adb2d3f11db1d1d9f73bd1656b6cd070937fd00e9992cfb5e9b3cfab044dcd9f0f39cd7275c0cc1e349dcbfec521cb42d8a1cadfa0ccc94afdcfc93e5f53c88d9d8ac7be5b41c764d267c6fe0e4cc6ac068dc68c8588c59ae530c4d50cbdc4858690
  | 5, 11 => 0xfe80830ffa667ec4fa51689ff92ca2caf861eb3ef5b6e4fff50cfeb5f4b9c40ef43efc72f1d2bbcaf195ef9bf18d7981
  | 6, 0 => 0x1efef9231efeb8c61eaf72f61e89c4571e685c0e1ce122ff1c783ebd1b171b191ab77be01a928cca1a6aef1219cb62221993156418d230451782a15e177294ae171c8c0516dc176c1694a22e1600589415d81e4815d0da4914880f5b147936bc1376f25912990d631266a7c7125878621249c763114f698c1140d19a110eb0061083627e10740d900ff50bcb0f6491320f5336310f1fce070ebf56e50ea94fe70da784ce0d9a31980c7a0eb50b1fc84f0a51b2b9097d87dd093ca32d08a22be1085ae9b3072d7577069707390634dbb605c84fe905549da10506640d04b6dde0046fc6f8045fd300042bcb960343c6b7023c23f3020442c90128e6cd00d7f0ac
  | 6, 1 => 0x3f7d1f2f3f2d04c03eda8bda3e018dc13d9dc1363ce2a0a53c38e89e3c2577fd3b8868853b7aafd53a9abf4339d7aea738fbe1c4380b534837bc75873730bdd8372650b936cfb5b534e7896734975158342c36c0337b782733758f6b3343139532cfb64d31dae103318b5ad6314443ee3042d04d2fef2b282fa99c6d2f733ea92f7320112eb666fe2dfaf5702deb8e6b2d40a9f42c9d50862c582d4b2ba72d132b7112532a660f8c29e6d08e289a931c284d7c8f280665a727f29a1c279758232728e63c2672924e2616485625967e972557ae1125185d652514d4b5250827e424e2eef424c32b1622e10f1c22d4e77422d0f3ab2261f78e21c0242c1f57e922
  | 6, 2 => 0x5b670a3a5b46ad695acd6bb55ab753705aaef20b5a62453259f3271d598d301e5986e0e15915948259105f54583a84f9580158be56475d635640df1c55c13d20548b1a8d5460b5c35448f3e75400e09b53d6c8e353b54c97535b9b955292e42851aa8be751a2e52d5196082551635f90512f621c50d47de650d0bd0f506b5b5b4fdf8ab04f7d8c634e79a7f44d7f89b34d7877b94d6cb90a4cb623674c4ddca94b45303d4a69d4414a0593be49de7f144976a041478ff849473f6c08469eff2646196c6345fc993a4559dff0452dadd545197eaa4449c6e043c8267043ad475343533e77433257234279b1824256fb274214f79241a4be92415770964036f807
  | 6, 3 => 0x914e96758cb7df488c5e12728888432e86a1e898865b5dd7855636dc8397c31d835cb67a8206fbad813532b97ea52a9a7e0d02217d86a6037d7ff5b97cab64697c6fd11b794607e978ec812178e9822377100796770b4cce758f448f751fea457445a6b572520b3071f40ace7162838070d16f3170ae07ab702a82636fe47b586fa0d83b6f4f26676e594ad96e41b5e36dac72f76c7e6f8d6c754a6f6be20bfe6b7180a36b3e4af769e2331369c7f863698e1b046949f7d6689cb753685c28de67ae8f756713f9e666f33cce66427e3566014baf6594bfe26563ad90640b49fc6244026561dff08a60a063015e9639f35e6e33215e2d4e6a5ca1c7ad5bdd801c
  | 6, 4 => 0xcd6d2e54cb8cad4fcaba9890cab6bc24c93e5f53c9309a55c83666acc764d267c751a598c5d66057c59baa72c54699b3c4c04e76c304f894c3023110c298c5a9c1011079bfbee9b1bee38db5bec67373be935888bae715ceb95c6462b7b2eb27b7253029b6cb792cb5290c62b4d91bdab47f2618b3862481b35bb289b2d89b0ab29e5067b232091bb1d62a66afeb66efaf726a77af100af3ae51fd58ac1eaa63ac1af8ecab087d87aafea7b5a9d70da4a9ca2a55a9bd72b6a7188f03a67f7706a4494849a3ed6994a202a7a4a1712e8ba12a17a39fedccf99f39fa529c4c29679a88cb9399b7469a999751ed9937bf139690607195fc1c0b9419e6d2915d4001
  | 6, 5 => 0xff6d1ffefbe36f05fa667ec4f9642421f8d81426f888c825f835a693f79f097ef5d38d0ef16bb5a5edb2990feca1a47ceb7b64d6e8afc50ee86223d1e8129da4e7cb86bce60b2a37e57138b5e505bdfae2d3044de0ff3f70e0ef09ffdfc9d83ddf82c155dea6adbbde9f3bb1de29fa58de257fa4dd92a404dd179b7bdaf6dd36d89f7cf6d86c0d65d7f49cded5f42528d51a1c75d2ff818bd02990d9
  | 7, 0 => 0x9f39fa526b7180a36594bfe255c13d20
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x841010008410130441203000481010004810100048101
  | 3, 0 => 0x410c120000084101204412030008410100041103304412030008410120441203304412033044120400048101314c12020000000130441203000841013044120400048101000841010000000200048101000841012044120330441204000841010008410100000001240412050004810134480200000841012044120334041205
  | 3, 1 => 0x8410100084101000841010000000130441203240412053044120400048101314c1202324c1202000481010008410100084101204c1203
  | 4, 0 => 0x1000c110200041103000c11030004110542041200000c1104000841010000000100048101000000010000000200041104324c1202000c110200000000000481010008410100084101000c1100200812000000000600000006000c51024108120000048101324c8200000000050004810100000005410c120000000007
  | 4, 1 => 0x200000006000000000000000500000005000c01000000000500084101304c0200000000000000000000041103144802000000000000000000000000012404120500080100104402000000000400081103410812000000000000084101344802000000000000048101324c82000008410100048101244c020000084101
  | 4, 2 => 0x4810100000001410c1200000c1103144c020000000006000000001044020000000000420c1200000000000004810100000007000000070008410100000006204412040000000000048101304412033044120400000003304c02000008110300041105000c110300000000000c110200000007000000030000000000000000
  | 4, 3 => 0x4110500000001000841010008410130441203000411040000000100048101000000000000000200084101000411030000000100084101000000030008110300084101420c1200240412050000000700000001214842000000000500000006000000023044120400041103000c5102000c9102000481010008410100000000
  | 4, 4 => 0x1000c1103000811030000000300084101000411040008410100048101304c020000000001000000010008410142041200344402000004110534081200320c920000000001000c11030004110500000002000000060000000610440200000000000000000100000002000c110221484200314c120200041103324c8200
  | 4, 5 => 0x6144802003448020000000007000841010000000200081103000841010000000200000003000000060000000100000006000411030000000600000001000c11040008010042041200304412030004d1020004110534440200000c110321484200000c1104000c51020008410100084101000000060000000700000001
  | 4, 6 => 0x4000000010000000100000000000000010004110500041103304c02000000000021484200000c1100000411050000000600000007000c110220441203000841014204120000000006324c8200344402000000000200000001304412043044120300000006000841013448020000000007000411042148420000000001
  | 4, 7 => 0x8410121484200000000010000000000041103000c11000000000500000001
  | 5, 0 => 0x1000c91000000000200000001000000010000210000000003000000020000000200002100000000040000000500041104324c82000000000400000000000000040000e10000000001000411040000000300081104000000070000000000000002000c9102000000060000000200041105000000020004110000000003
  | 5, 1 => 0x7000000010000000500000001000000020000000000048100000000000000a10000006100000000020000000000000002000000050000000100000003000000060000a1000000000600000001000000020000000100000002000000010000000500041105314c42000000000000048101000000060008110400041100
  | 5, 2 => 0x10000000000000007000000030000000000000001000c81000004110500000005000000010000210000000001000411030000000600000003000000040000000100041105000000050000000700000001000c1103000000030000000200000003000000050000000300000001000000020000000100000003
  | 5, 3 => 0x34440200000000060000000100000005304c020000000005000000050000e100000000000000000700000002144c0200000000070004110300006100000000040000000300000002000000060000000400000001000c11030000000200000004000000040000000100041105000841000000000000000000304c0200000c1103
  | 5, 4 => 0x5000000010000000500000003000000000004010000000003000000010000000300081100000c11020000000400000005000000020000000200000001000c510200000002000000020000000100000001000000010000000200000006000000060000000100000000420c120000000002000000030004110500084101
  | 5, 5 => 0x411040000000300000001000000010000000300000000000c1104000000040000000100000002000000000004110000000003000000010000000300000002000000000000000100084101000000010000000500081104000000010000a100000c110000000003000000010000000300041104000000050000000100000001
  | 5, 6 => 0x300000002000000030000000200000004104402000000000400000002304c020000041104000000050000000200000004000c5100000000070000000200000002000c810000000001000801000000000100000003000411030004110400000005000000040000000300000003000411040000000500000001000c1104
  | 5, 7 => 0x1000c110200000004000000020000a10000000003000c11000000000400000005000841010000000600000002000000010000000100006100000c11030000000400006100000000010000e1000000000500000001000021000000000100000004000000030008110000041105000000040000000200000004000c1103
  | 5, 8 => 0x10000000100084101000481010000000100000002000c010000000005000000050000000400000001000000030004110500000003000000060000000400041105000000061044020000000004000000043448020000000005000000000000000400000005000000010000000700000001000c11000000000110440200
  | 5, 9 => 0x40000000100000001000000050000000000000003000c110000000005000841011044020000000003000000050000e100000000000000000000000003000000020000210000000005000000060000000000000005000000000004110300000000324c8200000000040004810100000001000000010000000100000002
  | 5, 10 => 0xc9100000000010000a1000000000000000001000000013448020000000001214842000004110500000005000411050000000300000002000c1100000c110442041200000000060000000400000002000000070000000300000000000c1100000c910000000005000000040000000434480200000481010000000100000000
  | 5, 11 => 0x84101324c820000000000000000010000000200000003000000010000000200000004324c8200000000033448020000000005000000000000000600000006000000040000000100000004000000030000000500080100000c11000000e1000000610000000002000021000000000300000004000000004204120000000000
  | 5, 12 => 0x1000000020000000142041200000801000000000100041105000851000000000400000004000000040000000700000006000801000008410000000004000000040000000500000002000411030000000100000001000000030000210000000006000000010008010000041103000c5100000000050000000300000004
  | 5, 13 => 0x10000210000000001000000010000000300000001000c910000000006000411040004110500000003000c11000004110300041104000c4100000000010000000142041200144802000000a100000000060000000200000003000000060000000100000003000000040000000200081104000000050000000000041103
  | 5, 14 => 0xc110200000000000000060000000100000003000c1100144802000000e100000000020000e10000000001000000010000000100000004000000020000000400000000000411030004110400000000000c1104000000060000000200041103000c81000000a100000000000000000400041105000000010000000142041200
  | 5, 15 => 0xc010014480200000000010000000100000000000c110300000001000c11000000000100000007000000020000000300000000000c51000000000600000003000c8100000000010000000700000001000000010000000200002100000411050000000300000002000851000000000700084100000000040000000100000001
  | 5, 16 => 0x6000000020000e10000000006000000010000000021484200000c11030000000000000007000000000000000100000001000000020000000200000001000000010000000100006100000000070000000300048101000000040000000500000001000c4100000c110000000001000000030000000700000001144c0200
  | 5, 17 => 0x100084100000841014204120000000001000c510200000002000000020000e100000000050004010000041103000000020000000000000001000000030008410100000003000000030000000000000001144c020000000003000000050004110300000003000000030000000120480200000000030000000300000001
  | 5, 18 => 0x1000000010000a1000000000100000006000000010000000500000002000c1103000000060000000500000003000000040000000500000001000000020000210000000001000c1102000c110000000002144c0200000000040000000300000002304c0200000000010000000400000001214842000004810100081104
  | 5, 19 => 0x1000000030000000100000001000000030000000224440200000000020000a1000000e10000000006000000010000a10000000002000000051448020000000001000000060000000500041104000000010000000600000005000000050000000300084101000000010004810100000005000c11040000000100000003
  | 5, 20 => 0x200000001000000010004110400000001144c02000000000100002100000000000000000700000001000c81000000000300002100000c1102000000020000000100085100000000020008410000000003000c110000000001000000000004110500000001000c110000000001000c9102000000010000000500000001
  | 5, 21 => 0x2000000010008510000000000000000050008410000000001000000010000000200000000000c1102000411030000e1003444020000000001000000072148420000000001000000000000000100002100000000070008410000000004000000000004110400000001000000050000000500000005
  | 5, 22 => 0x100041103000411050000000121484200000000030000000100081103000411050000000000000002
  | 6, 0 => 0x100000003000000050000000000085100000000000000e100000000030000000400006100000801000004110000000002000000040000e100000000070000000000000005000000010000000100080100000000010000e100000401000000000000081100000411000008110000000005000000030000000300000000
  | 6, 1 => 0x50000000100000001000000010000000100000003000c010000000004000000030000000000006100000000030000000300000002000000000000000400000004000000050000000400000005000000010000000100000004000000010000610000080100000000000000000400000001000000030000000400000002
  | 6, 2 => 0x200000003000000040000000500000001000000010000e100000000000000000300000000000000020000000000000003000000000000000300000003000000040000000500000000000000010000000500000001000000000000000600000004000000010000000500000004000c4100000000040000000500000001
  | 6, 3 => 0x400000003000000020000a1000000000100000004000000040000000000000003000000020000000100000002000c9100000000010000000200000005000000000000000200002100000000010000000200000000000000040000e100000401000000000000000000000000030000000000000004
  | 6, 4 => 0x300000004000000040000000500000001000c91000000a100000000000000000400000004000000010000000200000003000c9100000061000000000500000004000000050000000000000000000000010000000000000002000000010000000200000004000000040000000400002100000000010000000000000004
  | 6, 5 => 0x4000000030000000200000005000000020000000200000005000000020000a10000000001000000010000a1000000000500000003000000040000000000000005000c91000000a100000000020000000500000006000000000000a1000000000200000000000000010000000000000001000000030000000200000004
  | 6, 6 => 0xa100000000070000000500000000000c110000000004000c81000000000000000000000000040000000300000004000c110000000003000000050000000400000000000000040000000100000001000000020000000000000001000000000000000500000000000000050000000000000000000c0100000c810000000001
  | 6, 7 => 0x4000000010000000100000000000000050000a1000000000500000002000c110000000004000c9100000000050000000500000002000c11000000000100000003000c810000000004000000010000000000000003000c81000000000000000004000c8100000000000000000500084100000000020000000400000000
  | 6, 8 => 0x10000000500002100000851000000000100084100000000020000000300000004000c510000000003000000020000210000000005000000050000000300000001000021000000210000000001000000000000000600000000000000040000000000000000000000050000000200000005000000000000210000000000
  | 6, 9 => 0x1000000030008110000000001000000010000000200000006000000010000000200000005000851000000e100000841000000000100000001000000030000000400085100000841000000000200000005000811000000000100002100000c110000000003000000000000000300000003000000030000000500000005
  | 6, 10 => 0x1000000010000000000002100000c01000000e1000004010000000000000000020000000100000000000c0100000000010000000000000001000000010000000100000001000000000000000000002100000000020000e100000000010000000200000003000000050000e100000c010000000004
  | 6, 11 => 0x200000005000000010008510000000001000841000000e100
  | 7, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 6 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 3 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 4 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 5 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 6 => checkCutEntry dom_8 roots_8 4 s ws hint
  | 7 => checkCutEntry dom_9 roots_9 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_10 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_10 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_10 == dom_10) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_10 goalM u ys) : RunD dom_10 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_10 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_8 : ∀ i, 8 ≤ i → i < 16 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_16 : ∀ i, 16 ≤ i → i < 20 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 4 16 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 20 → Z 3 i = true := range_split z3_0 (range_split z3_8 (z3_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_16 : ∀ i, 16 ≤ i → i < 24 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_24 : ∀ i, 24 ≤ i → i < 32 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_32 : ∀ i, 32 ≤ i → i < 40 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_40 : ∀ i, 40 ≤ i → i < 48 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_48 : ∀ i, 48 ≤ i → i < 56 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_56 : ∀ i, 56 ≤ i → i < 64 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_64 : ∀ i, 64 ≤ i → i < 72 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_72 : ∀ i, 72 ≤ i → i < 77 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 72 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 77 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (z4_72)))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_16 : ∀ i, 16 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_24 : ∀ i, 24 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_32 : ∀ i, 32 ≤ i → i < 40 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_40 : ∀ i, 40 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_48 : ∀ i, 48 ≤ i → i < 56 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_56 : ∀ i, 56 ≤ i → i < 64 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_64 : ∀ i, 64 ≤ i → i < 72 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_72 : ∀ i, 72 ≤ i → i < 80 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_80 : ∀ i, 80 ≤ i → i < 88 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_88 : ∀ i, 88 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_96 : ∀ i, 96 ≤ i → i < 104 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_104 : ∀ i, 104 ≤ i → i < 112 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_112 : ∀ i, 112 ≤ i → i < 120 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_120 : ∀ i, 120 ≤ i → i < 128 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_128 : ∀ i, 128 ≤ i → i < 136 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_136 : ∀ i, 136 ≤ i → i < 144 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_144 : ∀ i, 144 ≤ i → i < 152 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_152 : ∀ i, 152 ≤ i → i < 160 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_160 : ∀ i, 160 ≤ i → i < 168 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_168 : ∀ i, 168 ≤ i → i < 176 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_176 : ∀ i, 176 ≤ i → i < 184 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_184 : ∀ i, 184 ≤ i → i < 192 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_192 : ∀ i, 192 ≤ i → i < 200 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_200 : ∀ i, 200 ≤ i → i < 208 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_208 : ∀ i, 208 ≤ i → i < 216 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_216 : ∀ i, 216 ≤ i → i < 224 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_224 : ∀ i, 224 ≤ i → i < 232 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_232 : ∀ i, 232 ≤ i → i < 235 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 232 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 235 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (z5_232)))))))))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_8 : ∀ i, 8 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_16 : ∀ i, 16 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_24 : ∀ i, 24 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_32 : ∀ i, 32 ≤ i → i < 40 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_40 : ∀ i, 40 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_48 : ∀ i, 48 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_56 : ∀ i, 56 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_64 : ∀ i, 64 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_72 : ∀ i, 72 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_80 : ∀ i, 80 ≤ i → i < 88 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_88 : ∀ i, 88 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_96 : ∀ i, 96 ≤ i → i < 104 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_104 : ∀ i, 104 ≤ i → i < 112 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_112 : ∀ i, 112 ≤ i → i < 120 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_120 : ∀ i, 120 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_128 : ∀ i, 128 ≤ i → i < 136 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_136 : ∀ i, 136 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_144 : ∀ i, 144 ≤ i → i < 152 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_152 : ∀ i, 152 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_160 : ∀ i, 160 ≤ i → i < 168 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_168 : ∀ i, 168 ≤ i → i < 176 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_176 : ∀ i, 176 ≤ i → i < 177 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 176 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 177 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (z6_176))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_16 : ∀ i, 16 ≤ i → i < 20 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 16 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 20 → Z 7 i = true := range_split z7_0 (range_split z7_8 (z7_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_10 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_10 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_10 roots_10 goal_10 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_10 goal_10 := by
    have h0 : isConstB dom_10 goal_10 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_10

theorem low_10 : Lower dom_10 roots_10 goal_10 9 := S_10.noCircuit

def dom_11 : Nat := 0xffffffffffffffff
def goal_11 : Nat := 0xfeeefeeefeeeeaa0
def roots_11 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff0000ffff0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_10

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_11_bits : ∀ r : Fin 64, roots_11.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_11_lt : ∀ r : Fin 64, dom_11.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_11 T)
    (hlow : Lower dom_11 roots_11 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_11, Avail mask256 roots_11 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_11 hfan 0 roots_11 roots_11 rfl hsup0
  set out := (execN C.gates roots_11).getD C.output 0
  have hout : out &&& dom_11 = T &&& dom_11 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_11_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_11 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_11_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_11).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_11)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_11.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_11 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_11).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_11 &&& mask256 = dom_11 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_11 = T &&& dom_11 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_11, hd63, hout]
  have hnc_m : ¬ IsConst dom_11 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_11 roots_11 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_11, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_11 roots_11 0 roots_11 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277070496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_11.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_11 10 hT6 (by unfold IsConst; decide) low_11

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [9, 8]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [12, 5]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_12925_aux

theorem PEqualNP.Outside.L_meta_12925 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277070496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277070496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_12925_aux.wit, PEqualNP.Outside.L_meta_12925_aux.wmono, le_trans PEqualNP.Outside.L_meta_12925_aux.wsize (PEqualNP.Outside.L_meta_12925_aux.lower s hs), PEqualNP.Outside.L_meta_12925_aux.weval⟩
