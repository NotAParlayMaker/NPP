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

namespace PEqualNP.Outside.L_meta_12126_aux

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
  let x := (((w &&& 4294967295) ^^^ seed) * 2654435761 +
            (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519 +
            (((w >>> 64) &&& 4294967295) ^^^ seed) * 3266489917 +
            (((w >>> 96) &&& 4294967295) ^^^ seed) * 668265263 +
            (((w >>> 128) &&& 4294967295) ^^^ seed) * 374761393 +
            (((w >>> 160) &&& 4294967295) ^^^ seed) * 1274126177 +
            (((w >>> 192) &&& 4294967295) ^^^ seed) * 2869860233 +
            (((w >>> 224) &&& 4294967295) ^^^ seed) * 1640531527) &&& 4294967295
  let y := ((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295
  ((y ^^^ (y >>> 13)) * 3266489917) &&& 4294967295

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

def dom_0 : Nat := 0x808080808080808
def goal_0 : Nat := 0x808080008000000
def roots_0 : List Nat := [0x800080008000800, 0x808000008080000, 0x808080800000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(11, 27), (11, 43), (19, 27), (19, 51), (35, 43), (35, 51)]
def r1sG : List Nat := [11, 11, 19, 19, 35, 35]
def r2sG : List Nat := [27, 43, 27, 51, 43, 51]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x9edf8e44
  | 3, 0 => 0x9edf8e44
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x80808080000000008080000080800000800080008000800
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_0 == dom_0) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_0 goalM u ys) : RunD dom_0 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_0 roots_0 goal_0 4 := by
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

theorem low_0 : Lower dom_0 roots_0 goal_0 4 := S_0.noCircuit

def dom_1 : Nat := 0x88008800880088
def goal_1 : Nat := 0x88008000800000
def roots_1 : List Nat := [0x80008000800080, 0x88000000880000, 0x88008800000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x888800008888
def goal_2 : Nat := 0x888000008000
def roots_2 : List Nat := [0x808000008080, 0x880000008800, 0x888800000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 4 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0x88888888
def goal_3 : Nat := 0x88808000
def roots_3 : List Nat := [0x80808080, 0x88008800, 0x88880000]

theorem low_3 : Lower dom_3 roots_3 goal_3 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0x8888888888888888
def goal_4 : Nat := 0x8888888088808000
def roots_4 : List Nat := [0x8080808080808080, 0x8800880088008800, 0x8888000088880000, 0x8888888800000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(7, 15), (7, 23), (7, 39), (11, 15), (11, 27), (11, 43), (19, 23), (19, 27), (19, 51), (35, 39), (35, 43), (35, 51)]
def r1sG : List Nat := [7, 7, 7, 11, 11, 11, 19, 19, 19, 35, 35, 35]
def r2sG : List Nat := [15, 23, 39, 15, 27, 43, 23, 27, 51, 39, 43, 51]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x49e848b4
  | 4, 0 => 0xb1ad94414478560527fdf67522913f3f
  | 5, 0 => 0x6f944dcc44faf3cb043b5eaa
  | 6, 0 => 0x44faf3cb
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x88888800888888008888000088880000888088808880888088008800880088008080808080808080080808080808080800880088008800880000000000880088
  | 0, 1 => 0x8888888888888800888888888800880088888888808080808888888800000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa9654
  | 4, 0, 0 => 0x86214864305b86435876535
  | 5, 0, 0 => 0x86424086434876435
  | 6, 0, 0 => 0x86434
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1f81c003f038007ff8fc71c7
  | 0, 1 => 0xff8e38e07e00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xdfb9d26ff4b924fdb0b46042
  | 0, 1 => 0xffffbdf6ff24
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 8
  | 5 => 2
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x77f844e
  | 3, 0 => 0x44faf3cb37a387b00c12b46b0794e57e
  | 4, 0 => 0x6f944dcc44faf3cb0d398f5507868aad05978a3504c60dfd043b5eaa0414e490
  | 5, 0 => 0xd398f5507868aad
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x1
  | 3, 0 => 0x3
  | 4, 0 => 0x4000000000080000100000400000
  | 5, 0 => 0x400000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 1 => checkCutEntry dom_1 roots_1 4 s ws hint
  | 2 => checkCutEntry dom_2 roots_2 4 s ws hint
  | 3 => checkCutEntry dom_3 roots_3 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_4 == dom_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_4 goalM u ys) : RunD dom_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_4 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_4 roots_4 goal_4 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_4 goal_4 := by
    have h0 : isConstB dom_4 goal_4 = false := by decide +kernel
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

end S_4

theorem low_4 : Lower dom_4 roots_4 goal_4 7 := S_4.noCircuit

def dom_5 : Nat := 0xa0a0a0a0a0a0a0a0
def goal_5 : Nat := 0xa0a0a080a0808000
def roots_5 : List Nat := [0x8080808080808080, 0xa000a000a000a000, 0xa0a00000a0a00000, 0xa0a0a0a000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 7 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xa000a000a000a0
def goal_6 : Nat := 0xa0008000800000
def roots_6 : List Nat := [0x80008000800080, 0xa0000000a00000, 0xa000a000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_7 : Nat := 0xaa000000aa0000
def goal_7 : Nat := 0xa8000000800000
def roots_7 : List Nat := [0x88000000880000, 0xa0000000a00000, 0xaa000000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0xaa00aa00000000
def goal_8 : Nat := 0xa8008000000000
def roots_8 : List Nat := [0x88008800000000, 0xa000a000000000, 0xaa000000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0xaa00aa00aa00aa
def goal_9 : Nat := 0xa8008000800000
def roots_9 : List Nat := [0x88008800880088, 0xa000a000a000a0, 0xaa000000aa0000, 0xaa00aa00000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(7, 23), (7, 39), (19, 23), (19, 51), (21, 23), (21, 53), (35, 39), (35, 51), (37, 39), (37, 53), (49, 51), (49, 53)]
def r1sG : List Nat := [7, 7, 19, 19, 21, 21, 35, 35, 37, 37, 49, 49]
def r2sG : List Nat := [23, 39, 23, 51, 23, 53, 39, 51, 39, 53, 51, 53]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x6d59eb1c
  | 4, 0 => 0xa8684f4613ea33580f9d1b630b05d489
  | 5, 0 => 0x12268aed05b36a95034be7d5
  | 6, 0 => 0x12268aed
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0000000a000000088008800880088008000800080008000800080000000000022002200aa00aa0022002200220022000000aa000000aa0000000000aa00aa
  | 0, 1 => 0xaa00aa0000000000aa000000aa000000aa00000000000000a000a000a000a000a000a000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa8764
  | 4, 0, 0 => 0xcb96450c9214cb8655cb9635
  | 5, 0, 0 => 0xcb9640b9604cb9765
  | 6, 0, 0 => 0xcb964
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x300cf003000f3ff303c303f
  | 0, 1 => 0xfc0c3cc00333300
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xa355df157142a35a20142015
  | 0, 1 => 0xfeaebdea8b77b62
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 13 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 13 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 13 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 13 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 8
  | 5 => 2
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x526aae5f
  | 3, 0 => 0xb6ad889c27245b711eb530d912268aed
  | 4, 0 => 0x434be8bf12268aed0a521f3405b36a9505150376034be7d5019030d0002d503a
  | 5, 0 => 0x434be8bf019030d0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x0
  | 3, 0 => 0xc0000000000c00000
  | 4, 0 => 0x30000000000100000800000
  | 5, 0 => 0x2
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 4 s ws hint
  | 1 => checkCutEntry dom_6 roots_6 4 s ws hint
  | 2 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 3 => checkCutEntry dom_8 roots_8 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_9 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_9 == dom_9) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_9 goalM u ys) : RunD dom_9 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_9 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_9 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_9 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_9 roots_9 goal_9 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_9 goal_9 := by
    have h0 : isConstB dom_9 goal_9 = false := by decide +kernel
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

end S_9

theorem low_9 : Lower dom_9 roots_9 goal_9 7 := S_9.noCircuit

def dom_10 : Nat := 0xaaaa0000aaaa
def goal_10 : Nat := 0xa88000008000
def roots_10 : List Nat := [0x888800008888, 0xa0a00000a0a0, 0xaa000000aa00, 0xaaaa00000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 7 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0xaaaaaaaa00000000
def goal_11 : Nat := 0xaaa8a88000000000
def roots_11 : List Nat := [0x8888888800000000, 0xa0a0a0a000000000, 0xaa00aa0000000000, 0xaaaa000000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 7 :=
  lower_iso [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_12 : Nat := 0x2020202020202020
def goal_12 : Nat := 0x2020200020000000
def roots_12 : List Nat := [0x2000200020002000, 0x2020000020200000, 0x2020202000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_13 : Nat := 0x2222222222222222
def goal_13 : Nat := 0x2220200022000000
def roots_13 : List Nat := [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x2020202020202020, 41, 45)] (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xa0a0a0a0a0a0a0a
def goal_14 : Nat := 0xa0808000a000000
def roots_14 : List Nat := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xaa000000aa00
def goal_15 : Nat := 0xa80000008000
def roots_15 : List Nat := [0x880000008800, 0xa0000000a000, 0xaa0000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 4 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_16 : Nat := 0xaa00aa00aa00aa00
def goal_16 : Nat := 0xaa00a800aa008000
def roots_16 : List Nat := [0x8800880088008800, 0xa000a000a000a000, 0xaa000000aa000000, 0xaa00aa0000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000, 9, 25)] (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xaaaa0000aaaa0000
def goal_17 : Nat := 0xaaa80000aa800000
def roots_17 : List Nat := [0x8888000088880000, 0xa0a00000a0a00000, 0xaa000000aa000000, 0xaaaa000000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_18 : Nat := 0xaaaaaaaa
def goal_18 : Nat := 0xaa808000
def roots_18 : List Nat := [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000]

theorem low_18 : Lower dom_18 roots_18 goal_18 5 :=
  lower_iso [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_19 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_19 : Nat := 0xaaa8a880aa808000
def roots_19 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

namespace S_19
def pairsG : List (Nat × Nat) := [(7, 15), (7, 23), (7, 39), (9, 25), (11, 15), (11, 27), (11, 43), (13, 15), (13, 29), (13, 45), (17, 25), (19, 23), (19, 27), (19, 51), (21, 23), (21, 29), (21, 53), (35, 39), (35, 43), (35, 51), (37, 39), (37, 45), (37, 53), (41, 43), (41, 45), (41, 57), (49, 51), (49, 53), (49, 57)]
def r1sG : List Nat := [7, 7, 7, 9, 11, 11, 11, 13, 13, 13, 17, 19, 19, 19, 21, 21, 21, 35, 35, 35, 37, 37, 37, 41, 41, 41, 49, 49, 49]
def r2sG : List Nat := [15, 23, 39, 25, 15, 27, 43, 15, 29, 45, 25, 23, 27, 51, 23, 29, 53, 39, 43, 51, 39, 45, 53, 43, 45, 57, 51, 53, 57]
def mpG : Nat := 0x1fffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_19.map (· &&& dom_19)
def goalM : Nat := goal_19 &&& dom_19
def NN : Nat → Nat
  | 5 => 11
  | 6 => 30
  | 7 => 15
  | 8 => 5
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x8d3c668a89a0a79760d0fa3a51e446474a42e7bb444881f53ad11f9b33f1fe37337834762ad1bd39127d9804
  | 6, 0 => 0xf03af885c2e232c17d07626d77e0f0a871b7d4da6f2cce536dd9cd9c6a6081b9527a6a134f11434b4a8290cd46e25b8143dfc0a9369f6afd2e67f65129c5488423b1c2792355f3541f5f3fa01d3412d51589473214bc139413663fe80fc935a60f9f6c000c7a25d10baabe1c08f51fb1048a5eef00cba419
  | 7, 0 => 0xb5a6c74bb3d718eb8a4c1367891a7b53731476bf51e879b74dca022d450553513e19393a2928d39a1da0c72915498bdd0f40648b0121d32500a80964
  | 8, 0 => 0xf7c60b5c5e605c4a434117361c4118391161fe36
  | 9, 0 => 0x5e605c4a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0aaaaaaaaa0a0a0a0a0a0a0a0a00aa00aa00aa00aa0000aaaa0000aaaa000022220000aaaa000000aaaaaaaaaa000000aa000000aa00000000aaaaaaaa
  | 0, 1 => 0x808080aa808080aa8080808080808080808080800000000080808000808080002a2a2a2a2a2a2a2a2a2a2a002a2a2a0022222222aaaaaaaa2222222222222222
  | 0, 2 => 0xa0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a080a0a0a000a0a0a000a0a0a000a080a080a000a000888888888888888888888888000000008888880088888800
  | 0, 3 => 0xaaaaa0a0aaaa0000aaaa8888aaaa0000aaaa8080aaaa0000aaaa0000aaaa0000aa88aa88aa00aa00aa80aa80aa80aa80aa80aa80aa00aa00aa00aa00aa00aa00
  | 0, 4 => 0xaaaaaaaa00000000aaaaaaa0aaaaaa00aaaaaa8080808080aaaaaa00aaaaaa00aaaaaa0000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x91c615491685c61644e60185913845024757485591c61748a691c61748f692179b5d26012185100501820610059227185d2691c61440e6
  | 6, 0, 0 => 0x9207185d239c09185d138469217185d235e481c61751279217185d21de485f617592791e71b61749c091c5d224568607185d245c071a61748060185d238401a17185d6491701c61748101a47185d244379217185d231e47185d24417
  | 6, 0, 1 => 0x718591394001c60818050247dc5d2158085c61218060005d2144014091c5d2345602481c612198091c61720769217185d209c0018486100500091c65749648dc617592791c6174d245c091748e1446
  | 7, 0, 0 => 0x85c6174806000917485114091c61748d60247185d621807185d6491602471a617498091c617481692181c61749e485c617592791c6d85d245c091c6174906024617592118091c61748b6000717485014001c6172005
  | 8, 0, 0 => 0x9217185d260247185d25024717485501c617480591c6174916
  | 9, 0, 0 => 0x247185d25
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 40
  | 6 => 46
  | 7 => 46
  | 8 => 40
  | 9 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc7fffffe38f1e38fff80e3fe03ff1f801ff81fffffc0fc000e001ffff
  | 0, 1 => 0x3f00038000001c00000000000000ffffffc7e07ffe3fe3ffffff1c788
  | 0, 2 => 0x38e1c381c000000038700001c38000001c00038e1dc01c00000003870
  | 0, 3 => 0xe38fe00703ff003803f801c01fc001c701fc0e000ffc70007f038003f8
  | 0, 4 => 0x1ffe0000ff8fffc7e00001ff03fff1f800000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb467efdda30d1a18b6d00c1b602d50900148804b76fc0240008000ddbb
  | 0, 1 => 0x9244b8049225c02400080004893ff6dbb47fb6dda36c3bf77b618708
  | 0, 2 => 0x4b9e5cba5cc08112e7972e961cb9309941ca9279e3dc93c408848c78f3
  | 0, 3 => 0xfbdff977b7ff5bbcb7fa5de49fd2abdf5bfecedb7ffe76d2ffb3a497f9
  | 0, 4 => 0x1fff2244ffffffffffdab5ffdbfff7fed2240
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 29 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 29 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 37 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 37 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 37 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 37 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 20
  | 5 => 90
  | 6 => 240
  | 7 => 62
  | 8 => 6
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xf03af88572c2047d61edf3b55e605c4a4fcebb694ed8bfcf4a8290cd4480c13e2b63d4fd2b3b1b9125911c3723ed6593208fb8dc1dec8e4f1ccee13f17f0360313d949a60a0a0329098141df0609f98b
  | 5, 0 => 0x426633c93e66ece63e0f047a3ba7edb53ad8f02b38f23fa533fc7a2f310e22f02facf2132ef225e42e9fbd452c66e7d62bbe87742ba647972a86e3002990e76628b4738928a50b452788959126fb56e0251474282501d2a62073668820052d471f7f36fb1eeb4bfe1da0c7291c26afa21b049a7018c309b318a87de517d42cc9175f46c515f1d2ff15c4041e12a105c71159f289110240e30f9e67900f40648b0ee31f480eb452f70d3c0f210c1dced209e48b7109b76e85096c6be108634cbc084deefe0801cde906693a6d063ecf110631843f040e0645037e67c103285ed4022e903001a200d10122735a0121d32500b5eb5300a80964008f2da3004943ce
  | 5, 1 => 0xe9dfd64bd1d8d1eebb7c6bd6b3d718ebac1e9d928d5de9048a4c136773d849e7731476bf6f532b206ed4276f6e9174cd6ae83cbf5e605c4a587282bf578b15d851e879b75198b7734dca022d4cdcf4904c8adaae4b3118eb4a7f0a3d494313e545121d1c43e83dc2
  | 6, 0 => 0xe08c0c60dd4f2ce0d9384840d521cc80d31b0f40d2bfcd10d186c150d1465790d0a6d0c0c60ba150c1ee5a30bfa440f0bdc11cc0bcb458d0bc2085d0b6ea98c0b5305160b3367230adb34500abc83320a81b759094007820922086908c1e2a008bca936083f7b9408181ad007d62d8f07ad3e87079e510f0794d21a06b500fb06a491b2065402f6061475da05edbba505ccae18047d664a04792a8c04474d0c04399b7303f28392039b52e1035496cb033a336202e69a9502db91f402c881f802b6c37802a311da02a0e5cc029a37e80281821502627e22023b5a6e0207b85401a4227f00d5a92a00b71e6200a10b94009d21c2008f2da30065c173002fc57a
  | 6, 1 => 0x22f83ce121d8f9a81f77183c1f4c47991ec1c3381e1838511db9b2191d29ed081d1e5b601cbc48d81c69d93d1c4118391c0e1d0d1c00563f1bfc41891bf3e7221b123e581ae1bf581add3c401a5aa6ad19df927e1974bd3919602f58190b757e18eddd8418c72c111843097e17e3852717cb900917c93fbd1709fd3416dbdd4f16afd13b165fb574161d34e91610ed0215eb6e121488f89114741099144249d31422a31413f8d96e13f815ff13e8d03613c4e272137358871344ddcf12a3d4f412768c431161fe36114a745b10d6b7f21071687c106295da1029da780fb51e2f0f8ce0c00f7c2a5e0ec624110e828a870e3ec9340e35f2bb0e2959890e1bddba
  | 6, 2 => 0x4cc959904c8adaae4c5d80774b4c23294a96f5e04a83e1b1498c4f06482ccf5646fb374246fa98b346e6ab29454f91e3450553514406f62b43cdf2da43411736418ad45e4112d31e40be8b463f5f9d343eef5f153e57878c3e55ea103cb816b73aebb523396af6233902e45738a8d6563720ffe2354ea01c3535f1b8350a2b563422b27333ef7b4633ef5b2133d4f27133b4f68632aabd1932767163324517e23040067f2f242d1d2e9253412d6a7b0c2d4466f72ccd84ab2cafe8142c22aaea2b59062a2aeccb962aaf6cff29ae28eb2928d39a28c0cc84287b01d2280891d327e8f4af2672f28a263cc900260a814724a5cc30246e49ab23dfa9d32397c488
  | 6, 3 => 0xf7c60b5ce72fb13fca32efc1c497fde2afd6b753adb68e38aa6f415ba340bece9ddd3c3a9a477ca09587a9e49547402a92f6dbb792a4f4cc9208b69d8fe0acf78b2a39e78815eca881cad71b7f5249027cab3df07c0caf977bd4db1d78f8e4c3766e47ea7554e2536d39d8776b32a6f764be8836641584cc63f4f5da5e605c4a5da388245cc77c185bda9a4b5b1a3bce56588a2f55f37dc5558d86b854bd057754644cf753acd3d3520a1d1450fbb5a4503b99b04f9812614f85b9324e211583
  | 7, 0 => 0xf7c60b5ce72fb13fc3077eadbe2bf3a8bdf41f2e9a477ca098ac46c598aa05cd9208b69d75d43a97742ef8f0685c0d11641584cc629446175e605c4a5c6c52da5b1a3bce568d02b44f85b9324b9ac9714b5f4b934734fb6c4341173638a8d65634a87c1e327edc0c3211f5d731dbabbb29a1cf9b277bdc3a23375fe4211c77bc1d639a991c4118391b7498d71979e5c518faf7bd189f90ca1733c399143a212e13d9649e12a6d5171161fe360fd928f90fb51e2f0f6df4c60ee741b50e828a870e1bddba0e08c0c60d6675210d1465790b7fb2c00922086908bc17b407d8153903e7dec102a311da02875b1e00e1cd8e00cad8d0007484ba
  | 8, 0 => 0x98ac46c55b1a3bce4f85b93229a1cf9b08bc17b400e1cd8e
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x304014d400853010000000001c00000000001000c130c0800000c010200051030801402444d3010000030041400000851012148d134c0000000c91042108c130c0800000000070000021440400000c01020000002840000000000090000000000400000c0106
  | 5, 0 => 0x91300800000000000225450300c0c00048852010009103080400000000050000021440000000021000000031040c00000c0105000d101081000000401030005103080000000000030004920480000244042040000000001800000c01050000000002000000c010600000000004000000a1010000021440400000000070009103080400000000040000000000c000180e20000000214400000000e10000091310808002344d200
  | 5, 1 => 0x10040800000c010000006038808001440c20100000324410000000000700051300804002008c2020009110480000028022000010013480000344402040000000001800000000081000c130c0800000c01020000000001400000000050000021440000000000020000000001c00200402020000002840000244c020000000214400000000000700000214400000000c1000000003041800100c02020001223080800000c0106
  | 5, 2 => 0x50300808000280e2021000c130c0c00028062000009030080800000000010000003040000400852000000003040095140c030200012100808000000000500006008800000000000000000000010002444020400000104400000180a2000001221480000000000070010c214800000484d20130004310c08000008510000000000000000080e200
  | 6, 0 => 0x9130080000000000090000003840400000851010000002840c000000e1010000013440400000c410200000000004001440c2010000031040800008062020000000841000000c0100000001044000000000005000000000180000006100000d1100810000008c1020000020040800048c02000000002841000000851000000000001c00000000050000a018808000000e1010000023040c0000000007000000084040000085101
  | 6, 1 => 0x2840000000061040001210080800000000090001231080c000488520000091100808000000c1000000000001c000000000500012310808000000210000000000008000000000500000008400002444020200000028400000008c1020010032481000244c420300100214804000280e20000000038404000000e1010000031040c000000c1010000001840400000c410200091130808000000210100000210408000000c100
  | 6, 2 => 0xd110081000000811040000000840800000000020000000000800018022010009110080c000000e10000000104404000000a10100000028408000004d1000000003840400300402020000003840400000000010000000002400000000000000010440000000c4103000000304000000084102000c010080c000000610000000300408000004d1010000020040c000000a10200000030400000000e100000000000080000000000
  | 6, 3 => 0x100410000000a10000000030404000000e10200006038800000004c1020000031040800244402030000010040800048c020100000214404000000e10000000000004000000e10100000214400000008010200000134400000000c10100012300800000008510000000324410000000000500000214404000000a10200000214400000180e20200006038804000000000000000018400000080e2010005030080c000004d101
  | 6, 4 => 0x21440000000000070000000001800144c02010000a038808000000a1020000003040000000021010000a018800000000e10100000038400000000a1020000010041000000041040000003840c000008d1000000000000000000000060000000001400000000050000013440000000c01000000003840400430852000000002840400000411000000003840c00400852010000023040800000000060000000001c000000e101
  | 6, 5 => 0x28408000000000500000000004000000a1030000010040800048852000001210080800000041040000000841000000c01010000000002000038022000000023040800000851010001221480400000061000000203880800144c02000001210081000000851000000002840c00000401040000c13080c0000000004000d110081000430852010000010040c000008510100004310808000000c101000000184000000000007
  | 6, 6 => 0xa038808000000a1020000000001400000c010100000000008000000e1020000003840800000c010000000000014000000a1020009130080400000061000000002840800000c01000000000001c000000000000000134404000180a2010000000001800000000000000e02881000000000080005030080c000000c1030000000000400000000000000000000800000000070000010040800000000010000000000400000c9104
  | 6, 7 => 0x214400000000a1020001221480000140c020200000300400000000000500000000008000000a10200002038800000000e10200000214400000000e10200000000018000000a102000000084000000000005
  | 7, 0 => 0x400000c01000000031040c000000000400000100408000000000100000038400000000000200000000008000004c10200000000000000004010400000000000000000a1020000030040800000c010100000124404000000a1030000000000000000021030000003840c000000000500000000008000000e1010000000000000000000010000000000000000061000000030040c00000000040000000000c000000e104
  | 7, 1 => 0x800000000070000000000c00000000020000000000800000c910400000000008000000e10000000000014000000a10200000214400000000000300000300400000000000400000000000000000000100000000000000000e10200000000004000000000400000028400000000000400000000008000000000200000214400000000000100000000008000000e1020000000000c0000000001
  | 8, 0 => 0x800000000000000000000c0000000003000000000000000000004
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_4 roots_4 7 s ws hint
  | 1 => checkCutEntry dom_5 roots_5 7 s ws hint
  | 2 => checkCutEntry dom_9 roots_9 7 s ws hint
  | 3 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 4 => checkCutEntry dom_11 roots_11 7 s ws hint
  | 5 => checkCutEntry dom_13 roots_13 5 s ws hint
  | 6 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 7 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 8 => checkCutEntry dom_17 roots_17 5 s ws hint
  | 9 => checkCutEntry dom_18 roots_18 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_19 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_19 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_19 == dom_19) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_19 goalM u ys) : RunD dom_19 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_19 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := range_split z5_0 (z5_8)
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
theorem z6_24 : ∀ i, 24 ≤ i → i < 30 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 24 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 30 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (z6_24)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 8 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := range_split z7_0 (z7_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := z8_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := z9_0
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z9 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_19 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_19 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_19 roots_19 goal_19 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_19 goal_19 := by
    have h0 : isConstB dom_19 goal_19 = false := by decide +kernel
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

end S_19

theorem low_19 : Lower dom_19 roots_19 goal_19 10 := S_19.noCircuit

def dom_20 : Nat := 0xcccccccccccccccc
def goal_20 : Nat := 0xccc8c880cc808000
def roots_20 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 10 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19

def dom_21 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_21 : Nat := 0xf0e0e080f0808000
def roots_21 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 10 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20

def dom_22 : Nat := 0xcc00cc00cc00cc
def goal_22 : Nat := 0xc8008000800000
def roots_22 : List Nat := [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000]

theorem low_22 : Lower dom_22 roots_22 goal_22 7 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_23 : Nat := 0xf000f000f000f0
def goal_23 : Nat := 0xe0008000800000
def roots_23 : List Nat := [0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000]

theorem low_23 : Lower dom_23 roots_23 goal_23 7 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22

def dom_24 : Nat := 0xff000000ff0000
def goal_24 : Nat := 0xe8000000800000
def roots_24 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]

theorem low_24 : Lower dom_24 roots_24 goal_24 7 :=
  lower_iso [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23

def dom_25 : Nat := 0xff00ff00000000
def goal_25 : Nat := 0xe8008000000000
def roots_25 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]

theorem low_25 : Lower dom_25 roots_25 goal_25 7 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24

def dom_26 : Nat := 0xff00ff00ff00ff
def goal_26 : Nat := 0xe8008000800000
def roots_26 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

namespace S_26
def pairsG : List (Nat × Nat) := [(7, 23), (7, 39), (19, 23), (19, 51), (21, 23), (21, 53), (22, 23), (22, 54), (35, 39), (35, 51), (37, 39), (37, 53), (38, 39), (38, 54), (49, 51), (49, 53), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [7, 7, 19, 19, 21, 21, 22, 22, 35, 35, 37, 37, 38, 38, 49, 49, 50, 50, 52, 52]
def r2sG : List Nat := [23, 39, 23, 51, 23, 53, 23, 54, 39, 51, 39, 53, 39, 54, 51, 53, 51, 54, 53, 54]
def mpG : Nat := 0xfffff
def pool6G : List Nat := []
def xsM : List Nat := roots_26.map (· &&& dom_26)
def goalM : Nat := goal_26 &&& dom_26
def NN : Nat → Nat
  | 2 => 1
  | 3 => 8
  | 4 => 16
  | 5 => 33
  | 6 => 28
  | 7 => 8
  | 8 => 3
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x310b853
  | 3, 0 => 0xc1651500b1d05900674420505268ee50310b8530155147c013f8a73000403dc
  | 4, 0 => 0x5129b06010beb7c80e8582210a04962b0423b5da041eac5703b35cb00390f4b7024e6241021827e9013f8a730100c70a007abd3b00639d04005177f00001d357
  | 5, 0 => 0x795e5f4c630b6fa64e839eef3ef063c82715944f1d303a381bab7b6a185c0dd218204cc71693f9ce10beb7c80f20f4390ec876490c7419e20c365b8609131eb3083120d3074ade44057cfe7a056b2cd604fafb52035e18a70346ace5030d9e79027c63d7025559630230ae0d01d6981101c22cf4018e8e470141925200cfbac100552ab4
  | 6, 0 => 0x4ae8fcce3c24ab4420c70dce1d96bdaf177cb9861730e1120fb3e3730e3447020c8ccfdc0c4195a70b3b3b4207a9dac50568907a04dbcf38046346ce04604064040982fe03ec833203d5b70203b5bf6702f719bd02b7d74902066c9c01b7fdce018b3b31012ab14200989ed80039c3fe
  | 7, 0 => 0x68111a2b53083dc521c2b7f910aca41e08c0a32103f2196302709e6e0231b28e
  | 8, 0 => 0xa5e2e6eb11927a610893e084
  | 9, 0 => 0xa5e2e6eb
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf00ff00000000000f000f000f000f000c00cc000c00cc000c00cc00000000000000ff000000ff000000f000f000f000000077007700770000000000ff00ff
  | 0, 1 => 0x4400cc004400cc003f003f00ff00ff003f003f003f003f003300ff003300ff00330033003300330033000000ff0000002a00aa00aa00aa000f00ff00ff00ff
  | 0, 2 => 0x770077007700770077000000ff0000005f005f005f005f005500ff00ff00ff005500ff005500ff0055005500ff00ff00550055005500550055000000ff0000
  | 0, 3 => 0x88008800000000008800000088000000880000000000000080008000800080008000800000000000800000008000000080000000000000007f00ff007f00ff
  | 0, 4 => 0xaa000000aa000000aa00000000000000a8008800a0000000a000a000a000a000a000a00000000000a0000000a0000000a00000000000000088008800880088
  | 0, 5 => 0xc8008800c0000000c000c000c000c000c000c00000000000c0000000c0000000c000000000000000af00ff000f00ff00aa00aa00aa00aa00aa00aa00000000
  | 0, 6 => 0xea00c00000000000e000c000a0000000cc00cc00cc00cc00cc00cc0000000000cc00800080008000cc000000cc000000cc00000000000000c800c000880000
  | 0, 7 => 0xf0000000f0000000f000000000000000ec00ec00a000a000ec00cc00cc00cc00ec00cc00a0000000ec00a000ec00a000ec00a00000000000ea00c000ea00c0
  | 0, 8 => 0xff000000ff000000ff00000000000000fc00f000cc000000fa00f000aa000000f800880088008800f800000088000000f000f000f000f000f000f000000000
  | 0, 9 => 0xff00ff0000000000ff00c000c000c000ff00a000a000a000ff008800880088
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0xfd8283
  | 3, 0, 0 => 0x7ec541c488fd82847edd3a0482cd3a3400fd82838d05b2049709aa448f0d7284
  | 4, 0, 0 => 0x971e0b512b2e3c15ea5603f689d02cb8f05b20596fdc2740b1992d5291404b70c9224b8f057a258f017293ab1dd395ca5404b84d5224b6ab13a358ed162848b1a0bb6aa565ca7ec54acb8ed93a05
  | 5, 0, 0 => 0x8f1a0354881a5c77cd548269705a325229a3c162b94a868f1a0b5521d804b7ed52135971e0b55069804b9305aa75971d7244035a5c780b91a06971e0b56895a5c774d562968d05a3258a5a5c78ac97296011e035507165c782d54846
  | 5, 0, 1 => 0x12c88b0c0d65c782f14a16971e0b5526180407ed19295971d7294479a5c782b149f6971e0b554a5a5c782d54966971e0b55205804b8f057a958f01ab25091a5c782d59a96011a0a84e2d63c174e5aa96971e0bb6aa5a5c780b949e6
  | 5, 0, 2 => 0x25c782d54996
  | 6, 0, 0 => 0x12e44782d54b4b8f05aa92441e5c782d54a036f2e3416aa52227971e0bd6aa523cb8f05fb5527de5c780fdaac52e025c782d17116012e33f6aa52300971e0a9442da5c78301aa910f2e3c16aa10177971e0bf6aa4bb808f060355249804b8f05a9118c025c780d54a26
  | 6, 0, 1 => 0x971e0b55298a380971e0b5526da5c782d54a71ee0004b82c93a05971e0be6aa51b80971e0b55239a5c78cd572948e023b5529c300600025a916181a80971e0b55215a5c782d56ab52f2e3c16aa4e157
  | 7, 0, 0 => 0x25c782445a80971e0b55249a5c782d54a726e025c78d05a916012e3c16aa10300971e0b55aa5a5c782d54a74cf2e3c682d54a47
  | 8, 0, 0 => 0x4b8f05aa95012e3c1522d65c782fdaa96
  | 9, 0, 0 => 0x4b8f05aa95
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 25
  | 3 => 32
  | 4 => 39
  | 5 => 46
  | 6 => 53
  | 7 => 53
  | 8 => 46
  | 9 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3ff003c30c3330f3330003f0303cf303cf0000ff
  | 0, 1 => 0x333c3fcffffcf3ccff33ccc30cc0fc0cf3f3ffff
  | 0, 2 => 0xffcf0fc0fcff3ccf3ffff3fc3f30fff30c0f00fc
  | 0, 3 => 0x3000000c0000000003000000000000000fffff
  | 0, 4 => 0xc03c0c0000033000c3300c0000030000000030f
  | 0, 5 => 0x3c0030c303000000c0000003ff0f0cf3f0cf00
  | 0, 6 => 0xf00003030333cf3330030003300cc300000300c
  | 0, 7 => 0xc00f0c000033f33333cf3333030cff30c000f0ff
  | 0, 8 => 0xfc0fcfc000f3ccccfc3cc030fc000cc3cf3c3c00
  | 0, 9 => 0xfff00ff0c3fcc33fc30f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1570a142081570a1570a01502015570000000055
  | 0, 1 => 0xa35825ca7d5ca2849d2248820488755df7f1575f
  | 0, 2 => 0xea8a0ea8f5b6288a35d7a3582a20d5a2080a20d5
  | 0, 3 => 0x1570a1425d1420801557015020005500000fffaa
  | 0, 4 => 0x5ca7d5ca285df7f49d7749d2248875488201575f
  | 0, 5 => 0xb77dfa35d7a3582a20d5a20805df2a5df7f5df2a
  | 0, 6 => 0xfffaaebdf7b77dfb778ab77dfb62ddb6288b77df
  | 0, 7 => 0xea8f5ea8a0fffffffffffffffffffffffaafffff
  | 0, 8 => 0xfeafdfeaa8ffffffffffffffffeafdebdf7ebda2
  | 0, 9 => 0xfffaafffffffffffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 20 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 20 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 76 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 76 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 76 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 76 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 1
  | 3 => 6
  | 4 => 36
  | 5 => 74
  | 6 => 79
  | 7 => 20
  | 8 => 2
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0xcb3cc68
  | 3, 0 => 0x515e73d03599dc60319608f01acd23b0163d84c00a51026
  | 4, 0 => 0xa5e2e6eb260c8d9d1d96bdaf1b3f9290198129ea18fbe13a136270f910f43d6c0bc0520f0a50d57a0a063fb6090c6d0e080e76c90803777f06554445057b417d046f0bf60421203c03fc5e8f030de36d024178aa02114d4c01ef655d01ea025e013af9770136e0c7012f3673010ed8ca00f0f98500e3740f00c8d464009e711d007aa0830060566b001d5e240005063e
  | 5, 0 => 0xf21228d0eec98a00e7d981e0c4195a70b56c99f0b1a3b790afb958d09339b470923c7e80904da7808c9db8708c0a32108134bba078324e5077cc4ca06dd16ef06d5935606211a8105f8e05505b3b15a05ac75f50518e00904cc777304c2802404bc8238048c55b4046c5e03044d10b40405062803f2196303b925f603b6903003a20db60333f01302b64e5d02659cc00250eb6a0207fb1f01e24fbe01df949101caece701b950f8019c19bc01909ffa017e1b34017e086e016f2a56010133e900f4059c00d83dc700cf83d000a44a59007e9981007a1d530075924800752f6d006d592b0057a851004e583b004ca7ea0049719b003c1023001e2cd4001e0ce0
  | 5, 1 => 0xa5e2e6eb68111a2b53083dc54b064ef642bdf8fa3c24ab4439fd1e081a5575f0121585720fc7331c
  | 6, 0 => 0x11927a610f6ad2e00ef8dc560da269960ceb1d0f0c2a4b9e0c1ee6c50b6b61cb0b0e27130a9320ff0a7d6b970a76eece0a0e725e095899a508e2f50508a624190893e08407e248dd06ad6569068f01cb065fd1f60638f31805d9cfb805592266052c7e4104e70ec604dc86a704aab3060420c04403aeef770384ce400380cdb0036f23d00306063302e128ce02d9c9550279d20602709e6e0254dbe2024021a3021182490208df600207a95e01ea025e01c3f1a001956e5501922b2c018b843b018699b00176ab71013c6bd1012ce94e011ce88f01035ad000f96b9500d465af00a97c80005678fc003dfffe00357ad50031d8c80019568600141c5000053444
  | 6, 1 => 0xa5e2e6eb598100db2bc3a1b12b5bf89229ff020221c2b7f9218974de1da12a871a5cf6ba191065b218b07b6218af50ce1635af2f1329e0ad12158572
  | 7, 0 => 0xa5e2e6eb1c0f707816d8e31012c3ee3b1249c6e811927a610b063f8a0893e08406a9707f066ea6de05592266046f0bf603de457102801eab0211824901e5f44700c30f67007a1d53003c102300340466
  | 8, 0 => 0x1249c6e8003c1023
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x3214043484400
  | 3, 0 => 0x51080244c040200040404c43000014c24404300350484240440150048424c44000000000000003
  | 4, 0 => 0x200040020483000000000000002000c0200c830000014414c8301000000000a10100040404c430200000000c010100084414c83000000000080103000000480c201000004008c202000000000000100000000000000000000008103000c03444030000144424c0302000000000610000000000c01010000000000004000000000210200000000c410200048424c43020000024040203000000000000100084414c83000000042404200001404244c3000000000000000000000008010100000000c0101000c830080304
  | 4, 1 => 0x95140c030100000000801000000000000001
  | 5, 0 => 0x480c20300000410c020000000200c82010000012004202000000008c102000003204c20000000048c4202000000488420400000000000020000000000004000003100420400000000c410000000000c4101000003008c20000000000000010000024004201000000008c102000000000000300000414c8200000c8020c030200000008062020000043440202000000000210200000434802040000000002101000000000810200000420c4203000004308020100000040842030000000000000000000000000000000414c8200
  | 5, 1 => 0x40000000084104000001000c20000000048842010000000000003000000008010200000000c81000000000000000000c8020c03040000043440200000001400e2000000000000000000000008010100000240c42000000000000001000000008410200000400c8202000000484c20400000000c81030000000002100000002404020300000000c810100000000c410300000410c820000000000021020000000000003000000080a2000000000000004000001008420100000400c420000000020482020000000000002
  | 5, 2 => 0x2100000000000e1000000000000003000c4010c030000000410c0200000000000000300000000c810200000000000020000004840201
  | 6, 0 => 0x801030000000008102000000000e1000000000002102000000000000100000000c810000000410c8201000000280e201000000000610100000010c020000000400c42000000000000004000000000e1010000000006100000000000e103000000008c102000000080e2010000000000001000003008c201000000000610000000048c420200000000021000000000084103000000000a100000000488420300000000000010000000084103000000000000200000000841010000000008102000000000610000000000c4101
  | 6, 1 => 0x2100000000000e100000000000000100000400c420300000000c010100000000801000000000000002000000000a102000000000e1040000000000003000000008010000000000c410200000000c810200000000c0100000000004c100000000000a101000000008410000000000c0104000003004c201000000004010200000000c41040000000040101000000484020100000000c41010000000002102000004008420300000000841000000000080101000000000c1000000000040100000000000e101000000004c103
  | 6, 2 => 0xe1030000000040102000000000e1000000000806203000000000a10000000400c82000000000000002000000000e103000000008c103000000488020200000000c01030000000002102000000000a1000000000000002
  | 7, 0 => 0x10000000000002000000000a10200000000000030000000000001000000000000100000000000020000000084100000000000000000000000c410100000000000010000000000004000000000000200000000061020000000002100000000000c103000000000000400000000000000000000084103
  | 8, 0 => 0x30000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_9 roots_9 7 s ws hint
  | 1 => checkCutEntry dom_22 roots_22 7 s ws hint
  | 2 => checkCutEntry dom_23 roots_23 7 s ws hint
  | 3 => checkCutEntry dom_24 roots_24 7 s ws hint
  | 4 => checkCutEntry dom_25 roots_25 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_26 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_26 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_26 == dom_26) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_26 goalM u ys) : RunD dom_26 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_26 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 8 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := range_split z4_0 (z4_8)
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
theorem z5_32 : ∀ i, 32 ≤ i → i < 33 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 32 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 33 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (z5_32))))
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
theorem z6_24 : ∀ i, 24 ≤ i → i < 28 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 24 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 28 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (z6_24)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := z8_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := z9_0
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z9 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_26 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_26 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_26 roots_26 goal_26 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_26 goal_26 := by
    have h0 : isConstB dom_26 goal_26 = false := by decide +kernel
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

end S_26

theorem low_26 : Lower dom_26 roots_26 goal_26 10 := S_26.noCircuit

def dom_27 : Nat := 0xffff0000ffff
def goal_27 : Nat := 0xe88000008000
def roots_27 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_27 : Lower dom_27 roots_27 goal_27 10 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_26

def dom_28 : Nat := 0x5555555500000000
def goal_28 : Nat := 0x5440400000000000
def roots_28 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_28 : Lower dom_28 roots_28 goal_28 7 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25

def dom_29 : Nat := 0x3333333300000000
def goal_29 : Nat := 0x3220200000000000
def roots_29 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]

theorem low_29 : Lower dom_29 roots_29 goal_29 7 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25

def dom_30 : Nat := 0xcccccccc00000000
def goal_30 : Nat := 0xccc8c88000000000
def roots_30 : List Nat := [0x8888888800000000, 0xc0c0c0c000000000, 0xcc00cc0000000000, 0xcccc000000000000]

theorem low_30 : Lower dom_30 roots_30 goal_30 7 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_31 : Nat := 0xf0f0f0f00000000
def goal_31 : Nat := 0xe08080000000000
def roots_31 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]

theorem low_31 : Lower dom_31 roots_31 goal_31 7 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25

def dom_32 : Nat := 0xff00ff0000000000
def goal_32 : Nat := 0xfe00e80000000000
def roots_32 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]

theorem low_32 : Lower dom_32 roots_32 goal_32 7 :=
  lower_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30

def dom_33 : Nat := 0xffffffff00000000
def goal_33 : Nat := 0xfee8e88000000000
def roots_33 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

namespace S_33
def pairsG : List (Nat × Nat) := [(35, 39), (35, 43), (35, 51), (37, 39), (37, 45), (37, 53), (38, 39), (38, 46), (38, 54), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [35, 35, 35, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 44, 44, 44, 49, 49, 49, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [39, 43, 51, 39, 45, 53, 39, 46, 54, 43, 45, 57, 43, 46, 58, 45, 46, 60, 51, 53, 57, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_33.map (· &&& dom_33)
def goalM : Nat := goal_33 &&& dom_33
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x144f6d7f
  | 6, 0 => 0xc98d0c7
  | 7, 0 => 0x854d8be
  | 8, 0 => 0xbe37fa2f009e3c06
  | 9, 0 => 0xbe37fa2f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000f0f0f0f000000000cccccccc00000000aaaaaaaa00000000555555550000000033333333000000000f0f0f0f000000000000ffff00000000
  | 0, 1 => 0xffff000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x732105
  | 6, 0, 0 => 0x742105
  | 7, 0, 0 => 0x875315
  | 8, 0, 0 => 0x876545875415
  | 9, 0, 0 => 0x876545
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 24
  | 6 => 24
  | 7 => 24
  | 8 => 24
  | 9 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe00ff80070381f80381c71c01c0e3fff8fc703f1f8e38e3f1f81c003ffff
  | 0, 1 => 0x3ffc0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf24ffa4a74ba5f94b95cf3c93c9e7fdb0d8602d1a8c3062d16818001b6db
  | 0, 1 => 0x3ffe4924
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 30 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 30 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 9 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 9 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 9 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 9 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 10
  | 7 => 10
  | 8 => 3
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xbe37fa2f
  | 5, 0 => 0xbe37fa2f0854d8be
  | 6, 0 => 0xbe37fa2f0e32f4250ca5baa2074804950446120002f432fe025ffba9022fd7f60183c7bc009e3c06
  | 7, 0 => 0xbe37fa2f1f4b03c71a89ccf80b87d7e6062d6bb7048b280d03cb1e610183c7bc00fff5f6009e3c06
  | 8, 0 => 0xb87d7e6048b280d00fff5f6
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x6100
  | 6, 0 => 0xa1040000e1020080a2020180e205008062000280e201028022000000e10200006100
  | 7, 0 => 0xe10300002100000000020000610100000000000000000000e1020000000200000004
  | 8, 0 => 0x20000000000000003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 5 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_28 roots_28 7 s ws hint
  | 1 => checkCutEntry dom_11 roots_11 7 s ws hint
  | 2 => checkCutEntry dom_29 roots_29 7 s ws hint
  | 3 => checkCutEntry dom_30 roots_30 7 s ws hint
  | 4 => checkCutEntry dom_31 roots_31 7 s ws hint
  | 5 => checkCutEntry dom_32 roots_32 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_33 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_28 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_32 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_33 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_33 == dom_33) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_33 goalM u ys) : RunD dom_33 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_33 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := z8_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := z9_0
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z9 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_33 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_33 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_33 roots_33 goal_33 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_33 goal_33 := by
    have h0 : isConstB dom_33 goal_33 = false := by decide +kernel
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

end S_33

theorem low_33 : Lower dom_33 roots_33 goal_33 10 := S_33.noCircuit

def dom_34 : Nat := 0xff000000ff00
def goal_34 : Nat := 0xe80000008000
def roots_34 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]

theorem low_34 : Lower dom_34 roots_34 goal_34 7 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24

def dom_35 : Nat := 0xff00ff00
def goal_35 : Nat := 0xfe008000
def roots_35 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]

namespace S_35
def pairsG : List (Nat × Nat) := [(9, 25), (10, 26), (11, 15), (11, 27), (12, 28), (13, 15), (13, 29), (14, 15), (14, 30), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [9, 10, 11, 11, 12, 13, 13, 14, 14, 24, 24, 24]
def r2sG : List Nat := [25, 26, 15, 27, 28, 15, 29, 15, 30, 25, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_35.map (· &&& dom_35)
def goalM : Nat := goal_35 &&& dom_35
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8299b27f1e1cd3f5170f4d9c162ee1b101eed52c
  | 4, 0 => 0xc157d9278299b27f781943e868d7846c5d5bb24528a6614227dd34650e21469b032235bb
  | 5, 0 => 0x8299b27f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00000000000000aa00aa0000000000aa00a00000000000a000a00000000000880088000000000033003300000000000f000f00000000000000ff00
  | 0, 1 => 0xff00cc0000000000ff00aa0000000000ff00000000000000fa00fa0000000000f000f00000000000ee00ee0000000000ee00aa0000000000cc00cc00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xdb864fb764dc844db854db984
  | 4, 0, 0 => 0xb86040db864db8605edb8650d8614dba865db8635db8625db8765
  | 5, 0, 0 => 0xdb864
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x6d06006000ce71e0f1ff
  | 0, 1 => 0xf8ee6de001fd1f01ef06d18e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x50a2ed2ed0e40aca5160b0a4
  | 0, 1 => 0xfffffff5bbfd9f47ef7ef5ae
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_35 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_35 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_35 == dom_35) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_35 goalM u ys) : RunD dom_35 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_35 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_35 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_35 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_35 roots_35 goal_35 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_35 goal_35 := by
    have h0 : isConstB dom_35 goal_35 = false := by decide +kernel
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

end S_35

theorem low_35 : Lower dom_35 roots_35 goal_35 6 := S_35.noCircuit

def dom_36 : Nat := 0x5500550000000000
def goal_36 : Nat := 0x5400400000000000
def roots_36 : List Nat := [0x4400440000000000, 0x5000500000000000, 0x5500000000000000]

theorem low_36 : Lower dom_36 roots_36 goal_36 4 :=
  lower_iso [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_37 : Nat := 0x5500550055005500
def goal_37 : Nat := 0x5400400054000000
def roots_37 : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]

theorem low_37 : Lower dom_37 roots_37 goal_37 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550000000000, 14, 46)] (by decide +kernel) (by decide +kernel) low_36

def dom_38 : Nat := 0x3300330033003300
def goal_38 : Nat := 0x3200200032000000
def roots_38 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]

theorem low_38 : Lower dom_38 roots_38 goal_38 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37

def dom_39 : Nat := 0xcc00cc00cc00cc00
def goal_39 : Nat := 0xcc00c800cc008000
def roots_39 : List Nat := [0x8800880088008800, 0xc000c000c000c000, 0xcc000000cc000000, 0xcc00cc0000000000]

theorem low_39 : Lower dom_39 roots_39 goal_39 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_40 : Nat := 0xf000f000f000f00
def goal_40 : Nat := 0xe0008000e000000
def roots_40 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]

theorem low_40 : Lower dom_40 roots_40 goal_40 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_38

def dom_41 : Nat := 0xf000f000f000f000
def goal_41 : Nat := 0xf000e000f0008000
def roots_41 : List Nat := [0xa000a000a000a000, 0xc000c000c000c000, 0xf0000000f0000000, 0xf000f00000000000]

theorem low_41 : Lower dom_41 roots_41 goal_41 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

def dom_42 : Nat := 0xff00ff00ff00ff00
def goal_42 : Nat := 0xfe00e800fe008000
def roots_42 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

namespace S_42
def pairsG : List (Nat × Nat) := [(9, 25), (10, 26), (11, 15), (11, 27), (11, 43), (12, 28), (13, 15), (13, 29), (13, 45), (14, 15), (14, 30), (14, 46), (24, 25), (24, 26), (24, 28), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 10, 11, 11, 11, 12, 13, 13, 13, 14, 14, 14, 24, 24, 24, 41, 41, 41, 42, 42, 42, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [25, 26, 15, 27, 43, 28, 15, 29, 45, 15, 30, 46, 25, 26, 28, 43, 45, 57, 43, 46, 58, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_42.map (· &&& dom_42)
def goalM : Nat := goal_42 &&& dom_42
def NN : Nat → Nat
  | 5 => 3
  | 6 => 8
  | 7 => 4
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x78c300b8643102854984e49c
  | 6, 0 => 0xa579a9d6930a9c0c8ead530c70aaedde5c71ab0531b2d2051d03c94918406cf8
  | 7, 0 => 0x203fcfad1e8c6bf619f5616b06cd6aa0
  | 8, 0 => 0xd9129671
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00cc00cc00cc00c000c000c000c000aa00aa00aa00aa00a000a000a000a0008800880088008800550055005500550033003300330033000f000f000f000f00
  | 0, 1 => 0xff00ff0000000000ff000000ff000000fc00fc00fc00fc00fa00fa00fa00fa00f000f000f000f000ee00ee00ee00ee00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xdc2105dcb65260dca415
  | 6, 0, 0 => 0xdcb97527dc976527dc9752070dc753060dc875060dc7520600dcb65500dc7205
  | 7, 0, 0 => 0xdc97526dca9756dc975460dc9725
  | 8, 0, 0 => 0xdc9755
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 32
  | 7 => 28
  | 8 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x381c3c000380001c0ee80001c00000039ff1f88bf1f8f0f1ff01f
  | 0, 1 => 0x3ffc00070070001f81ffc38e3ff47007f001f8fdf
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x4b95cbc120391093c9ee82103c400904b9b61b08ad1a8d0b16b01b
  | 0, 1 => 0x3ffc48879274abdfbdffd7bf7ff674a7f237fbfdf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 27 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 27 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 2
  | 5 => 45
  | 6 => 120
  | 7 => 12
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xd91296711d03c949
  | 5, 0 => 0xd9129671d16c20d0c41dc3aca632ee029f26db3f94dd1a44785ae0006fe8bf236db98eb966ba42cc6079e3385b78636d5813e247574fb3c455f48467545fc207540b43034f19fb594a0700b544cff7103774626534185d4733ed21b8302d27862a5991a3284d4a5a27111e8a23f1463821e3e8e221964a89203fcfad1f946a1f1eb957cc1e8c6bf61d5694121d03c94919f5616b190105d016e5f65515f65d8906f63bea06cd6aa004af059c0380f4b10162be6d
  | 6, 0 => 0x405a87083bec846d3b0cc4653a3920b635a2162b345ebdde33ef45013356a829333d02b23115141c303c57f42fff6e4e2ef1088c2b6863c32a77cf472a6494fd286a853e28560c7a26519f572604ff9624d1834422b91f29227c42a921da65062117b20c203fcfad1fb02f271ed9dbff1e5bd6291df41f551d9395051aec58d119f5616b17948b21159e4e6714bf94441422af6f13e84a51131f8efc114105671070e68a0f513fc60ec32aba0ddc32aa0d7d88410d5d4c1e0ce1761b0ab670ff08ac3ed907df697106f63bea06324d890614470e059a1e4605666afd049ec4d10378e939035615c803242f6b02eb611a029a2f160274b5e900dbcda30034b3e0
  | 6, 1 => 0xd9129671b596b269a94df08fa572da3da0fdde18a0dbcfb29c66d38d9c445de698985b1595006dcc91027e8790e9c60890787e328ed193ee8cc02dca8c6b73fc8be173a7867828c086294d4b83713dfc826f7c138190c1f081447f867f911bcf7dca0de57afa1144765401a6716c071070274374686b25956539ed895f6f36f05cfbab5a5a94972758d8567158bd549158042f1956ca8861551e8539549412e35493c9e154414be652ff078152e0af2c52963e3450877aae504b960e4e49a4a14d92f1534c0fee764b8a48a24839fb3d44cff71044c99c024469ffdb4119551b
  | 7, 0 => 0xf4bf4b31d9129671bd718b95afee52caa2d382085ff904b84b88a90248992d773a17464a135e80ec0fa4afb40d66d9a7
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x21484200
  | 5, 0 => 0x2148420010440201104402000000000600006102204802000000000510440200214842000280220000000003104402002148420020480201214842000280620021484201000021002048020021484201000811002048020021484200000801000000000400000004000000050000000400002100204802000000000621484201
  | 5, 1 => 0x40000000600006102028022010000000300000003204802010000000700000004000000032048020121484201
  | 6, 0 => 0x801000000610100084100000411000000000100009101000061010000a10000006100000081010000000300000003000000070008110100000004000000010000000800000003000000040000a100000801000000610000000006000021010000000500006100000061010008110100000005000000030000000000006101
  | 6, 1 => 0x41101000021000000610100081100000801000000210100000007000401010000000400006100000841010000000800006101000000070000510000006101000021010000610100006100000061000000a1000008410000000006000411000000a10000002100000411010000a1000000a100000061010008110000002101
  | 6, 2 => 0xa10100080100000021010000a101000061000000000300085100000000030000a10100000000000811000000210000080101000000040008110000002100000401010008010000040100000811000000a10000080100000000020008010000084101000811010000a1000004110000000005000000060000000000002100
  | 6, 3 => 0x210000000003000811010008110100080101000801010000000400085100000021000008110100000007000000040000000300000007000801010000000300002100000841000000000100084100000051000000210000081100
  | 7, 0 => 0x1000000000000000000000001000000010000000100000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_34 roots_34 7 s ws hint
  | 1 => checkCutEntry dom_32 roots_32 7 s ws hint
  | 2 => checkCutEntry dom_35 roots_35 6 s ws hint
  | 3 => checkCutEntry dom_37 roots_37 5 s ws hint
  | 4 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 5 => checkCutEntry dom_38 roots_38 5 s ws hint
  | 6 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 7 => checkCutEntry dom_40 roots_40 5 s ws hint
  | 8 => checkCutEntry dom_41 roots_41 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_42 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_38 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_42 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_42 == dom_42) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_42 goalM u ys) : RunD dom_42 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_42 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := z7_0
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
  scr dom_42 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_42 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_42 roots_42 goal_42 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_42 goal_42 := by
    have h0 : isConstB dom_42 goal_42 = false := by decide +kernel
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

end S_42

theorem low_42 : Lower dom_42 roots_42 goal_42 9 := S_42.noCircuit

def dom_43 : Nat := 0xffff0000ffff0000
def goal_43 : Nat := 0xfee80000fe800000
def roots_43 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_43 : Lower dom_43 roots_43 goal_43 9 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42

def dom_44 : Nat := 0xffff0000
def goal_44 : Nat := 0xfe800000
def roots_44 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_44 : Lower dom_44 roots_44 goal_44 6 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35

def dom_45 : Nat := 0xcccccccc
def goal_45 : Nat := 0xcc808000
def roots_45 : List Nat := [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000]

theorem low_45 : Lower dom_45 roots_45 goal_45 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18

def dom_46 : Nat := 0xf0f0f0f0
def goal_46 : Nat := 0xf0808000
def roots_46 : List Nat := [0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000]

theorem low_46 : Lower dom_46 roots_46 goal_46 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45

def dom_47 : Nat := 0xffffffff
def goal_47 : Nat := 0xfe808000
def roots_47 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_47
def pairsG : List (Nat × Nat) := [(7, 15), (7, 23), (9, 25), (10, 26), (11, 15), (11, 27), (12, 28), (13, 15), (13, 29), (14, 15), (14, 30), (17, 25), (18, 26), (19, 23), (19, 27), (20, 28), (21, 23), (21, 29), (22, 23), (22, 30), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [7, 7, 9, 10, 11, 11, 12, 13, 13, 14, 14, 17, 18, 19, 19, 20, 21, 21, 22, 22, 24, 24, 24]
def r2sG : List Nat := [15, 23, 25, 26, 15, 27, 28, 15, 29, 15, 30, 25, 26, 23, 27, 28, 23, 29, 23, 30, 25, 26, 28]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 2 => 1
  | 3 => 7
  | 4 => 22
  | 5 => 64
  | 6 => 54
  | 7 => 8
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x46aa201
  | 3, 0 => 0x7d1c75c97cb0cd98707cdbac387751951a7a24cf11cb729f06b20658
  | 4, 0 => 0x5c5c9ccd547d6fec4f7214973e617cfd34a7f0131e6a4bea18adeadf15f5d6c914f01c8b13c9460e126aa854110a8c4b10e00a620e791a7c09738b040843a76f080f9179077086c607595a5b071a59b2063fd312014c0c3f
  | 5, 0 => 0xdf4911b2c305114eb67e85eaa254e4fa90b3b74b75611ce66568c27d5968176d57bfe6945415aa625383a22e4f67311047e1d63d475480bd46f054eb3fff87e43f0f42f83d768cd73b2e37d4385cc9e42a1576ce28d75ccc28b5b1fb285139ae2675a1cf25d2f9d4258be00f235ed6af20a5ef32203756df1f8c67e91ebffd381bdd97901b8accd61ae126f519f7eb2f1782da56144dd23712b3d679118433b61120bb090f0ed4fc0eeeaf850e4cd1600c242f8e0aedc22d09e8843009d43ae409c00d9a09aa0cfb097b66250797a04f075c367d06e9042405ac37af0510ad9e03f40bc303ccd9890364a72a033350e5029a86610232a61e0132efe50050d134
  | 6, 0 => 0xe0ea08deabd556e297ab739f90b3b74b7f95d5887aa2b5876d6ab4c46029e0ea5cc09c6d5ab570fb58e6f25c57661a9f52b9fb645081c56d4f6731104e0ae47e47e1d63d47dfadaf431deb01361a5168357eca043523d7dd32d3405c329985ba2fe39c9c2f96325f2c4f21532b00d0ed29bbdef9292bcfa32515df9722c1e95420bc0fdd202fbf561f436d281e561c0219ef57cd17aab85b16eb4bab15fb06b414e17f6b1463a74f116b7904105d54730e8cab400debe53a0d0dfe170aa4161f08088c370728aace0713412c03732ac503558ff102ee6cc5
  | 7, 0 => 0xd5d7a2ceb41bdfa3564c9356202fbf561f16380d1e29e5df14e17f6b0d59fc0a
  | 8, 0 => 0x1f16380d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x2a2a2a2a000000000f0f0f0f000000000ccccccc0000000003ff03ff0000000000ffffff0000000000ff00ff0000000000aaaaaa000000000000ffff
  | 0, 1 => 0x50f050f0000000003f3fffff000000003f3f3f3f00000000373737370000000033ffffff0000000033ff33ff0000000033333333000000003300ff00
  | 0, 2 => 0x808080800000000080800000000000007f7f7f7f0000000077777777000000007777000000000000666666660000000055ff55ff0000000055555555
  | 0, 3 => 0xa0a0000000000000a000a00000000000a0000000000000008f8f8f8f000000008c8c8c8c000000008888888800000000888800000000000088008800
  | 0, 4 => 0xaaaa000000000000aaa0a0a000000000aa88888800000000aa80808000000000aa00aa0000000000aa00000000000000a8a8000000000000a0a0a0a0
  | 0, 5 => 0xcc00cc0000000000cc00000000000000c0c0c0c000000000c0c0000000000000c000c00000000000bb33bb3300000000b3b3b3b300000000aaaaaaaa
  | 0, 6 => 0xee00ee0000000000ecececec00000000eac0eac000000000e0e0e0e000000000cfcfcfcf00000000cccccccc00000000cccc000000000000cc808080
  | 0, 7 => 0xf000000000000000eeeeeeee00000000eeeecccc00000000eeee000000000000eecceecc00000000eecccccc00000000eeaacc0000000000eeaaaaaa
  | 0, 8 => 0xfa00fa0000000000fa00000000000000f8f8f8f800000000f0f0f0f000000000f0f0000000000000f0a0a0a000000000f080808000000000f000f000
  | 0, 9 => 0xfc00fc0000000000fc00000000000000fafafafa00000000fafa000000000000faf0f0f000000000faaaf00000000000faaaaaaa00000000faa0a0a0
  | 0, 10 => 0xff88888800000000ff0f0f0f00000000ff00ff0000000000ff00000000000000fcfcfcfc00000000fcfc000000000000fcf0f0f000000000fcccf000
  | 0, 11 => 0xffff000000000000fff0f0f000000000ffcccccc00000000ffaaaaaa00000000ffa0a0a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1560bc3
  | 3, 0, 0 => 0xb9568a54b9566b04b1019274a9416a84b9564324b95e2374b91d7974
  | 4, 0, 0 => 0xb9568b864b56a4364996e55a0b542dc9ec91a05b1561b250b72acd625d6e59ab11d2d495119285b95223734b72ac450156e558af8badcab3d4175b95621a24b72ac46491405cab10925488bd4195
  | 4, 0, 1 => 0x2acc64c502dcab359295b95672d50b72bd588f96a4062b542dcaafd9265
  | 5, 0, 0 => 0xb9561b464a1ae559ac901e6b956a535aa1ae55a9099286b9566446469ae5488c95a86b9562325021ae5588c95286b9564c47ec9ae5588c91976b9562325031805cab350095ab121bc64a1805caaa0d865b9566b2405dae5580f96a86
  | 5, 0, 1 => 0xb956232502daa4486c9423601719100c096e5588c94046b95623964a1805588f8d005b956232503dae5588c94076b9560315aa1aad4a5119286b95623b4669ae559ac97a060172acc64816e5588f8d146b95623864bd805cab11f145
  | 5, 0, 2 => 0xb9566b66481aa4487019286b9562325085ae55a92d9286b956232504dae5588c94016b9562325039ae5488bd6a8601522324e8d6e5588c941d6b95623e5a81ae558d119286b9569a8345dae5588c941c60172ad3505d6e5588d59286
  | 5, 0, 3 => 0xb95eac464a1805caa404865b95623e3419ae5588c94166b956232505d804464401005b95aac464a1ad55a9118a86b95622e5aa1ae59ab119226b956236505d805caac88065b9562325035ae5588c94156b95623156a1ae5588ed4186
  | 6, 0, 0 => 0xb956a4464a11380b95623234418000b95623220a02ac464a048060172ac45ea04b00b956a325019ae5588c97a84ef72ac464a11917b956a4464a033dcab1192d58a1ee55a7119284ee02e55a51192860172a4464a11b00b9562284e25ae5588f59284ee02e5588c93a36
  | 6, 0, 1 => 0x1562325ea00300b9562315069805cab119283ed72ad388c9410701569c464a00300b9562282025805caacd9280cd72ac486c962870002e32501812dcab119284069ee5588c98a840e02e5588c941a6b95623262a0d3dcab1192f5ca1ee55890e03250f72ac464a08097
  | 6, 0, 2 => 0x172ac47cc90300b9562325089805cab1192814c02e5564a0d06601562325aa0035cab119283419c000b9569ad50b72dd5a91192870002e55644032dcab529c464a1c05cab119281ac02e557cc940660172ac468c9435cab1192f5041ee5588c96a82ef72ac588c941a7
  | 6, 0, 3 => 0x5cab1192806d72ac464a0d147b956a4464a01b80b956232505d800088c940200b72ad488c96a87
  | 7, 0, 0 => 0xb956a4464a1805588c94005b9562325019ae5588c941a60172ac464a16e5588c98a860172ac464416e5588f99286
  | 8, 0, 0 => 0x5cab119285
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 25
  | 3 => 32
  | 4 => 39
  | 5 => 46
  | 6 => 53
  | 7 => 46
  | 8 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x6d369c1e0f063b1dfff8071ffffe3fe00c1b4db8007ff
  | 0, 1 => 0x1f0c87cfffff9fcfe7399ccffffffffe71f9c4e27007fc
  | 0, 2 => 0x6000003ffffe7f9fccff30003c7e33fff25fc9648
  | 0, 3 => 0x600000006000000070783f00e0760180cc03000000030
  | 0, 4 => 0x6d0000c060c030198000030003680000001b000030183
  | 0, 5 => 0xc70000000603018c0000000c01ce27d39c4e38369b7
  | 0, 6 => 0xf783ddeec603db8f0783f8fc7e31d8ec63800000003
  | 0, 7 => 0x3dfefc7bf1d8f780018ef7e31d8ec1b71c0369b7
  | 0, 8 => 0xfe80000007f3f98f87c31f00000c060c000018007c0
  | 0, 9 => 0xff00000007f7fb8fe8001f0f860dbf001b4db830183
  | 0, 10 => 0xe0c067c1e0f3803fe7000001feff63fc0007c3e18c77c0
  | 0, 11 => 0x7ff800ff0f87f1d8ef9b4dbf30183
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x249248c160b12b95d9528060a452614800829149800291
  | 0, 1 => 0x9b4885cb6ff796cb672994caf57af5ea51a944a2528bd5
  | 0, 2 => 0xa452614800bd6eb67a9d4cf53a98e874336da25689448
  | 0, 3 => 0xe4204080e4410080357abf4ae576158acc2b0110042b1
  | 0, 4 => 0x2ed24c5daedcbb5db976bb724976a4924903b091072393
  | 0, 5 => 0x50ad72a150a0693498d2402100d234b2fd6bd5eb976bb7
  | 0, 6 => 0x74bf7abddeecfb7db8f27937afd7eb5daed6ba152d76bb
  | 0, 7 => 0x950a80fdfefdfbfdfbf7d2e7eff7efdfefdfbfdfbf7fbf
  | 0, 8 => 0xb59feb6b35927f3f9cfa7d39f4a853e9f4e7d3e9ca87d1
  | 0, 9 => 0xd5aff3ab55a2ff7fbdfed66bfdfef7fbfdeff7fbdfeff7
  | 0, 10 => 0xffffffeb75b3d6ffefadd6cdfeff7bfd5ab7fbfdeff7fb
  | 0, 11 => 0x7ffd6efffffffffffffffffffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 23 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 23 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 93 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 93 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 93 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 93 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 1
  | 3 => 10
  | 4 => 54
  | 5 => 129
  | 6 => 85
  | 7 => 3
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x56a2c07a
  | 3, 0 => 0x75a5febb555446552c51c539238d54fa1b7763ad1b68a915197aab0d09bdc74c0712d06c047f099f
  | 4, 0 => 0x899b611982155f4381c2b1a977756ab270e1439265cb0eeb566dcd9e55f208fb5554465552b9fb644c90cc8e49686fd743980a5243524ec241fe2dc3405775793b76083f3af23825382cbcdb364724a53628209134301c7630d7ec102df8dd882bedd0882b034b142b017e5a28d974fa23ecc35e1fdedf781f8c67e91f2e8eac1f16380d1cf440ea1897b7f61662e82a153a84d11485fcff14669044141bf90c125f69710dc002130c94a480087b1dd70660b5d705d870c304c76f2104ae9b11042af45701f6885101b535c9014288fb00551d150012c27b
  | 5, 0 => 0x1a048a061949af1519470f111943591217ad32821656d1d814e17f6b1495c9761477927812a81bdc129dfe4511c48365117fcf9b10e5309510d02a87107734ac0f9e18eb0f666dd70ef0e9720e3a9bb30d6be9a80d59fc0a0c7e7de50c6790470c5ebf740c3ac9150c364f570b05db300afd82840ad595070ad496f30a71277e0a5a15d809e20d56099e2858095bfb51090f691808d8769f08c7cfc108669b7e07c0faa8077a495006e8a7590626599c05e064d905c0402305920706058920430575e2490484ac0e044f3628043b779203d1223d02ed9b7902e3b84b0292e66d02929a92019ff3b8015176a90145c58200ec9e3600d726f000cab9cd00548321
  | 5, 1 => 0xd5d7a2ceb41bdfa3a3368cc49ce1902a9090b510902695cb776744b0731dd7b36d6ab4c466255012656abff26029e0ea5aa3dacd56832b8c564c9356538d037852b9fb64518b59705051f0284faf070a48fce799468606aa46359f6544f637be443d9fe3431deb01428d989c3f3e42403eaa30213d67fb903b2c091939ebd0ee37947c0335e7b92135a803f93523d1063430d5d8329985ba2fe39c9c2f1339232c56ab272bce8e692b25634e2b034b1429b82ef5297b3eeb28ae69ed2640cd66255006622515df9724ece7ba24133d5a23307e8221c99be520f514d6205f4d0c202fbf561fe940211f16380d1eae7a981e29e5df1cf440ea1c0da8881a6f1858
  | 5, 2 => 0xd9652b0a
  | 6, 0 => 0x472e25f7472264c643e31893439320594188c1e54043c9fd3fae35903f1826db3467e4ca33d80d6531c1c2362e71161b2c56ab27289999ce266c889d249ff5e02429127222fed1a021c99be5205f4d0c1fe940211f7d4f3f1f16380d1e69702e1e50a10f1e3bac671e29e5df1b8aa26a1b2ce8521b0173181a79258e19b88af7199f5f931949af15184e1a8e162a946a151f252713d00c0b13622b701288ee2a119c9bfc117fcf9b1070a54c0fec26080fdbc44b0e7383530d5df6510d59fc0a0c6da9dc0b13579c0afc43060a26f5fd0974d4bb090d6eb408211c8607d6cfc007c232ef070d327e0675769906257e5f045f366803254368002ac174001d64ce
  | 6, 1 => 0xd5d7a2cece52c4fab41bdfa3b331484eaacb8ff07f5bec7e7d2e058d7308fdf96f92c96d6add4a64636bbcda62f7203662446dd5618cfab15e5072d55dd68d6a5aa3dacd56832b8c564c9356532816c44f96a2a9
  | 7, 0 => 0xaacb8ff062f72036090d6eb4
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x4102
  | 3, 0 => 0x40102000401020004010200000001000401020004010300040104000401030000000100040104
  | 4, 0 => 0x244c0200000401020000000000040102000c41001044020000000000000000000004010300000001000000000000000300000000104402011044020002408201000000020000000300000001000000002148420100000001000000000000000200004104000000040000000121484200000000030000000200000003420c1200
  | 4, 1 => 0x40102000401020000000400000004000000020000000200040102000c01010004010221484200304c02000000000100040102000401020000410200000001424c02010000000100000000000000010000000200000000
  | 5, 0 => 0x3000c410100000003000c0100000000000000a100000000010000000010440201000c41000000000000000001000c810000000000000041010000a10000008100000000030004810000000003000051010000000000000000214842000000000200000003000000020000000200005100000041010000000400000002
  | 5, 1 => 0xc01010000000300040102000000020000410200040104000021000000e100000401020000e1010000000000000002000000020000610000085100000c810100000000000c0100000081001044020100000004000411000000000200000002000000000000610000004103000000021044020000000001000c01000000a100
  | 5, 2 => 0x300000001000c4100000401030000410100008101000000030000610100040101204802010004010200000004000000000000000300000002000061010000a100000c0101000000030000000100000002000000010000000200040100000000030000000000000000000c4100000000030000000100000000
  | 5, 3 => 0xe1000000000300000002000000020000e1000000000200084100000000020000000200000000000c010000085100000000010000a1000000000300000003000000000000000200000002000c91000008510000000001000000030000000200000002000000000000000000000002000841000000000300000004
  | 5, 4 => 0xe100
  | 6, 0 => 0x400000004000000010000000200000000000051000000000200000000000c410000000002000000000000000200002101000000020000000000000002000000030000610000040100000401000000a10000000000000c4100000061010008410100000002000000000000a10000084100000000020000000000000001
  | 6, 1 => 0x100085100000000000000a100000000000000a100000c0100000000030000000300000001000851010000e101000000030008510100000004000c41000000000300085100000000020000000200000003000000000000000000006100000000010000000300000001000c010000006101000000030000000200000001
  | 6, 2 => 0x10000e1000000000000000003000000000000e101000000020000000100000004000000010000a1000000000000000001000000020000000300000001000000040000000100084100
  | 7, 0 => 0x100000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_35 roots_35 6 s ws hint
  | 1 => checkCutEntry dom_44 roots_44 6 s ws hint
  | 2 => checkCutEntry dom_18 roots_18 5 s ws hint
  | 3 => checkCutEntry dom_45 roots_45 5 s ws hint
  | 4 => checkCutEntry dom_46 roots_46 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_44 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_46 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_47 == dom_47) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_47 goalM u ys) : RunD dom_47 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_47 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 7 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 7 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 7 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_16 : ∀ i, 16 ≤ i → i < 22 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 16 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 22 → Z 4 i = true := range_split z4_0 (range_split z4_8 (z4_16))
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
theorem z5 : ∀ i, 0 ≤ i → i < 64 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (z5_56)))))))
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
theorem z6_48 : ∀ i, 48 ≤ i → i < 54 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 48 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 54 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (z6_48))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := z7_0
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
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_47 goal_47 := by
    have h0 : isConstB dom_47 goal_47 = false := by decide +kernel
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

end S_47

theorem low_47 : Lower dom_47 roots_47 goal_47 9 := S_47.noCircuit

def dom_48 : Nat := 0x5555555555555555
def goal_48 : Nat := 0x5440400054000000
def roots_48 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_48 : Lower dom_48 roots_48 goal_48 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555555500000000, 14, 46)] (by decide +kernel) (by decide +kernel) low_28

def dom_49 : Nat := 0x3333333333333333
def goal_49 : Nat := 0x3220200032000000
def roots_49 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_49 : Lower dom_49 roots_49 goal_49 8 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48

def dom_50 : Nat := 0xf0f0f0f0f0f0f0f
def goal_50 : Nat := 0xe0808000e000000
def roots_50 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_50 : Lower dom_50 roots_50 goal_50 8 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49

def dom_51 : Nat := 0xffffffffffffffff
def goal_51 : Nat := 0xfee8e880fe808000
def roots_51 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_51
def pairsG : List (Nat × Nat) := [(7, 15), (7, 23), (7, 39), (9, 25), (10, 26), (11, 15), (11, 27), (11, 43), (12, 28), (13, 15), (13, 29), (13, 45), (14, 15), (14, 30), (14, 46), (17, 25), (18, 26), (19, 23), (19, 27), (19, 51), (20, 28), (21, 23), (21, 29), (21, 53), (22, 23), (22, 30), (22, 54), (24, 25), (24, 26), (24, 28), (35, 39), (35, 43), (35, 51), (37, 39), (37, 45), (37, 53), (38, 39), (38, 46), (38, 54), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [7, 7, 7, 9, 10, 11, 11, 11, 12, 13, 13, 13, 14, 14, 14, 17, 18, 19, 19, 19, 20, 21, 21, 21, 22, 22, 22, 24, 24, 24, 35, 35, 35, 37, 37, 37, 38, 38, 38, 41, 41, 41, 42, 42, 42, 44, 44, 44, 49, 49, 49, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [15, 23, 39, 25, 26, 15, 27, 43, 28, 15, 29, 45, 15, 30, 46, 25, 26, 23, 27, 51, 28, 23, 29, 53, 23, 30, 54, 25, 26, 28, 39, 43, 51, 39, 45, 53, 39, 46, 54, 43, 45, 57, 43, 46, 58, 45, 46, 60, 51, 53, 57, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
  | 6 => 6
  | 7 => 37
  | 8 => 55
  | 9 => 40
  | 10 => 19
  | 11 => 7
  | 12 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0x58e2d3934e68fb842007d4ba1e19212211281ffa0ca7348c
  | 7, 0 => 0xc9e68500b5cb2a3db37e378b6b43e4ab5fb507a55cc4b57b550d8d32524b5e0d502a61194b51391a465c6806440be00d416b8ee34012f5943fdc32763f3962eb3f154b353abb393f312e2e6f294f229c26f772222124acc4206038bf1fee78841fe8b9771d7d47a91a034a961955709717fb0e4f12fe3d0112189f7b07be2dee06e8cf4a06e793a206c19858026dee2600af7543
  | 8, 0 => 0xbf896989b785e4f5b71766f4b4dd74ceab6e0ec69eb917169c3e977483678b58826658c67b3832d66e4afe03674d56e462d7d48c62ac17cf5f3c4d2a5df52dc7569441a05571c5bc5081f7ed4b20f2674592bfd944380cd5419b127e405279ec401d09b83d6089e83c348841343aa3bd32fc7e7c3148b3b92f4d32572ab9d00429737e302840067726f83c73247ee72923494c871f8169a11d065bcb1ae066441aa8832215da453a157642e50f3ab4560f0b2f3a0efd143c0eb9f9960ced1cf50c443a61097f938304a66b8403c36990021b4903017c0eef002c6432
  | 9, 0 => 0xf6b5bc52c1438dfb9ced0d808cd89e4e8778745f765f42f57290796d70db175f5c8704475532c75f3a4736a733b8069c33036e7130cd9f642cba5f7d2ac5b924289b697326eb9842262bc017218408162161cccc1c8393441c014a3918917f9417bc20f015ef008612331bfe1182c6e9108dfb000fb89c5c0ee047db0debc18b097f4255080f2ac20694c235061b45cf03a0c62d02c871ac0229321f01805451
  | 10, 0 => 0xec58a0db7f1e4fa93cc117773bcc4b8e392a121934bd92e33092a0e22d6782ad2990644b28a5bcb421f40ce020bd10b41ae5543519b15e6818b98c200ecd7e060b8bbf6b07e6419702f5fddb
  | 11, 0 => 0xee12c54db03b1c5fa423463069904ec94e31041e448b58423e51fe3b
  | 12, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x11111155333333ff0f0f0f0f0f0f0f0f07070777070707770707070777777777030303330f0f0fff00ff00ff00ff00ff0000ffff0000ffff00000000ffffffff
  | 0, 1 => 0x3f3f3f003f3f3f003f3f3f000000000033333333333333331515153f1515153f151515153f3f3f3f131313ff5f5f5fff131313135f5f5f5f131313005f5f5f00
  | 0, 2 => 0x80808080808080807777777777777777777777007777770070707000707070005f5f5f5f5f5f5f5f5f5f5f005f5f5f0055555555555555553f3f3f3f3f3f3f3f
  | 0, 3 => 0xc0c0c0c0c0c0c0c0aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaa00aaaaaa00aaaa8080aaaa8080aa80aa80aa80aa80a0a0a0a0a0a0a0a08888888888888888
  | 0, 4 => 0xeaeaeaeac0c0c0c0eaeaeac0eaeaeac0eaeaeac000000000cccccccccccccccccccccccc00000000cccccc00cccccc00cc80cc80cc80cc80c8c8c888c0c0c000
  | 0, 5 => 0xf0f0f0f000000000f0f0f000f0f0f000eeeeeeccaaaaaa00eeeeeeaacccccc00ececececa0a0a0a0ecececa0ecececa0ecececa000000000ececec00a0a0a000
  | 0, 6 => 0xfcfcfcccf0f0f000fafafaaaf0f0f000f8f8f8f888888888f8f8f888f8f8f888f8f8f88800000000f8f8f80088888800f7f7f7f077777700f0f0f0f0f0f0f0f0
  | 0, 7 => 0xffff0000ffff0000ffecffecffa0ffa0ffeaffeaffc0ffc0ffc0ffc0ffc0ffc0ffa0ffa0ffa0ffa0ff88ff88ff88ff88ff15ff15ff3fff3fff00ff00ff00ff00
  | 0, 8 => 0xffffffff00000000ffffff00ffffff00fffff8f8ffff8888ffffececffffa0a0ffffeaeaffffc0c0ffffc0c0ffffc0c0ffffa0a0ffffa0a0ffff8888ffff8888
  | 0, 9 => 0xffffffff1515153f
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x23bf70c121e14e0088d0c0808067ee1825487863c77ee18b04879e43f70c121e18f1dfb86090f087
  | 7, 0, 0 => 0x8f15fb86090f0488efdc3564c121e88efdc30487878e800c121e26080807011dfb86090f0378efdc36609101e8011d82748781017011dfb86090f0578f11fbe70c121e88efddb86090f0980001f911a1810060090f180c0808078efdc30487cf0c88efdc305890f0788efdc305090f19800012110c080806
  | 7, 0, 1 => 0x11dfb8607890d700fdc346090f007011dfb85a90f067011d82422401017011dc30487848178efdc30488cf12800c121e2e08080700fdc3054a521e78efdc3466c121e800fdc1e383430078f19fb86090f0987ee18264a90f9e88efdcb86090f0b88efdc304c90f0c88efdc304878a94800fd81e26341007
  | 7, 0, 2 => 0x23911a1810160119fb822343007011d22322181017011dfb864c121e700fdc3048787807
  | 8, 0, 0 => 0x11e33f70911910d001fbc70c121f2202004784fdc304878d400011dfb860a921e700023bf70dd8243ce000477ee18243c49c00000c0f0d0404030084fd8243e781008011e1bf70c13a43d0023b860bd21e2c0600008efd82422401380011dfb86090f09700023b04878b0202e023c07e90f180c0a00007ee1824224003c78cfdc305e90f169
  | 8, 0, 1 => 0x11dc356090f18030023bf70c15243c660000011dc111a180b007ee18243e78d8088f19fb86ac121e312000007e78686040180008f19fb8223433808efdc304878c8980001fb0487c88200e023bf76e182b487a00007ee182e3c340380011dc24464430178efdeb8609d21f3d20213f78e18243c0200008ec179e1a080b808efdc305c90f168
  | 8, 0, 2 => 0x8f09fbc70c121e3b2000474878c060405c00000fdc111a1803008cfdc243c6030080119fb86090f1001001fb86090f9e380200008ee182b48780b8000023b022341016011e03f74e121e0d0023c67ee182b487a00477ee12223c7434008f19fb8607898d8000233f70c088d00e000477ee12222219c0477ec121f3c6c140000fd8243c581007
  | 8, 0, 3 => 0x476090f170405c00070c121e2e0403808efdc305690f0988efdc356090f180920233f70c121e2e020047609119e32080c0000c121e30080807
  | 9, 0, 0 => 0x23b04878c0202e000477ee181e2635c04770c12233c640c0000023b048441016000003f70c088d00c000386090f180201c0008ee18243c4c0b808f19fb860bd21180000038609088100c023bc70c121f3c0600008efdc1e3a3433c78cfdc30488cf1990119fb86090f18010023c67ee18243c4e00008efd824464413808efdc304884f198
  | 9, 0, 1 => 0x23c67ee0f0d0ce023c17eedc30487a00477ee18244678e40000fdc243c60300700023b86090f1702e023bf70c12223c6600007ee18243c400380011dfb860b9211700023b86078c8d02e023c67ee18243c5e003f76e18243c6404008efdc304e90f9e800023b04878e8202e023c67ee181e323600008efdc305690f38000023bf60446826
  | 9, 0, 2 => 0x477ee088d0cc000006090f020201a3bf74e182f4878c4808efdc304878e9080001fb86090f1c00e000467ee181e1a01c0477ee9c243c60340000fdc304878b807
  | 10, 0, 0 => 0x1fb8607868068f19fb860bd21e80001c3048780806011dfb86090f167011dfb0488cf0278efdc30487cf1d80119fb86090f00700023bf70786866011dfb04878c82700023b848783016011dfb86090f91700fdc304878c807011e33f7090f067011dfb8488cf0678efdd386090f188011dfb86090f1c7
  | 10, 0, 1 => 0x11dfb86090f1778f19fb86090f18800023b048781016
  | 11, 0, 0 => 0x7ee18243c01804770c121e02d1e33f70c121e7011dfb86090f3477ee18243c75e3bf70c121e30e023bf70c12116
  | 12, 0, 0 => 0x23bf70c121e6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 53
  | 7 => 60
  | 8 => 67
  | 9 => 67
  | 10 => 60
  | 11 => 53
  | 12 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc0e07038f08f0fe3f1f81f80f80f8e3f1ffe38018018e3f1f803ff1ff18e07038e380f80ff1ff007fc7ff8007000ffffc0007fff00000003fffffff
  | 0, 1 => 0xfffff8038ff8ff8fffff8000000000fc7e38e38f08f08ff8fc0ff8110110ff8fc0038ff8ff8fc7e3ffff1ff1fffc7e3803f1ff1f8fc7e3803f1ff1f8
  | 0, 2 => 0x7ffffffe3ff1ff18fffff803ff1ff181c0e00007f07f00ffffff1ff1ff1f8fffff803f1ff1f8ff8fc703f117110fffff8ff8ff8ff8
  | 0, 3 => 0x7007007007007038fc0ee8eef007038fc0000000007038000ee8ee8007000000ee8007000038000000eef000000e00e00e070000001c00e00e7
  | 0, 4 => 0x703ffc700700700703f007eefeef00703f0000000000381c71c70f70f70381c71c00000000381c00070f70f00001c00000070f70000001c7007000
  | 0, 5 => 0x1c0e07e000000001c0e00007f07f0003f1ff1c0ee8ee803f1f8fc70f70f00381c7fc0e00e070381c0e07ef7ef70381c0e000000000381c0000e00e00
  | 0, 6 => 0x1f8fc71c7f07f001c7e38fc7f07f001c0e07fc00e00e71c0e001c7fe7fe71c0e001c00000001c0e000000e00e0ffffffe3ff1ff181c0e07e07f07f07
  | 0, 7 => 0xfff00003fff8000e38fffff8e07fffe07ffffff007fffe00fff03f007fffe00ff8e38e07fffe00ff81f80e7fffff8ff8038fffff8e00ff8038007ff8
  | 0, 8 => 0xfffffffc0000000fffff803ffffff8fffe07fffff80e7fff1c7fffff8e07fff03fffffff007fff00703ffff007fff000e3fff8e07fff0001ffff80e7
  | 0, 9 => 0xffffffff8110110
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x90080002850850862d1681980d80d862412001801801862412003a51a5182040200180580580db005b45aa00060006db6c0005aa500000003b77b77b
  | 0, 1 => 0xf6fb78db8dd8dd8f6fb78d80880880b46a30c28d08d08d20900030110110d20900038558558b0482127a15a15cb0482003a15a158b0482003a15a158
  | 0, 2 => 0x1241221227ff6fb6c3ed1ed18ff6fb6c3ed1ed189d2e96c26d06d00fbddee1be1de1d8fbddee1be1de1d8db0d86036116110f6fb78db8dd8dd8
  | 0, 3 => 0x9048724722722724f279fc9ee9eef24f279fc088088424f278d89ee9eeb24f021b49ee966f2042796c9669eef042211e41e21e270090493c12e12e7
  | 0, 4 => 0x2df6fffc7aa7aa72df6fffcfeefeef2df6fffc48848844b95cf3d72f72f74b95cf3c40840844b95ce1972f72f34205cb2d32772f70994cf3c72a72a7
  | 0, 5 => 0x9d2e97e448048049d2e96c27f27f236ff7fffcdeedeef6ff7fffd7af7af74fb7dffc5ea5ea74fb7dffd7ef7ef74fb7dffc48848844fb7ded85ea5ea3
  | 0, 6 => 0xdfbfdffe7fa7fa7bdfefffe7fa7fa79dbedffc5ae5ae79dbedffe7fe7fe79dbedffc48848849dbeded85ae5ae3ff6fb7e7ed1ed1c9d2e97e67f27f27
  | 0, 7 => 0xfff92493fffa55afffffffffffffffffffffffffffffffb4fff6ff77fffff66ffbefbf7fffff2dffb7fb7ffffff24ffa4ba55fff9f24ffa4ba55fff9
  | 0, 8 => 0xfffffffc4884884fffffedbffffffbffffffffffffffffffffffffffffffffffffffffffffffffda7b7ffff77ffffb35f7fffbf7ffff96dbffffb7ff
  | 0, 9 => 0xffffffff4994994
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 60 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 60 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 73 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 73 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 73 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 73 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 2
  | 6 => 110
  | 7 => 775
  | 8 => 1530
  | 9 => 668
  | 10 => 142
  | 11 => 10
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x69904ec9294dc11b
  | 6, 0 => 0x233e20622288dcd92130c9e21f56b35e1f4a65881f0384251e4ee8231d9a85901cda02611c394d881bffe5ea1bba032819be657f192f816518fc467817243ef416c656ae16b51b0c161c501615ab19e1157642e514adfa2b1434812213ba083412cf85f6124ccdf611ccc03910ae2fee10804d220f5d4fbe0f3ab4560f0b2f3a0efd143c0e9911f30e2979ba0e2736e40e1e1be60dc803b50dc4fd410d878d7f0cfd2d230c22ae9c0b0f47fb0a68938809a6f5a70953df3209198d66090d9a3b08a9c56406659d3b0661c94305c20d3505985903052be44f04fc00db04b2361a04a66b8403e4be83030e58ba0241a5e40228068201fee19001799b510146ef3a
  | 6, 1 => 0xcbc796d6c553c30d9f7e9c4e82fd07698258853d8214533f7c8e4b127c0635f27b3832d671e705e16e44abc869904ec96408025a605be8f35f3c4d2a5e33e1a85b69d0d959ddfd5557960954540538174feb594a4e287dcf4d4a456b42595e283f6762873e9cc51a3e7735983d6089e83d004c543b6601ea3a969ea938af006435cd167d35a83b7d32fc7e7c32f07da42ff7e4202e2c43b62ae662c32a8f9b7b294dc11b29133c2028d0b9a8282e316026f05d85240a1788
  | 7, 0 => 0x44d5d65044a19b8043d15ac04209d2b04168bbd040a215c03d8f88903ae258a0396d90203894f8703876ef8035f94ef0350bde9032ee458031fe41d031fb596031aab46030fadaa02fee29302e35a9502e2cf3302d8606502c871ac02b2621402abe4de02a85d5e02979383029236b1027c5fc2026c1d6a026540140261e00f025cf5fc0229321f020f1fe9020f118f0204898801ccfcc701cac26b019bad4e0180545101799b5101665ea0016393e5015594650146a016013cdafb012da8060114dd0a01138b4400eddb9500c6f9fb009f8d0c0097b25e00909152008048790060f0340025776e0024bf16001fd2b7001528ba000d270c000552ec0004753c
  | 7, 1 => 0x8a214d6088046be08750522085305840823806808202fdc081c48db080b3b0e080292e107e9058f07d5953c07cdac3c07cb083b07bfb25107bc02ac07a6673f078d2e44075d5d09074d25fe073cce0b072bdfb90721757f06f9e0d606eaabe906ce11f406c77b680694c2350693b607068baf62067f98610672cd3906717074065360cf063e57f10620e04b0614be9f06107ac905d957f4057f12ab05749ba1056dadbd053f6b36052ea70b05233084051fc57f051baee0051a045704fef64804f6979a04f25c9004f0624004d9793504d1fa3604c8050004c218fe04b70e4c04b2361a04a9f28204a62d1a04967f3e046fa680046868f10462dc010452145d
  | 7, 2 => 0xe0a42640df787f50dec3c420dc93c5e0dc05ef50d943ba80d938d0b0d8e510c0d8c04060d45d33b0d42efca0d31246d0d1f33740d015e2d0ced83b60ced1cf50cd7214d0ccb89940cc59d920caf2c950c7632cd0c3937ba0c3210590bfe8fab0bdc717c0bd3bfe30bbf20220bbb80af0bb1bf460baf792b0baea7f80bae5f0a0badbde00b928aeb0b89a6490b7becc40b5d6d290b205dc60b1e0e150b13323e0b0677570af894000ad0b8980acd7e3b0a9b18170a93d8ea0a85532d0a7b21b40a2c39bb09f5607409a36368097f4255096f3ca2096ed48e0966cc96095168de0949888d09473c35092dc0b40914462a09134ba608fa00c508f29ab508e7736d
  | 7, 3 => 0x139487091384eb78138478191376e821136c9e03136674db135dad2f1358f0e61333a9ff13317d271309120c12f6184512ed765412ed0bd312e8524f12e1ee3d12dd636112d8963e12cb39d1128aa3681283c9ed1247ed0a124797511229424312186111120cc5d611dec15f11ccbda511a6e7fc1199326f118402221182c6e911635a70115b617a1151ec031133caa811183bea110fb92c10ae2fee108e7b26108dfb001083cb52107d8d39107b399a1055f4e0102513f81008b9700fddf9580fb89c5c0fb0cd810faeaf310fa9ebd30f90b2d80f84ab120f82b5ed0f500d480f378bc50eeadcc60ee047db0ed44eff0e8e94130e8db99a0e79b63e0e3e8b3d
  | 7, 4 => 0x1a7eb0581a707fbd1a5145881a0fe1f91a0b4a2f1a04127119f2677e19ed676819c71eb9199c1e14199761581968084c1932b2771925c43118fe582918f2f3be18b4e9fe18a9d32918a6931a18917f94188f9c9f1877b26c185374f418428353183db2121823c5831813dfc3180931c817fd680217f3ea9617bc20f017a7521917a467cd17a3fd8a179d33d1178690dd17863a811735e4441731363a1722ec0c16eb69f216e773511698dd41166408ba16440fea16307110160a634415ef008615dee7a015dcd5cb15d9171915d518eb15c5888815b26b3a157a0c7215466e63153a81ab151afbab14cd97a81425160113f040b213e6dc6a13e3f27a13d91c1b
  | 7, 5 => 0x22fa94f622e876dc22ae2cdf228d994b2274a471226d9e5f226a603022341d9e223331d12213668d2212ca5321dd5eb721d9c98d21c1443d21b7a350218781e0218408162161cccc215d54e02142691d21264a122102b3f420f9b42d2084b313207fc04620347cdc20087c111ffb45b01fee380e1fd910571fcb9c611f79759d1f63d20b1efd030b1e86a78c1e678d4e1e449cef1e18d0911e17ba0c1dee68aa1dbd53d81d9a85901d4a809a1d46b1f31d1b23831d109b321cacd5651c9080811c60c6e11c12ff661c014a391bdcc8361b8906561b8722501b7512a31b57e6571b38640a1b286c551b1e882d1b0210d31aeec9a91ae0b3da1aa992901a90a64e
  | 7, 6 => 0x2a536bde2a414a002a1373692a02b47829de97fe29c4c8d1299ba6dc298365f329657def294c69ad291862b628fb059228ef4b1928ec176228eab98b28da11e428cffce828b7dffc289b69732895085a28517e9d284bcb7728368cc52826a02a27d6184f27b4486127aa2da427a40957276cce0e275ee4fc272339c32709631b27027fe226eb984226e82a3126ceedb426b97f192696fdc32677e324264f4d2e263e9f43263e231225d8091925ba8e6025b63d7525a98b4625a2c03d25988b2c258d1fce254d06e0253b5831252f45e325174321250616ff24f4af5624c5e7ef2421da42241a876223d9a24d23ca962123b1c59e237897372362220922faef67
  | 7, 7 => 0x34e9af4034dc58ca3485af5c3463c98a34100b3133b8069c331a561133036e71330270b2330199fa32e96c7f32d3b93f32c6176132b44b48329820063267db4d322bdb4731d3df853187dd7e31433e5431326ae33105e5d63102392330f42dda30cd9f6430988cee305936de3058c3d5302a24be2f7541d82f4d32572f468e342f299ded2eebfd262eb748022e53d9512e51f60f2e41a7a62dbd649e2db0e2002d943db32d8597b52d7b2cfb2d71b0932d3c126e2cccdb662cba5f7d2c846c9c2c4ea21f2c4b233c2c4634082c37b19b2c30d6402c02f3282bfab3512bcc63da2b8503a52b78c8a62b5a9b192ac5b9242ab0c6b42aa93b642aa182692a90a8bc
  | 7, 8 => 0x42ae47e14274b34542410619423a84ef420ecb7341e4c5f041817900414d75384117f5ed41010dd24055e447401d09b83f910d993f39095b3eeb24f03ec1abad3eaff6353e7eacc43e7e4a6c3e7e1a983e279ced3e0a48ab3d2457473d0b205f3ce24ffb3c8555d23c32a9cc3c0c92b83bf8deb13b97bdba3b63a2f93b354e843b2f00ae3b29fd0f3a4736a73a3bf3ff3a12cb1139f1753739d8600a39b1f60d39772579396f503b3953a30f392a0c883924d04338ccc9f638ab17fe3892a392388c5d013886a28b386b3482385878a637fc42b137e2a73f37ca40ec375daa9f3725161336f3623136c497c63671c89d3589656d3582cf813580964f3506461f
  | 7, 9 => 0x575051b05743894555fb885855c03d395572da3a554d61895532c75f53f9c9a053e9723a53e3bb1253b7a098537291635364f0b8535368c052b23514529320d8525ff1c5522bfeac51b61c2c5147a09b50e6d3db4fcdcbc94f4004b14f1d65a94ee29f7f4e89d7f24dadc5d34d1916ed4cc77bb14ca7b7c44c7f526b4c6ec9ca4c052ea24b97652f4b9726c34af999624ad6f0ee4ac1c24e4ab7af434a31533c49e84a8449661549493f616c48b36d9d485b42eb477294e6473ba7db47030d1a46e22c26467a270f45f0649045e5719445de28764589367e45788fd1456741c944a433304420dd5a441ac3bd43680c3143636382433b59b6431d4bbc431cb093
  | 7, 10 => 0x72c06d1d71812023712ceca4711c65f170db175f70d632e570ba7cba7020fbc56f9e2f476e38966b6d97aeb66ccc2a0c6c10698c6b0eb39a6a96ab4a69dece0e69904ec96961104968cd5e9f68acce9467c3a660679108ac672aa2e0671fe9f86672b771660ea0b465744b4f64af859264039a7663d2150663c9a87f63692f766351308c631c9c4f62a77a4b621ef261618bb58b60efb630604f99fb6028997e5f9e50ac5f274ffe5f26aa5a5f092b4d5ef710bb5e959cd25e7dcfbc5e37e5975e0ff00e5d8915ad5d88ab225c8704475c1095f85bfe4a725bc970c35bbb25b25b3aabf35afffdb15ac2eae65a6cf1395a19f4b758939390583f2dfb57950560
  | 7, 11 => 0xc9fbc9ecc7c24aa3c779049fc1438dfbbdd6e7a4b87b99c9b71766f4b70034a2b6d68232b695ef65b2baa25bb14bbc95b13f8770afcad501aae12a43a96b0179a76e9a2fa66ecd80a65b1221a4b84506a2f17af1a198f551a1288b809fd647019f25d41899bcd29d946238e193b7994e92baeec8901b6b648de4e8d78da781618cd89e4e8bcbff4e8a48063c8946c7f88928e20888682a3687d7840d8778745f876ebd9686a31899868142a485094322824f568982058c4d7fc912067fc2e8ad7ebdaa097d7c6b0c7c879f237a5e30277a07f55e79c41dbd795fd1bf77f3814f77044bd7767474a4765f42f5741b6e6173d72cc973d05ad073c023b4737413a7
  | 7, 12 => 0xfad718e0f6b5bc52e8f2fd56e7e88bf0d3fec4fad113b182d057e820
  | 8, 0 => 0x1f22d0e01e6a1bb01e5cafa01db726b01da1e4601cfa26a01ca4cd701bd77e901b0755501acf8e301a9e2b101a7e61201a3f671019f2f3301940380018678aa017eef750176e1970173ad6301717a070151ca560151a4300146552701423723013f028301352bc901229e660121f500011e3bf30114dd0a0106cd5f010424a70103e9ca00ef9c6300df80cb00d0447400cef0b400bece0000bd953400bd19b700a39a3a00a1ff8e00a01007009c53f40096090f0095699f008b729600885c120081971b007bdb1b00789a2f00780d7c00763d640046f4700046056b003404750033a68300325d9b002ad87a002a4f5c0028338b001141d0000eaebe00004f32
  | 8, 1 => 0x46d920204606a38045074ed04459d820444a6640439f2f30434a0ea042b810404174029041662e3040ce1ad040a9f000403da7f04007e3403fa26ba03e4b2b403d561a903cfe5a403afd31303ae112a03a46b1d03a0362203940aa0037e293e037d62de037b3dd9035d52020346fe36033ff4970338cf1e0338135903268d7403079ec602fed06a02f5fddb02f2b1e002ed76e002e53e0d02e1a3fb02e126fc02d2c26602cff0b602cf2cce02cec7d702ce9da702bfd9a802bddd4902b3992502a7019a02a10e3402979383029769f202823732027328db0246c2bc023b3ae502290be2022134b3021cd9e402149ad802144588020f64f70208e20602041133
  | 8, 2 => 0x624bd6b061ed51c061ea936061c26ad061a83e90601330605fcea2e05f0dba005eb793805e4d78805e4721b05dce1a805d0f88805cc69d505cc0b3305b98e1f05b183ef05ab6a7705a9f63905a874ad059ed3fb058fc924058f4ed60576c3ef056cb4e7056ca1d4056b97fe05690dc505627d30055cda6d054d388f0541a0c40538a9bb05382eed05374572052d470905251a90052476240523056e05177308050b9f55050b919304ffb30104f980a704f3f77104ec377d04e8d1a104e7d36f04d871c304be7a3504b54e9604b0fd510497638504944d530493c1d6048be5e1048b475b04891cff048544d704822ea50477114904770209046f0a71046e078c
  | 8, 3 => 0x8551b9c08516a5c084b0a8508498fe90841e830083bcadf0837268908359101083248320819bfaa080ec1cc080434b507f8990907e6419707e5cf3407e32f0f07cf77a007cb083b07c55d3007c51de307bac0d607b78b0a07b568f607b1884d07a69e13078bee1e07884ea607852a5a076036190749ab980740ac70073c9449072b303d07095bfa06f6ef3b06e0c14b06daf14806da6c1106d6015306cd9a4f06cbae1206cb296406c6224c06c4fec206be4b1006bd551306a3f4ad06a2dfce06a2b65306a0f4940692c5e2068c1c7d068802d10683a3ec067b6c8f065ae9c7064d0dae06466c4d063f37340633f646063019cb062febf9062d999906251951
  | 8, 4 => 0xb1307820b0f36df0b04cedd0b02a1120afec7860af54bf50ae91d430ae4ab900ae24fa20ad2223b0abcc9d50aa9d0830a9b3b1e0a9b18170a8bd0fa0a898cfb0a8770020a79332a0a552a4d0a3ed7240a205e780a16541c0a12b5ea0a117d030a078ade0a04d30b09ffa6ea09f3895e09f0111c09e9c6ca09e5416609cffb3809a06ddc099a9ce8098de5f30988e02f0975719b09710dd909682695094d4c840942ef37093b128d0933fc8d092622fa092579940921f9d709191c2c0905ab9e08fc24db08f483a508caee4908c5f74508bac8dc08b0f44b08a3949b089cd19d089c65ca089bf8d50895d51908906eda088e5cf0087c1ec30879b60e0869642c
  | 8, 5 => 0xdc9af900dc235ca0dbf34c50daeef0b0d9ad5280d74c8420d71a7330d69a2720d61cb110d4949790d3ea4a40d3c45160d397bd50d2a87680d26a7210d25d4e60d2191950d1f3f1d0d113b180cf077640cebdcd30cc035fc0cbe91130cbd5afe0cb8c39e0cb66bd50c971b3b0c6946000c6733db0c5fdc3d0c5b3b3e0c5a17430c4dbd8f0c4060750c35c73f0c2e0a0f0c1e318f0c1958900c0ae2cf0c0600430bfbc8ff0bee9f6c0bec9aa90be9cd190bdd8f930bd396390bcd40800bbb73db0bb824020bad3a7b0ba2eedf0b8c4d970b8bbf6b0b8647380b70a6c50b660ede0b5d6d290b585b130b5046a30b4d45a70b49aa330b3583b10b2d51780b15f32b
  | 8, 6 => 0xfc4f2070fc23a360fba516e0fb8ed8a0fa57e840fa561610f90509e0f8d993f0f83ef000f83e8f40f727ac10f5f76150f5e6ffd0f5de2c80f5566ed0f52c2bb0f52863c0f4db85f0f2f9cfe0f25226c0f19e5e70f08e6190f0006720efde4030ef63af90ef288480ee159480ed6929f0ed415db0ed1bb5b0ecd7e060ec197190ebceea70e9afe650e94e7d20e924b740e867e820e783b7b0e6f12fc0e6d80fd0e6ba2390e67c7c90e6708e80e6183940e614da40e60d5540e44916e0e31e3900e222dca0e1ef3e40e1cbd250e1732840e16a80c0e019f710dfe77ea0de567dc0ddba98a0dda46ca0dd676590dd54e180dd0fc390dcfee690dcbb51f0dca95b0
  | 8, 7 => 0x122c8bf41228e9d3121dd3651216e99a120f986d1206ecb91200645411fae06a11f546a611f0b41c11e8c5fa11e0ef6f11dda1b911d7b90211d1dd4e11ad3b2b119b0a151199326f1196fe39118f7b38115b14d211507abd1141c4f9113d8a7a1130aa13112306cc111e0597111ba9a9111954a1111576081103f46510ffa99e10fea14b10dd02a310d62d0c10d4721e10d223a510cc8a5810c2a4cb10a3bc10109959ad109246a910805d63107d3aa21079d4241076fc2610512a7b104c771910391595102deff5101d443e10133dd410117ec0101066f0100d7e8d1007396e0ffe55e60ffdd88b0fee49d00fe9bf0e0fe4a9ab0fe0a6cf0fcced760fcc996e
  | 8, 8 => 0x153abc241539a3fb15199b671519779d1507919e14ef616714d2fd5414cb3d6014c82f1914abecbb149ec8f614923958149069be14874938143af97814314de41423a57b1421fcdf1419d199140e6763140b8a8113fe6f7713ef499c13ee599a13e1a76713d2b7fc13d22f4a13c223a313b0bf0f13a8b69513990c881398e9331392e9161372d5dc1371cc45136993721366f74613617fb5135f532b135c88a31358002f1352f30c1350acae1330f289132898f0131a11631312a63112f4c8cc12e5d43612e3c77d12de921a12cb39d112bdbb8b12b24a9612ada0fa12a746b2129fd900129b6dc5127cb7be126017fc125d83591259e1741249d9ee1239c0cf
  | 8, 9 => 0x185eb5301854efdd18344a901823571d182006ed181b113e1816c2681814059d18114e1518097fbf18060e7817d33a8817c4f40b17c40d9617bc587817baec6917bac50e17b26bb417903f4f177fee50177de50d1776e4811771b41c176754891764813817429bba173d6d071728a70017245d7217212a5e171d0b311715f72f17057e0516ff67ae16de637d16c189fe16b0562d16a13f01169e9000169c51ea1695a5f41673979d166e2ec0166459e81663431a1650bf3a164bea57160f40e9160a8a2116041f3415e86ad815d4993215d0529715c5888815c0d50b15a387f4159a9bdb157b7f6a156e54b91563160e155e7c73155843ce154e52f415424020
  | 8, 10 => 0x1af41e671aec51911ae6575b1ae554351ad451d81acd36241ac823261ac3b1731ac35e671ab2d4941aace10f1aa35d941a8ea3051a7eb0581a7a1dfa1a63cc721a5cc8ca1a49b9bf1a37c79e1a200f2a1a1c192c1a1bf9471a0d40c91a0a201f19fc902d19f8bca819f25ddd19f1642319e8d26819e6d1cc19db3d9619da2b5119d561e219d4f96119cb199c19bd6beb19b4121e19b15e6819a4c68719927ea4198298e61974011419711c9f19677fee196446eb194885a419460cd6193db6031939cf201938eecc192f65af192c1cd81928d946190f5f7c18f9181e18eeb33318e8556f18e0b43918d2486d18b98c201897d6aa1877b26c18618e52185fc2c7
  | 8, 11 => 0x1ee7ebfc1ed591ba1ec8e6d31e72b2f11e716dd71e6f046d1e6c822a1e4f6eeb1e3d503d1e36e9ac1e0e98ca1df1bcc41de0a5541dddfcd91dd7f8d41dd265681dc984b31db37a491d7800521d7449191d6a18ff1d6924011d5d2f441d599b281d2042cd1d1881b81d109b321d0017961cfcf8381cf2c54e1ce751511cd62c421cc2bd091cc0b18d1cb7ea711cb684461caeb9c21c91aa531c7953841c60ca231c527bd21c4c8bdd1c4a3cba1c318fe01c2d13cf1bf87cfe1be8feeb1bcda54f1bc56e4c1bc3e3c51bc018291bb586041bb46c881b9c70151b8722501b73df081b69c07e1b699dc91b6504491b2ebe8a1b294a421afe703f1afa4bc01af79ecc
  | 8, 12 => 0x2253d0be225191b5224ede7c224d3e532245fe9c2227e0bb2220717d220fdcb4220200fe21f40ce021f2fc4c21df6a3721ca5fbd21c7acda21c1dfdf21be0de221a31a85219355992184081621806f822176041c21694b3d215817902128ca9f211fb1622118d8ca210ce7fa21033b4a20fdae3920eb6e0920bd10b420baab0320b3ef5520aa0f8720a9e85d20a11aac209c72bc20957acc2063475b205bd6d3205a473a2050c6112010c883200a488f2007274220071fcb2003e9701ff874121fef2a9d1feea6f71fe1657b1fd528dc1fb657f21faa76a61fa2c33b1fa0c5251f63d31e1f4aeabc1f414c731f40e9e01f3375f01f1d22bb1ef4a9511eef4e36
  | 8, 13 => 0x276f815f27201259270bbaa12701a80f2696fdc326749ef926381aeb2633ef5b261dbc4e260b9df02601391125ce262425cd094725c45e9b255f8228255a854d25531ace2547bfba253a83882511d18a25097dfb25002b9e24fa98e924fa194c24d855ab24b28a9424afe76c24af4e9124952ee7247379cc247043b32467843d243ecfec24283120241de4a723fc0e4423f119b423d6ecf523b4b32323ab50d123a062fe239d8b002398fcea236db0912361347d2352be9f234db0492344d9e92314ed322311f3a82306194b22fdb84222fa0b9422cfe1e622cf57f622c8689022c82c5c22b6592822b5307822aa41782293edd2227f35cf2271e240226d9e5f
  | 8, 14 => 0x2b48c6612b22931c2b18233c2b0dcf422af29d222ae835682ae1fb0e2ace0f242ac55d3e2ac469022a9c2ebd2a9b77792a7804b32a65c0562a2d79e42a2b654f2a1d179529f9e5a329e805bf29d216b729bf43fd29b8fa2329b2efba299d3f17299cf06329930a1e299242992990644b298f581d2975adf629741ed729718487294f02e5293a67af292b01692925454d29232b6b292201282904a04828ff1d4128f361b128d08b7a28cc582d28c3889128be392528a5bcb428a5553b288639ed2884a5c12871b50b28703db7285fd478283f4796283f1a732815cd23280e32f92807d94a27ffe0e227ece12127c6f11f27b9c98927b8c83227a449b927872db9
  | 8, 15 => 0x3092a0e23092400b308466a1307355153059b19830597e413058c3d530531e15304cf6a43043a4a13040074f303d46d6302ed8ef300d5f522fe99f072fd779f52fa951ec2f68e8a32f5b7e532f54b3712f4dd31e2f4467822f3b54bc2f00241f2eff46822ed32d7c2ece18e22ec5bf862e759f622e6458d32e15ef8f2e0f22842e06f51e2df8cd942de9bf942de4fc572ddded582dd157bc2daa6df82d9392982d6f387f2d6782ad2d41da852d2c15442d2ac0592d15561e2cf1a8762cc946112cc051b32ca9ec202c8b435e2c3aca532c3a93182c110e282bf147822bcee1e02ba3e7922b92ccbf2b8ccc292b76b4262b753d762b55af952b4cd11b2b4b4c1f
  | 8, 16 => 0x365bf4c43653b4f235fa4aaa35d4dc5035a5ce78358cab363582a2fb358115493574aec33573af463572873e356a8a493566f7473562aba0355d5682353e880b35271afb34f52d0a34e883de34e2300e34dd0a0834d18de534bd92e334674d32343851533434acc63420ff21340650a233d19fb833afebd5339bce7f33992ceb337bd554337ab58033760ffb336eb5d3335f87d5335a99693356c35a334d125a33055be032de943f32bc58e7328fec2c32844849327bd0073269ec703242634731f50c8031dce4e931dcc7cf31d9ecb331d9b83431ab793631a6cea631a074f73187a3a63182c7a4317d72253133f61b313345aa30f32a0b30eaf43230a6ec81
  | 8, 17 => 0x3d1bfbc63cc117773cb176443c721b363c5b82823c32269a3c298dbc3bea25e23bcde4e53bcc4b8e3bc9cd9f3bc6ecd63bb1335a3b73d6d93b6a32d53b6979553b4709fe3b3996b63b19e1813b0ea83a3b019a9b3aecd5253ac1b6963ac1067b3aba19c33a98d5e73a82270b3a7a63cf3a32b4d83a19419439f8911439ebfa2839e8541939d00cef39bf552039bb2775399e82a1397914de3961d837393d4784392a121939039eca3902314e3900cfa438f9f1d038830db23870d6553847afd3382ffa4f3817939b37ef2e6537cd6df437c0fdad379438ff379303b73785298a37820dc0376c9fb137514c553724cdef36dd8d1a36d7425636d19d7636808d8e
  | 8, 18 => 0x44b29a3644b0e6f244ae328044a7b9c244a2c5eb44475b41442cbecc441ea67b44059a0943fa8d3b437b5e634350aa5c433e9d7d430950b842dd918542631f4b4262e7c3425b7f94423458f44201593441fc611e41fbe10a41d72dcf41b6c4f841a0fa6b4173b35941700a9c4166c3f2412cb67740fa063d40e8793840baaef240ae2c6240a99c8b40a4f8494095c759405dfd4f405757d3403969de4009bb563fc0623a3fb26ee53f9b2f6f3f983e9f3f93ab833f88ae1e3f1eda923f1c14663ef29a593e9d96673e8de1f73e7e1a983e78f79b3e5e758c3e513ee93e2ec35d3e268d7f3dc5f5ba3dc1f0163db737d53d91f2f73d7651fc3d736b543d707eb3
  | 8, 19 => 0x4f31c05d4f23828d4f2361254ec4454b4e89cca24e7b64fe4e4c2f234e4b188d4e2a579f4d85e03f4d602a7e4d181a1b4ce6af274c2c29d64c1e5f1b4c1021324c08939f4bd620d84bc92bc54ba23e9e4b49ee814b15b0ae4afdaebf4af00fdc4ab7c62b4ab295c04a5efec54a4b93c34a2de168498957a8497e066349581ac149492bb94948b297491b352548f4399848d4d5f248c1d38148a3f7e7489496d848836d65486ea0f148621395479918ac477294e64709a38b4695700546841908461e573045d4bf9245d041f745c410af459cc6d1459ae53a459822e9457c14aa4579e640456f70154538033f45361a9f4530b80c4515bf0a44fce15344ce72c1
  | 8, 20 => 0x5e81b8755e66fe545ddec8b95da206915d62d94d5d3818cc5d2b734f5d1812cd5d0983375cc3ab4a5cafe6825c6758515bcbc3095b6292535b5bdb505ad90ed25a42a1135a21b51c5a0ce74b59fa16fc59d025ec59a6eaf258fbb52c58bf80d858bc3c2857bacd2d57995332574baa025720333356febec556e73c9256c8b64956c811d4568acc32564a59e4562dfe4a560bad1d55a12dd754c326a9548aba3b546d22b8542e432f540efb84540bc4af540362e7539fd903537cc0655364f0b8532cafce532ace1152d74f5f522563f351e6c6fa5183488851784bd1515b58eb514fabd55147a09b512027a5503e0580502e4e0d4fb062e34f5951674f4abc24
  | 8, 21 => 0x6e602b5a6de73a326d9665d86d2aa1716c66291e6b7fab696a860ad36a21a6f669f7a2f069ce4c2369931b8669904ec96959e9e46958b6ed69548d246922f50d68d15f9f68cd5e9f687f2e806873735f681ed83067d56b0567d3a7c767c3a66067668b2b673c0e5e66d60e4866ae674b6678a9e06678445e65c41b2065a5cd59657e37b6655854a5653ca82f64fefd4864cfe5616451e42c63c9a87f63c4ff3f635e23ba633ede3d63294e3d6301ab4462547817620384ba61a6b7ec612a678d611db01a60c6b07360802f78606feecb606e75936065faab60509c6c60424d8c602ba2465fb7af325fb0448b5f83829a5f4e5bbf5ef8db2e5eef258e5ea3365d
  | 8, 22 => 0x936521e19352783f92a979ba9147cf849126f78a902efa188e61a5b48d04eef68cfb3eea8c7e98c08c6994df8c23d8118ba6594988ee9c2985be4fed8583074384641f1f842300ed83fdd03a8314455582e7bf6f80421e698025b7407f1e4fa97ed85d0d7e8d37267e8725a57e55e9e17e2a22da7d7a68967d6b54717d0674347c8e4b127c6ffe687c2c68957b770fcc7b71fe537b364ce67b2570917aa675b57a26363079b1d1f97979d1167965429579611b02795b686a7895f96177e14d757791451176cfac407656bb6a7654a25c74a51e837339649d71f5f7d371629267711c65f17031c60a6ffe957c6ffe882a6fe6f0756f59144b6eb3f6886e8efcbd
  | 8, 23 => 0xf91cf46ef7f82693ec58a0dbe939dbf0e5961885e278969dde95e1dfde667a90dce4cd74db1676a7d9fb5938d4ffcf19d3fec4fad00efd4dcef33765ca158110c9a1a983c5183dddbd967785bd652f2cb8e8e148b66d9a2bb6442766b409e67db379cc2db219ddfcb0e799c3aeca1606ae7b8c5badc8338cad559489ab9c71ddab0a06c6a7bbe32da6e26bf9a4c9f329a46341c8a1559295a12049b9a083c0bd9f91f4af9ec99c4b9ec1e62d9eb63d339d74c4a49d3ecdb99c94dcb99b0fa6c29a8473029a1dcd2a97f9db109753a73597452ec1973bd9da96d5172795b424c895a3d65f94b4ac83
  | 9, 0 => 0x540b9d705326a00052f7b1e05266fc405053a2104d1fa3604a4109904a0211b046cf47e046268ba0438eafe043100bc041cbc3104184089040a9f0003ec275c03cbc32103afd0810369bd56035236190331cac603289afe02f2770602e35a9502db817802d9ded002d338cd02d180c602c9fd1402a6a579025fe3ce023eae8e022c52e3021705eb0204dd0b01fdc1b601e6a1bb01e616e201dfe0b301dd9b2901d8e54001c2557f019f51af019da6bb016f95e1015f4010010abf0a01056b7e00feba3800fe92c500df80cb00dd9c4400dcfa1700d64fc300b2161b00a39a3a009df599004241140027225c0025265100184f2a001528ba0010041b000bf75c
  | 9, 1 => 0xacd7e3b0ab08b550aaa02f00a5db90d0a36a06a0a3643350a01adfb09e7ecf009dee908096de79a092f2395092cbb7208c04d1d08bacf3c08a9ee4a08a5f7220895d5190882787208753c20086df8bb084e2610083591010819bfaa0814753607fcf0cb07ebb2c207e5cf3407c8882d07a1618d07989a1707983db6077f8a09076f5fa0076e26240750f592073325e0071ebcc606f2dd2206eac70a06d96cf306d1977a06d133fa069646980674bcee064e82c1062f44460624bd6b0620bd3c0614be9f0608b07505dce1a805cb05e805cac2fa05b2eac505b06fd605ab6a77057ddb480573298d056af0ba05682faf0563738e055dc609055450540543a4be
  | 9, 2 => 0x11c7a2ff11c11f5211a300cc1194d57e115b7aed1157b634113e45f3111803fb10e35cf710d62d0c109e2fc9109959ad10873aff10391595103235ff101d443e0ffdd88b0ff42e9d0fb3dfc60f9f8c4e0f5e8c8c0f232de10f20292d0f02d3df0ef660410ef288480ee348510edf2cdc0ed4fd100ebbd2790e4468b30e41de8b0dfe77ea0de050250ddba98a0dcf1c2e0daeef0b0da4ff430d876c100d5895510d4867920d4672090d228ef00d04b1d80cae16f50ca210370c7f8aac0c6b19620c5a17430c5381690c1036b40bf2010f0bed0ab30bdb57510bb355150bb29b970bac83940ba44ac10b8daa5b0b7e911c0b7121650b56b48e0b2edb290b2a0c8d
  | 9, 3 => 0x18b9e6661883febb187d4fd5184cfe9e184457f818103acb1803566017d58bc317bc30be17b4b8c1176707ad1723ed0716ff67ae16f738fb16f1ab3316ee128f16c75507169f5cd9169aa41c16926b4916902152168d303e1682538b16731ac11653c2d11621c450161b60761607f95a15ffc31f15ff488d15ddbb14159b56a61597e693157b7f6a156a35c4155f598915522f70154fa4221549f69d15335637151d3ae11519779d14f16ab514dd730214c61bf814b7c4bd14a41e26149a4ea1149974cf14897246143425e613f1229313a9dd36139ab4031350acae131968a612c9af9612ac746a1288b0461253b7c01208380211db7c4611d1dd4e11c9fc59
  | 9, 4 => 0x21a9023c213511102118d8ca210a2d14210940e420e5768320d1d0a420b14afe2097f466207b9112206d00e32026c16f200a488f1fe552091fd910571fc1b3651fa5f1db1f993d9e1f904b671f3d926f1f2e3b111edce4091ecb5d701ecad99b1e85d81f1e2098c81e0bbdd21e0058df1dcac76e1da313771d9a85901d64beba1d1a31a91d0194d31cd564d81c6862e81c54452b1c3fa0d71c0377111c02e4e51b9b06e31b77905d1b4bb61e1b17d95e1ae859541ae777391adb9ef91ad3a8a81a70570a1a2977e91a0a201f19ed676819d561e219c5213519adfb64198f74181941d4a919410728192698ce191c8807190ce19c18ecccb418e8556f18e6b268
  | 9, 5 => 0x290449ee2900d54528f114c028d0b9a828b7dffc28abaeea286eb3dd285e1f4628584ecd2843c9bb27ece12127a9766f27872db9274baa6c2749b15f274942202732e0e42726dd472706a8f026f92c792633c00426091b2e25f87f7325eb792125e2ffac25d362f6255a854d252f45e324effd7f24d5ba0324ac972f2481448224719ba5245d7b2224565eaf241d9716241a138724103ef62403d16a23f7bb1523b76dde23b0b50723a9d9a723a8da94239e18c1239c1d2c2386e49723451615233cdd422305e8be22e06b9022d366d722aa417822a8b57922a14111228c6789223aaa652229aa972220717d22033f5821f5914321d460ea21be0de221ae3ee4
  | 9, 6 => 0x36703f253651581035db2393356270d23553f90e3545db6c348ee9a334647388342f298b3420ff2133cd33f333c0d8fd337098c0334d125a32c69f34328d71a532426347323281b131cfb7f130f8cef630b0d687308f3f3f302a880b302a47402ff39f242f9ebac62f5b7e532f54b3712ef7279f2ef590472e52e3d72e2f44ab2dad3e8d2d9cc4ae2d6f387f2d43c49d2d3286802d0180522ceec5e32cafca952c4da73d2c4293e02c2bd16b2c21ef762c211baa2c1be5ab2bbcc4f62b67531d2b2be4192b0409f22ac55d3e2abf74ef2a82d1cf2a7bd5d22a71ab6e2a49769a2a2d79e42a20277c29f0ed3929b8fa2329aaf2102999a99b297c07d0292e053d
  | 9, 7 => 0x45f064904579e6404507e72f44e3171544af6d2d448b58424426eea9435e219c42f0c3f0427c5296421821c141588a44412582f04095c759406e45224045e22c3f2caa283f1a4e9b3ece239b3ec3f8233eadf8b13e5eba883e51fe3b3e19f81b3e0301fa3d88f5423d78115d3d6e78df3cd54ec73c7bdb083c5cbaaf3c53c6963bf169913bc59d713bc01a9d3b6df4fd3b30ed003b22fa393b0efdce3ae3cf123ac23f8e3a6372fa3a5836753a1fbb533a1ccc743a12271c397444d93924d04338f9f1d038e5f050388ab4cd387cf532385d7536385a6a0f38447f61382d8f7737d56bc9371be0213705e32a36e13f6d36d8325c36cf9b0036c8994636c497c6
  | 9, 8 => 0x5e2f14935d49c6ef5d49b83f5d0095c65cc5f4345c6758515c421fc05c31fa665b212d615b10def85a7dafd65a79a54a5a5fdbb45a31c0285917f13a58d22a7a588c4ea758543af7578d6fff56d3218456940023564c1fd0562dfe4a55f4986a54c3312b53fc1e2653e05ed2539e25065374b37f5271f78f5184a29a517002db510297345101dffc50e0ace45047ce89502addfa500ac4ec4fbb3e634fb062e34ee29ddf4ea0d3994e8abe644e50a07a4e31041e4e1ede624d6cf8004d2f029c4c9ad3b34bd620d84b81dc034b6d53844b1d854f49f183f349d127b849a0cb71495faea7491b352548c75f9b485e935b47db5ef94712821346da15bd465f78f8
  | 9, 9 => 0x950c9cb194603ffe92ddd80692baeec8922067668d8425078c7e98c0873c288b86a3189984bc6fc78302b3d682058c4d81e5a721816c4ed88151b0497ed25ffb7ec628ff7bb12fff7a26363079c81d30799c853f7976ef16795b686a78e6a6bc77e90f59779145117786e6957722059d76883f0f75ed2dc374371e9f7235c86071ebea7c715b90ad70770f5f706e1afa6f508a4a6f43ea976e53d0646c6b07056b7fab696b1211c96ac4e77d6a87738369904ec9698f8f7769548d2468ff83c268cd4f1168bb151a687f2e806827dfa8669586056632eccc65d88ac364b7656c643f8c6b62bc2e5c620278c661fa891460ccdd786013f4555f83829a5e43ac6e
  | 9, 10 => 0xfa4f38a7ee12c54dd95c5235d6b9f38bcef53381c9a1a983bb6591a0b533f09fb45b1497b3ee5fd1b198bc9eb11b3676b03b1c5fad0a2249a927f774a54fe581a46d2ef3a4234630a3d38329a304b7359deb9d439c3178d19a6cd7b29955825098f5fe4c9765e29c957c05e6957a19a9
  | 10, 0 => 0x2563fe192547379b250036df24f1d90e24923197242a74e0241a19e723fc0e4423d4986c23937e8522f2b390226d9e5f225227cd2232fccd21d460ea21a9023c2085ba6f1feb40ca1feab86f1dbf2e791d43fbd41c91f0b51c02e4e51b9b06e31a3039c4196926bf19570811194d07b41867ad1418097fbf1803566017a485a016ff67ae169f5cd9167ebc1d155b070715303b8814c25be7147387c8140ddc32122bc8a911f546a611c9fc5910eee49c108a8de8108a262d0eccb7400de1f81f0db6ae630db3a33c0b8daa5b0b5d6d2908cb2a3507852a5a07540f080499b2c10346c6ec01c0cf2f019bcd0d0132a60a0122554d011dc73700f26ece002f4827
  | 10, 1 => 0x966087349542aab190943691902d5b0c8f8b65ae8f0252678d842507855c72848302b3d6816c4ed880d29a3979fc07f6752fd48169904ec9655e0be16013f4555dfdbd4f5bcd8fcd5ab5abb153fc1e2652b2351452377d075111b38450a840dd4f85907a4f4e6d214f1c75a54ef5be6c4e31041e4c102132490e14d748a30f48479295b9477294e646d95771465f78f844aae862448b58424433319843fdcee442a809fe424b4c73417604ab412582f03e51fe3b3d88f5423a9cdd1a3a97ffb835e8537e35db2393358f846f33c0c90031c32ec3315f0dca30b17a1b30a941482cbbaac62c9d909e2b7a0cc6292e66d9292c0d97276f815f26dddbc72639e611
  | 10, 2 => 0xee9a4055ee12c54dd5f72ec6b5bdd37bb40748eeb03b1c5fa6ea9da8a4234630a304b7359deb9d439cee05e09c26fc2499f9d8c396f519d9
  | 11, 0 => 0xb40748ee8f8b65ae8302b3d646d95771358f846f242a74e0196926bf1957081117a485a0167ebc1d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x5
  | 6, 0 => 0x480e0280240057584325004020000000000005001594108030300000000000020001a5150030675588434404050000000000000471953244040100000000000060000000000009000000000000b0000000000001000000000000147185500c94000480a01802400001885110d30800159325003010000000000005755884344040500000000021060795940084403000991550030200000000000000001a15500300760c915500400001804340a3080018450508306000d9544403000480a03806400375594204040300118510c9309
  | 6, 1 => 0x1a5110d30807995324404020001a5010d3080001a1550030037159400844030795940084404471953244040000000000000000000000000000001181548030600000000121060480a03802400000000000000007919510c9402000000000000500000000061023715941080403079593110040307919500c9400000000000000700185500c930007959325004010000000000001760c915500402000000000000571119500c940000000000000060000000000003760c905504400000995110d30575584325004000019432406300
  | 6, 2 => 0xa038023004719532440402000000000000347181510c9401760c954440402000d951480305001182544030647185500c940047181510c9400048020280640337159400844030000000000001760c9544404000000e018023000019532440301000000000000800000000000080380a008064004719532440400760c9058404010480a0080640007995320404040001a544403020000000000007001182544030600000000841050000000000005000000280e20200000000401060001a0548430600159420403060001a52440305
  | 6, 3 => 0x7959410804030019443480308760c9058404027610d5048440507985500c940100000000000053715941080403001594108030300012018023000280e018024007610d05884405000000000000037159400844030011805484306
  | 7, 0 => 0x1593250430000000029002000001a5244030500000510c9200000c002806304000000008010400000354402070019423406302000005008520000000000000060000a008063020015932500301000000008010500195300843040000000081102760c9058044000001235440303001593250030000000000121060001202806301000000000210b00000058402080001200806301001593110830300000000000030001a0550430100195324403020015940084306000000180220100000000000010000a03802300000000000a108
  | 7, 1 => 0x12254403010001a1550030100185500c93020000e0290430200000048842040001200806301000d8058803030015932504301000c9544403000480a038024010000000002106000000480a2080001a055043010015931108303001954008430700000000c9100000000001210000000048022070001a5444030000000058402000011535440301000000001210600000324062000001a1550030000119510c93010001a5444030200012038023000000e42002304760c905840401000120380230300185500c93010000032440200
  | 7, 2 => 0xa01802300000000000e105001594108030400185500c93000000a0380630000194324063020001a155003010000e0280630400000038402080001203840301001953244030000000155002000001a54440300000120180230000000028022000000e01802304000000010010900159410803060001a15500300000005444020200115354403000000004806200000195110d30500000510802040000000000000001594204030400000000801030000e018023000000a0380230000000000121030000e01802300000000480e203
  | 7, 3 => 0x12058803050000000012104000c90550430200119510c9301760c9058404010019541080303000120380230700185500c930100012038853010000e058403020001a54440300760c9058404020000000000000000120280e300000d905504300000000480e2010001203802301000d954440302000120380a3020000e0280230000000055042000380202806403000120280630100012008063020018035484303000002544020100000018022000480e028064030000a00806301000000480e203000000010d1080015932504301
  | 7, 4 => 0xe0480630500119500c9301001854008530000000048062020000000000000000c95444030200181510c93000000003802207000000001210900000514802050008d0584030200000254402020000e028023000000e05504300000122340230000119500c9302000c90180230100000038122050001203806300000000480e2005758032504400000000000e1030001a055043000480a03806401000000001210500012038803035758032504401000000000e1040015932500302000120380230300195324403020019532440301
  | 7, 5 => 0x159301043040001202806301000c95444030000159410803030009545440305000120280e30200159400843040000004806203000123240230100159400843030000a03840301000c9008063000000a018023000000e410023000000a058403020019540084304000d525440300000000280620000159311003030000a0080630100012038063000015941080303000195110d305000d95444030000012028023000480a0180240100159325043000001203802302000000584020b000005148020500000000401010001203802301
  | 7, 6 => 0x1a155003000480a0380640200012504843050000e028023020001a5444030200000155002010000000000003000120380a3050000004802200000000000e10400000000061030001a1550030000012200063030000e0280230500012018023030001203806300000000480e2000001a200063050000e54440300000000280e2010000e0280230100159325043020001203802301001195108d302000000000e1000000a1550030200000038062000001203802301001953244030100181410c130100000038402000010d51480305
  | 7, 7 => 0x120180230300012008063000480a01802401000000000a109000d525440300000000010010600000254402010000050484205000120380a3040000a055043020000000000003001854008530100099544403020001a54440300000120280e3010001a055043020001202806306000d9544403000001202806300000000001210800194324063010015932500300000d905504300001443548030400000000801030015940084306000120380a3000000e028023020000e02806300001083544030300181510c9300000000380a200
  | 7, 8 => 0x79594108040400195420403060000e0280630500000500c92090000e0280230100195320403040000050484205000d805884303000000480620b0000000040109000002100220300012038063010000e0180230100159311083030001223406302000000180220000099055043010000a5444030200000454402000000000000000001943240630100119510c930200000000c5101000195110d305375594108040300000058842080000e0080630200000000401060001a1550030100144204c130000159325043000001205880303
  | 7, 9 => 0xa038023000000e0180230300184354803050480e0080640000000000000060000e54440300000123240230200000048022010000e0180230000099155003010001a155003010000e058803030000002802204000120380a3080001a5148030500000000801080000000002102000120280630000185400853010000002802200000c9008063000000e0080630000195320403030000a0180230200195400843040000e21402300000120380a301000003544020500000048062090000054440200000000280e2005758032504401
  | 7, 10 => 0x35440209001953008430457580325044010000a0380630100181510c93010001a1550030000181510c93010001a1550030100159410803070000000000000001953008430300194324023020000e028063030015932504300001953244030000000354802040000a41002300000000004010600000155002000001230006304000d52544030000000515002010001203806301000c901802301000000000000b00000500c520000000000401080019532040303000995444030000000000841030480202806405000c905840300
  | 7, 11 => 0x12510c930200195310803030001a15500301000c90584030200184454803080000000040102000000480a205001593250030000185500c93000380a00806400000000380a202000d805884304000000480220b000000480e209001593250030200184354803030000054440200000000380a200000995444030200181510c930000181510c930000000000000000480e01802403000d80588030300184324023000000e028063080015940084304000d8058403040018032406302000000000a1010000a038063020001a21002303
  | 7, 12 => 0xc910000000324402000008d018023020000e0280630100012314023000001200806300000004008420300000058842080000e02802300000000480e200000000480e206760c90584040000185400c5301000d8058843030480a0380240100000000c8103000120380a3030000035484206000000381220800119510c9301000d9544403020480a038064010000045484208000000380a203000120280630000002028063030000e25040305001593250030000181510c93020000e0280630100119510c9302000d805884303
  | 7, 13 => 0xe200063040000e50085300048020280640400000354802040000e40006302000000280e20900194324063020000035484204000c905840301048020280640300144354803030000005880208001153544030200194324063010001a15500301000120280630300012058403010000a1550030100000038022000001200806300000000480a2030001201802301000c120406300048020280640400000155002000001202806304000991550030100181510c93010015941080304000000000000a00195234403020001232402300
  | 7, 14 => 0x121090010d02806305000000000a1050015931100303000120280e300000000280e200001884340230500000000c91010001220006303001953244030200000544402000014031485300000d9544403020000025440200000120584030000119500c930000195420403040001a524403050000000040100000d5254403010000005504200000000381220800119510c930200195410803060000e02904302000000480a209001883544030300000510c92000480e0180240200000000061020001a1550030000140214c5300
  | 7, 15 => 0x480e0280640300159400843030000e21002305000120588030400002028063040000004806200000000000e100000000384020003802028064040001a54440302000000000000a000120080630100188434023080380a01802402000c90180230000012324023000000002806205000d9514803050000e008063010000000000009000003544020a000c4058803030001202806304001803548430600000500c92000000a0080630000000514802050019540084304038020280640400195324403000001a155003000000054440200
  | 7, 16 => 0xa102000000000000a0000032500200000c90584030100000000801060001a5444030000194324023000019432406300000120284030200000000841080001a1550030200000000000060000000000003000005010d208000d8058843030001a54440300000123240630000000058842080001250085301001593250030000012250403030015932504300000c9055043010001a5444030000012254403000001203806303000000000000500181410c130200188434023080000e2544030200144354803030019432406300
  | 7, 17 => 0x185500c93020000e02806301001000280630400012018023000001230481300000121000a3040018032406301001953244030000000000000060380a01802402000000008010800185500c93000000e028023040019532440301000000000000100000154802050000e018023000001201802304000005210d2080000a018023000000e018023000000e02806301000000480e204000000480220100000354402010480e018024050019540084303000000000000600000354402080480e0180240300159325003000019532440302
  | 7, 18 => 0x15941080304000000480620600119500c93000001a51480305000995444030100181510c9300000000381220500195324403000000e1000a3040015941080303000000584020b0000050504206000000380220300000000000020000005484206000005008420400180324063000001a5440430000000000c910000000028062050001203802303079594108040300115254403000000000084106000120380630000000434802080001a210023030795941080403000001548020600000000000000000e0280630200181510c9301
  | 7, 19 => 0x510802030000e25040304755884344040500000410802030000000000009000000480e2060000031485200001000588430300012018023050001a1550030157584325004020001a5444030100012038063010019532440302000000000000000104304813000001a5444030100000000801047558043484405000120380a3000000000000000001803240630200012250403040001a51480305000991550030000119510c93000000202806305000002100220300195324403010000a0380630075580434844050795941080403
  | 7, 20 => 0xc915500300000020280630600185500c930107959410804030000e0280630300119510c930100000510c920900181510c9301000000008410300012038843040000005884208001843548030700012018023020000000040109000000001210600000058842060000000000008000005210d205000195110d305000c90080630000000018022080001a5444030000000500c9209000000080620200119500c9300000005148020500159410803030000e0480a3080000e028063070000a0380630000000354402080019432406302
  | 7, 21 => 0x10001a504843050000e04806305000120280e3000000004840200000000280e20a000005444020000000028022060380a018024010001a1550030100012028063030000a3544030000000000c91090000005880206000120380a3080001a5444030200000000000000001232406300000d9210023030000003812208000120280e3010000a03840302000000180220b00000000401010000000000000000000480e2050480e018024020000000000008575803250440200000520402040000a1550030000119500c9302
  | 7, 22 => 0x584020000000000021080001a54440300000d8058843030001a514803050015941080306048020280640500000048c92000001a54440301000c95444030000195420403070000004806205000000000000500000000c910200000000c910000012510c93000001a544403000000a0380630000012018023007610d05880405000120280e3020000002802208000000000e10700002028063040000a039043000000000000001000123240230000000500c920900159400843040000a008063010000a03840301000000000e101
  | 7, 23 => 0x4010500002028063050000000006105000120280e30000002028063037610d058844050001a1550030000000000c910000000000000080015942040306079594108040300000000121010000202806303000000380220400000058802050019432402300001040280230300012038843050000000012105000000180220b000000488020300002028063040001a544403020001a54440302000120380a3020000054440202000000004010800000001001090000e54440300000c90180230000000000000080000005840209
  | 7, 24 => 0x1210900000018022000000202806308000000010d105000120180230000000000000050001a54440300
  | 8, 0 => 0x500c9201000000488d202000000280620100000214022020000001802207000005444020000000420022030000a0584030000000028062000000015500200000000484020100000254402010000023406201000004000a203000000488d200000003240220000012510c9300000000480a202000000480420100000038062000000030006204000003544020300000510c9202000000290020000012250403030000004806201000003544020500000000401050018423402301000000584020000000155002010000002802204
  | 8, 1 => 0xe058843050000032440200000000480e2000000000012100000003544020100000000c4109000005444020100000048c9202000000000210300188354403040000e058803040000000006106000003210020400000058402050000015500200000d5254403020000003840201000005110d2080000002802202000000380220600000058842040000031002204000000588420500000155002000000035480204000004000620200000048022010001202806304000002504020600000000121060000e02806305000000004010b
  | 8, 2 => 0x500c5200000004204020600000000c910000000058402010000004806203000000480620300000500c920000012018023010000052040203000000180220000188354403040000e40006300000000480220000000410022010000002806209000005444020100000500c920200000325002020001203802301000000584020400012038403040000a4100230200180434843050000000000000001804548430500000354802040000004806201000004340620500000500c92020000e40006300000000488120000000000c1100
  | 8, 3 => 0x801040000003802201000003240420000000510c9202000000008010800000500c92000010d25040305000000480a200000000000a1020000e41002303000000000e10500000008062000000054440200000000000e109000001000a203000000480a20900000155002000000002900201000000380a2010000e05880303000000480e204000000480a20400000038042010000035440206000000280620200000039002000000000012109000003548020300000500c9202000005010d20800000000000020000e02900302
  | 8, 4 => 0x40084203000000480a20800000000c910100000048c920200000500c9201000000480e204000000290420000000038402000000031485200000000010410b000000384020300000354802040000a0380230100000234022010000002802200000004340a2050000004880203000005008d2020000004802201000002000620500000510812000000002806200000005210d20800000324022000000032402200000000000610800188354403040000e05880304000003244020200000254402000001203840304000001000a208
  | 8, 5 => 0x54440200000002100220400000000121020000000000005000000000a1080000002900201000000280620000000354842060000000000001000000000210b000122000630500000510c920000012028403000000004802200000000480620000000038062050000041002202000000480e202000000488420500000028c52010000020006203000000588020400000500c920000000000021060000004840203000000480a20000000500c5201000003240620000012018023000000042004206000000290020000000000c0109
  | 8, 6 => 0x48c920000000510812010000042040203000000000a100000000380220100000420062030000004880204000000488020800000200062040000000104101000002504020400000048022050000004806201000000004010b00000510c92000000000084106000000000e10800000029002020000032440201000000390420000000048c9202000000584020100000038402020000003904200000003544020300000325002000000000000000000000380620600000234402010000004802205000001000a2050000032402202
  | 8, 7 => 0xe05884303000004000620600000500c920100000400062010000004885200000000010410000000500c9209000000480e2020000003802204000000480620100188434023050000a400063000000e05840301000000008110000000324062010000054440202000000480e2010000000000000000000480a20800000038402000000002806200000004008520200000048062010000000006104000000390020300000510c920100000018022030000000012100000000010d1080000000040107000000388020400000510c9202
  | 8, 8 => 0x38022000000032406201000000008010800000048022030000002806204000003148520200000510c1200000000010010a000004000a2040000040006202000002340620200000028022010000e0280630400000400c5201000000480e205000005210d20800000324042000000004802200000005010d208000c905804300000002350020100000001001060000002840201000000390820600012500c93010000000040109000000480620000000038022000000045484208000000280420100000048062000000035440200
  | 8, 9 => 0x4200220400000000021090000031402200000002340220100000544402020000000002104000000000210a0000a01802301000120180230100000028022000001a20006303000005210d20500000028062030000a0380230100000254402000000042006206000000588420800000000121040000004802208000005008420400000028062010000005840201000003250020100000354802030000003802201000000380a20000000354402020000041080204000000008410500012500c930200000048062000000000000005
  | 8, 10 => 0x2806204000000000210900000039042040000004802201000000004010b00000000401040000000012107000000488d2010000032504201000002100220800000410022000000002904200000120380230200000400c520100000048c92010000003840203000000008410700012058403020001232402302000003244020000000400062000000000002105000000290420000000434062050000000000000000000000a100000000290420200000048c920000000234022000000005840205000000380a2010000001802200
  | 8, 11 => 0x5110d20800000410022020018032504302000000280e20200000410022000000e4100230100000324062020000041002200001080584030300000018022040000001802205000003544020000000254402000000003880204001594108030400012354803030000005884205000c90180230000000028c120000000510c9201000120380630100000301082040000001802201000003048120000000510c9200000000480a201000000180220100000048402050000003840200000c90180230000000325002000000003881200
  | 8, 12 => 0x380a20100000048c92000000004802201000004100a2030000005880204000000010410a00000018022030000000000003000000384020400000324062020000020406201000000280620400000000841060000004806201000000484020400000048c9200000000000a10200000400842040000032500202000005210d2080018443480305000000000210200000038402000000002840202000000480220000000500852010001203840305000000480e202000004348420500000028022000000032402200000000380a201
  | 8, 13 => 0x48062060000004840203000000000000900000028062010000e420023040000e0584030500000500c5200000000280e2000000032402201000000380220000000544402010000e42002303000000484020000000038062020000020006203000000380620000000354842050001220006305000123548430500000048022020000000002108000003250020000000000801050000031080204000000380a202000005008520000000324402020000003806200000000280620800000500c520100000324062000018032504300
  | 8, 14 => 0x12210023030000000806200000000480a200000000380a2010000004840205000d54548430500000500c92000000003802200000000280620000012028403000000035484203000000280620000000048c9200000004340220800000400062000001225040305000000280e202000000480a20000000028062010001203840300000003240220000000058402050000032440200001842350030100000510c120200000028062000000004840200000000480a2020000001802204000000000000300000214c52000000035484205
  | 8, 15 => 0x3250420000000000c41090000005504201000120384030200012058403030000e058843050000001802202000120280e30000000000021000000035484208000000280620000000038402010001202802303000005210d20500000048022000001205884304000000488020600000001081060000021402201000000010010300000058842050000041002202000000010d10500000048022020000031100204000005444020100000028062010000004806201000120588430300000018022030000032402202000000480a205
  | 8, 16 => 0x324062000000025440200000004200620300000420062030000003802201000122000630400000324402020000004840200000003544020100000410022000000002900200000004200620300000028402020000005504200000120380a30100000008062000000a0180230100000500c920000000354402010000e0280230500000434062080000000040100000005210d2080000015500200000000480e2020000000002103000000000e104000003148520000000354402000018835440304000000380a2000000032402201
  | 8, 17 => 0x410812020000041002201000005444020100000048c9202000c9018023020000a038063010000e0290030100000235002010000003840202000001550020100000058842060000032402202000000004010800012200063030000000040102000000280620800000000401080000035440200000000000e105000000000e107000003244020100000048c020300000000c9109000003240220100000001041090000035440200000000380a203000000380a2080000a05840302000002344020000000310802030000035440201
  | 8, 18 => 0x280220a00000000401010000000000005000000010410400000434402080000015500201000000000210200000028022000000000000008000000388420300108018023030000002806201000000390020400000410022000000004802200000000280e2000001232406301000003250020200000510c9201000000380620400000000c4109000000588420600180354843050000005880206000000380620100000500c920000000500c92000000002802206000000480620100000204c120200012200063040000032500200
  | 8, 19 => 0xe1040000a05840302000000480a20200000250042060000000000008000000480e2080000e028403000000005840204000000390020400000001041000000025040203000001000a20400000055042010000002802200000005108020300000254402010001203802302000000380a200000005010d205001844348030500000048062050000004840202000000390820300000400062030000002904200000000484020200000048c0204000000280220200000214c52010008d0180230000000510c920000012500c9301
  | 8, 20 => 0x2802200000000390420400000000121040000025040203000003544020400000000401000000004802201000002100220700000354802030000003840203000000000210b000000584020200000048062010000e410023030000030481200000002544020000000058402030000003840200000005210d2080000002802202000002504020600000510c120000000400062000000004840203000003244020000000434062050000032500202000000001210000000001001090000e01802300000005110d2050000004880207
  | 8, 21 => 0xe108000000584020400000544402000000003806200000000010010400000510c1200000000010010a0000a40006301000120280e301000000480e2000000002802202000000380a202000003000a2040000e018023030000e0290030100000500c92000000032440201000000480e20000000314852010000005504202000003240620100000250402050000015500200000000480e203000000480620700000420402070000005884208000000010410200000048842050000005840205000003210420300000000c910a
  | 8, 22 => 0x38402010000032402202000002100220300000500852010000032402200000000480e200000000480a2020000000806201000000000e1090018835440304000003548020300000058402020000035440208000000000e10300000324062010000043484205000004340a20500000500c920000000048802030000002802200000003000a203000001000a2060000015500201000000000610b000001550020000000000801080000e2000630400000500c92000000031485202000003240220000000000c010a0018035484305
  | 8, 23 => 0x32500200000000480620800000420402040000003806205000000000000200000000801030000a0180230000000028022000000e20006304001843240230100000048402010000030481200000000010010200000325002010000000012109000000484020300012250403040000030406200000004100a2040000004840205000000380a20800184325003020000000006105000000001210500000410022040000025440200000005010d208000000584020400000500c920a00000510c92010000005880208000000010010a
  | 8, 24 => 0x484020000000038022020018032406300000d91000a30400000058802050000000040100000000388020700000200062040000042006206000d525440301000005444020200000048c52010000001802200000000000e10900000324402010000001802201000000004010400000354402010000032402201000000480a2000001225040304000000004010b00000055042000001205840301000000000e105000002000620400000048c9200000000480e20500000000c9102000004100220000000000401030001225040303
  | 8, 25 => 0x380a200000000004010a00000048c8203000000280e2000000035440202000000001210a00000400c52000000004884203000000000e108000000080620000000310802040000040006202000000000000a0000043480205000000000210200000048c9201000001550020000000310022040000054440200000003240220200000400852010018032406300000000380a20000000400062000000054440200000000480a201000002544020100000000c910b000000000210500000000c9100000000000a1000000002806200
  | 8, 26 => 0x324402010000051080204000000000e1090000000040101000005148020500000325042000000005884203001594204030400000048022000000001802208000000180220300000504842050000000002109000000388120000000048062040000000002104000000480a20400108058403030000005884204000120380630400000324402020000005840208000000390420200000048802040000004840208000000280e2000000000040103000000280e20000000058402020000e0290430000000400842060000000040102
  | 8, 27 => 0x54440200000005110d205000003210420300000354802080001201802301000000384020100012324023000000003806201000003008420300000048c5201000000280220200000000801040000e250403040000025440200000003100220300000500c9200000004100220000012254403010000004806204000000484020100000008062010000030084204000000280620300000058402000000000100109000005444020100000454842050000015500201000000380a200000000480620300000510c92010000035480206
  | 8, 28 => 0x28402000000042040203000000480e20000012038803030000003802203000001000a2030000005840200000001000a2030000a0180230100000510c920000000300842030000032406200000001550020000000048c92000000e25040304000c9018023000000004880206000005010d2080000003884204000000180220100000048812010000003802202001040280230300000048c9200000000480a20900000510c920100000214022010000000040102000003244020200000008062020000a05840301000000480e203
  | 8, 29 => 0x15500200000004008420400000500c52020001a210023030000023504201000000001210900000048c920200000039042000000054440200000000280220500000304812010000005884203001843548030300000001001090000040006200000000000a10a0000e2100230300000048c92000001a210023040000003802201000000010d105000000280220000000250402040000045484208000000001210a00000500c9201000002544020000000000401000001203884303000000588420400000058402060000040084207
  | 8, 30 => 0x18022010000004802201000005108d20000000500c920200000354402030000004802201000000480e2030010d028063050000032406200000000290020000000058842030000005880208000005110d2050000002840201000000480620400000000000010001a2100230400000304812000000040084206000001550020000000028402020000003806202000002544020000000048062010000002802200000003548020500000510c92000000035440204000000484020000000058402000000035484203000000000e102
  | 8, 31 => 0x210000000000401010000032406201000001000a20400000000061020000002904200000000000000700000000c510200000324022020000005840202000005108020400000038062040000e01802303000000584020300000000c91010000040006201000000004010500000058802080000032440200000000280e2010000001802202000000010d10500000048022060000000002109001594108030400000058402060000004806200000000000000600000038842080000031485201001843250030100000028c5201
  | 8, 32 => 0x30000040084206000120284030200000510c120000000500c9201000000480e207000000280220200000048c9202000000180220600000454842080000002806201000003110020300000325002010011535480305000000584020200000325042010000000012109000003544020000000410022000000004880205000003548020600000048402040000021002204000000000a10a00000324022020000045480208000000000000900000324062020000042002206000000480a201000000008410300000048c8204
  | 8, 33 => 0x284020200000048c020400012028063000000002802201000002544020200000048c02030000000084106000000001210a0000004840206000001550020000000410022000000032406201000003240220000000048c9200000000080620100000311002030000032440202000000380620400000400062010010d250403050001202804301000001000a205000000480e2000000000000005000000480e2030000000080108000000284020000012510c93010000003840202000002504020600000058402010000005840203
  | 8, 34 => 0x48402000010d02806305000000000e109000000000610200108058403040000003802203000000588020500000000c910100000325042000000041002202000000390020300000234402000000003802200000003240220100000000121060000e21002304000004340620800000000000010000041080206001594108030400000324402020000035440200000000484020300000048402010000032406201000004204020600000048c9200000003240220000000000c9109000000480a20500000028062000000004840200
  | 8, 35 => 0x32104204000000280e2000000005840200000000380a20200000000000080010d05840305000000380a200000000000210a0000030084203000000480220000000544402010000041002202000002504020600000354842050000e25040304000003210420300000048062030000041002200000000080620100000510c9202000000000610a00100058843030000000040102000000480e2010000005840203000000388420500012500c9300000003544020000000510c12000000054440201000000000a1090018845440305
  | 8, 36 => 0x354402010000005840202000004008420300000018022000000032440200000121000a305000000384020800000000021060000054440201000000384020300000008062010018035484305000000000e1030000002840201000000001210100000400062060000040006200000c905840302000004340620500002028063030000003840203000000000610500000048022030000003908203000002544020000104028023030000035440203000000380a20000000500c92090000005884204000001000a2030000040084203
  | 8, 37 => 0x48022010001203880305000000180220200000055042000000002904201000005210d2080000021002206000005244020500000008062010000003840202000000388420500000250402050000000100109000000001210900000018022000000051080203000000380a20000000325042020000032406200000000004010900000155002000000005840202000000008410300000354402010000000002101000001000a205001594204030300000420402070000202806305000122504030500000038842040000005840205
  | 8, 38 => 0x3250420000000510802030000040006200000005210d20500000048062030000e02840300000d525440301000003240220200000354402060010d0584030500000325002010000005840201000000000000200000000c4103000000001210b00000038852000000004880203000000384020700012058403010000054440201000000484020000000038802080000003880204000002100220600000028c5201000005210d2050000004802203000000000000000000048c9202000005444020200000038402000000032406201
  | 8, 39 => 0x588420600000500c920a00000420402060000002806206000000000210500000048022000000003806200000d525440301000000380a20200000250402040000004802204000000001210b00000324042000000000108106000005210d2050000054440200000000380a20000000048402000000005884205000000480a20100000434022050000000806200001083544030400000058402010000005884203000000004010b000000550420000000048402040001a21002305000000010d108000000380a2000000003900203
  | 8, 40 => 0x380a20a0010405880304000000480e20500000048c920000000500c920200000000121080000000040105000120280630300000058842060000202806303000003240620100000400842060000e0290030200000000c9109001844340a30500012028063040000001802203000004108020600000000c91090000054440200000000584020600000434402050000e25440302000000480e205000000000000900012038023030000025040204000004000620000000000c910000000048c5200000005444020100000000c9101
  | 8, 41 => 0x480220200000038402000000000012109000000480e2080000005840206000000004010b0000005840208000000180220500000354402020000025040206000000000610800000048c92000018432402300000000000e10100000000801060000e028403010001a21002305000000001210a000000588420500000000c010400000000121030000000002109000005210d2050000025040206000005210d2050000000000008000000584020600000048402030015942040303000000000210b000123240230100000500c9200
  | 8, 42 => 0x8062000000043484208000004008420400000000801080000002802205000005444020200159410803030000003812205000000380a2010000005840201000120584030300000324402020000051480205000120584030400000000121000000004881200000003244020000000500c92020000e02840301000000480e20000000048c92010001a2000630500000400062010000032500200000000010010a000000000e1090000000000005000000180220000000028062040000051080203000000000e1090000005884203
  | 8, 43 => 0x4344020800000048c92010000025040204000000380a20100000055042010000031402200000003240220100000058842050000000012109000000480220600000200062060000000000000000000480e20800000000000060000004802200000000001210200000048062020000000002106000000480e200000000380a2000000032440201000002504020300000058402000000e048063050000041002200000000080620000012038063030000001802205000001000a205000005148020500000454802050000002802208
  | 8, 44 => 0x4000005444020200119200063050000005840202000000480e203000002504020300000000401010000000100109000003148520100000048c920100159410803030000000040109000c90584030200000354802030000032402202000005110d20800000155002010000000084108000001000a203000000000000900000324402010000004840202000005210d2050000025040203000120280e3000000003840202000000000000b00000008062000010d05880305000000588420300000250402030000000040104
  | 8, 45 => 0x10d10800000250402060000041080203000000588420800000000c910900000048402030010402802303000123240230100000514802050000004806200000003008420300000048062000001205840300000000380a20a0000032440200000c905840301000002504020300000038402030000000000004000000480e2080001203884303000001000a205000000280220600000000c9100000000280e2020000000002107000003244020100000000000060000052440205000122504030500000000121030000035440204
  | 8, 46 => 0x25040206000c905840300000000480e20800000000061000000000000005000000000000800000434402080015942040303000002504020300002028063030000054440200000000000e1060000a03802301000005148020500000410802060000054440201000005444020200000018022000000001802202000000000e10900000000801050000000012107000000380a2090000000012100000000004010b000002504020500000454802080000025040204000c90584030000000048c920000000000c91000000004884206
  | 8, 47 => 0x90010d250403050000000040100000000480e203000000000000900000250402050000025040208000003250420000000048c92020000000012109000000000000600000250402030000202806305000000010d10800000324402020015941080303000000484020000000048022090000002802205000002504020500000000000060000001802200000002504020300000324062000000025040203000000010d105
  | 9, 0 => 0x8010400000028402000000035404201000000000000600000000c91090000000104101000000000e101000000010410400000000c9101000001000a205000000000a103000000010810300000325002000000003802202000000000a10600000454402050000003904203000000008110100000029042020000000040106000000000e100000000000e100000000000a100000004000a203000000008010600000000c91010000005840203000000000e10400000324062020000002802203000000000e102000000000000a
  | 9, 1 => 0x21010000000006102000000008010600000325002020000000104102000004548420500000000061010000000081100000000008d102000000390020300000001041000000000100106000000000a10700000000c810300000058402020000000104101000000000000900000000121000000000040102000000000a105000000000a101000000004810600000000c8104000000588420400000000000000000000000009000000000a1000000000040105000000000a101000000000210000000039002010000032406201
  | 9, 2 => 0x388020500000000c1102000000000610100000000121050000000006102000000010010700000410022000000000084105000000480e200000000480a2030000000012108000000280220300000000061010000000040107000000008410800000038022010000000000002000000004010000000510c9200000000004010000000000c810400000000061020000005884203000000480a20400000000401080000000002103000000000210300000000021010000000080105000000000a10000000000021000000000040103
  | 9, 3 => 0x25440202000000000e1050000000002105000000480e204000000010d105000000480a201000000001210000000325002010000004880204000000008d10200000001081060000000084103000000280e20000000001001030000000002104000000010810400000048062000000032402201000000008410400000018022020000000084103000000480e202000000001210a000000000e100000000000e10200000000021000000032406201000000010410200000000061000000003840202000000480a204000000000a102
  | 9, 4 => 0xe109000000480220000000058402050000000100101000000380a2040000000006108000000390020000000029002020000000104106000000010d10500000000021010000000012103000001000a20300000000c910200000000000090000041080203000000000e10100000000811020000000084105000000000210100000000c51020000000084103000000000a1000000000104101000000004010300000000401030000000002100000003250020100000400062030000000104104000000010810400000500c9201
  | 9, 5 => 0x48c92000000000085101000005210d205000000000a104000000384020300000001001000000003900202000000010410400000001041010000004840203000005108d2000000002806200000000380a204000000280e2020000000084106000000000a10a0000005880203000004000a2030000000080103000000000e1050000000002105000000000210000000000c9101000000390820300000000000080000000080106000000008d1010000000002100000000000610200000000c910100000000061040000000006105
  | 9, 6 => 0x401050000000002106000000001210200000354402020000000100103000000010d1050000000100103000000000210000000000c91090000000012106000000010d1080000000002101000003548420300000000000010000000040100000000380220100000000c910000000000c91020000000104100000003548420500000000000030000000040101000004108020300000000061000000000002101000000588020500000000061010000000004100000000000e105000000008010500000048402010000000006100
  | 9, 7 => 0xe10200000000c9100000000008510100000400062020000000000009000000000e102000000000610000000000121010000000040100000000010d108000000380620300000354842030000000004100000000000e10800000000401010000000000003000000001210100000000000000000000080103000000008010300000000401040000000000007000000480e202000000010d105000004000a20300000254402020000000006101000000000000a00000039002010000000080105000000010d1080000000000000
  | 9, 8 => 0xe1050000000100101000000004010000000000c9100000000480220100000001001000000000012104000000000a1020000000012100000000001210300000000801050000000012102000000004010600000001001000000003806200000000000e10100000000000090000004840200000000381220500000048022030000002840201000000001210000000000c91000000000080108000000004010100000000801030000035440202000000480e2030000000000009000000000610000000000841060000000108104
  | 9, 9 => 0x6100000000000e1090000003806205000000000e108000000001210800000000c91000000000002105000000000e100000000008410300000354802030000000006105000000001210100000000121020000000104100000000000a101000000000e103000000484020200000000c410300000000000060000000000005000000004010500000000841030000032402200000000000a101000000280e2020000000080105000000008110200000000c9102000000010d105000000004010200000000000000000003802205
  | 9, 10 => 0x900000000c110000000001001000000004884204000000008d1010000000000006000000000210100000000c910100000410022030000000006106000000004010100000000061010000003840205000000000000100000000c910100000001041030000000104103000000000e103000000000a10100000200062030000003880203000000010010100000000401010000041080204000000010010600000000c9100000000010410200000510c92000000000012108000000001210000000048c92010000000100100
  | 9, 11 => 0x6108000004108020300000000c91000000000000009000000000a10200000000021040000000040102000000484020000000000c5102000000000210900000000021020000002840202000000480e20400000001041010000000080103000000010410100000000c51010000000002102000000000e10200000000021030000000100100000000000000b000000000e1070000000104103000000008010300000000021040000000100106000000000000500000000c91000000000006100000000000000a00000000c5101
  | 9, 12 => 0xc910000000000c9109000000000e105000000004010300000000c51000000000000003000000000e10600000028402020000000080103000003250020000000500c920000000038842040000000000004000000000a100000000010d105000000008410800000048c920200000000841080000000002104000000000000800000000041000000000012103000000010410000000001001090000001802201000000000210200000200062030000000002100000000000610500000000c910200000000c9101
  | 9, 13 => 0x4010000000001081040000000012103000000000a1000000005880205000000000e1010000000012100000000000a1010000000084103000002504020300000000401080000000000008000000000e104000005210d205000000000610300000000c91010000032504201000000000000a0000000084108000000004010400000000000050000000002108000000008d10100000000401020000000012101000000000e1010000032440200000000390420300000000c9100000000001210300000354402000000000080103
  | 9, 14 => 0x108104000000010d1080000000000003000000000a10800000000801060000000006104000000000e100000000390820400000000c91010000000012102000000000000800000018022030000023440200000000004010100000000c910200000000000030000001802204000000008010400000001001040000000006105000000008010300000038802030000000084104000000000a1020000000006101000000480e202000000010010200000048c92020000000100103000002504020500000000401080000000000005
  | 9, 15 => 0xc91000000035484203000000000a1010000000012101000000000000b00000000000000000000002108000000008d1000000000040102000000484020100000000121030000000002103000000000e1000000000002109000000010d105000003240620200000000c91010000000080104000000584020200000001001060000000012100000000004010600000000000000000000080103000000000210200000000c910000000000c910100000000c91000000000085101000000001210200000000841040000000006103
  | 9, 16 => 0x21010000000085101000000008010800000000061010000043440205000000008010500000000021020000045480205000000080620000000048c9200000000000000900000000401010000000000000000000008410400000000c01030000000084106000000000610200000000121090000032440200000003544020500000000c91000000043402205000002504020300000000c010400000000c910000000410022020000000080105000000010410400000001041060000000100106000000000e101000000000a102
  | 9, 17 => 0xc9101000001000a203000000000e108000003244020200000000c91020000043440205000000584020000000001001020000000012100000000000000000000000c91010000000012106000000000a1030000000040100000000000000a0000000000008000000000610100000001041020000000040106000000000000a000000000000900000058842030000043402205000000004010200000000c910000000000c910000000000c910100000000061010000035484204000000480220100000324402010000035480204
  | 9, 18 => 0x12104000000004010600000000401080000000012103000000001210400000000061010000000104106000000280620500000354402010000000000008000000000e1030000000012106000000000000000000000121030000001802205000000000e102000000000000a000000004010200000048402050000035480204000000000e10100000000401010000035440201000000000e10300000000c9102000000280e20000000434842050000000100100000000010d108000000000e10000000018022020000000006106
  | 9, 19 => 0x1210600000000401020000000000005000000001210500000000401060000000012104000001000a205000000000a108000000010d1050000000108103000000000000000000000c9102000000004010400000000121030000000104101000000000000000000000121040000025040203000000000000a000000000000500000410802030000000006100000000000000600000000121000000004840204000000000000200000000000050000004840203000000010d10500000410022020000005840200000000000000a
  | 9, 20 => 0x2504020500000000121000000000000009000000001210300000000c9100000002504020500000325002020000000012103000000010d10500000000000060000000040105000000010d105000000000e1000000000040102000000000e103000001000a205000000001210100000000c91000000000104100000000000e10300000000121000000000040100000002504020300000000000090000000012104000000000a10800000000000080000000006107
  | 10, 0 => 0x90000000000000000000000000400000000401010000000000007000000000610300000000000040000000012100000000000000200000000061040000000002102000000004010000000000000000000000000006000000000000000000000061020000000000003000000000e1030000000000009000000000000000000000000000000000012103000000000e1030000000000001000000000000300000000061050000000000003000000000000800000000000080000000000003000000000e1000000000000001
  | 10, 1 => 0x500000000c91010000000000002000000000610000000001041000000000000000000000000000300000000801040000000004101000000010010100000000000000000000040102000000000000700000000000020000000040105000000010010200000000c910200000000000080000000000001000000000e10100000001041020000000000008000000000a103000000000210500000000000000000000000000000000000000400000000000000000000000002000000010810300000000401020000000000003
  | 10, 2 => 0x1210100000000000020000000000005000000010810300000000121020000000000000000000000000500000000801040000000000002000000008010300000000000000000000080104000000000000000000000000060000000000005000000010410300000000000050000000012103000000000000000000000c91010000000002101000000000e101000000000000300000000000030000000000008000000000e102000000000000500000000000010000000000000000000008410500000000c91010000000000008
  | 10, 3 => 0x600000000000000000000000005000000000000100000000000000000000040105000000001210500000000801040000000000000000000010d1050000000100102000000000e103000000010d10500000000000000000000006103000000000e10000000000000000000000000008000000000000400000000c910000000000000000000000000003000000000000400000001041040000000000000000000010410000000000000000000000104103000000000000000000000000050000000000005000000000e105
  | 10, 4 => 0x300000000000050000000000006000000000000a0000000000003000000000000400000000000040000000000003000000000e10400000000121000000000012104000000001210300000000000010000000000003
  | 11, 0 => 0x5000000000000000000000000030000000000005000000000000000000000000000000000000000000000000000400000000000030000000000004
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_19 roots_19 10 s ws hint
  | 1 => checkCutEntry dom_20 roots_20 10 s ws hint
  | 2 => checkCutEntry dom_21 roots_21 10 s ws hint
  | 3 => checkCutEntry dom_26 roots_26 10 s ws hint
  | 4 => checkCutEntry dom_27 roots_27 10 s ws hint
  | 5 => checkCutEntry dom_33 roots_33 10 s ws hint
  | 6 => checkCutEntry dom_42 roots_42 9 s ws hint
  | 7 => checkCutEntry dom_43 roots_43 9 s ws hint
  | 8 => checkCutEntry dom_47 roots_47 9 s ws hint
  | 9 => checkCutEntry dom_48 roots_48 8 s ws hint
  | 10 => checkCutEntry dom_49 roots_49 8 s ws hint
  | 11 => checkCutEntry dom_50 roots_50 8 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_51 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_26 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_50 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_51 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51 == dom_51) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_51 goalM u ys) : RunD dom_51 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_51 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_16 : ∀ i, 16 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_24 : ∀ i, 24 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_32 : ∀ i, 32 ≤ i → i < 37 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 32 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 37 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (z7_32))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_24 : ∀ i, 24 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_32 : ∀ i, 32 ≤ i → i < 40 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_40 : ∀ i, 40 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_48 : ∀ i, 48 ≤ i → i < 55 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 7 48 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 55 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (range_split z8_24 (range_split z8_32 (range_split z8_40 (z8_48))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_8 : ∀ i, 8 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_16 : ∀ i, 16 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_24 : ∀ i, 24 ≤ i → i < 32 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_32 : ∀ i, 32 ≤ i → i < 40 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 32 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 40 → Z 9 i = true := range_split z9_0 (range_split z9_8 (range_split z9_16 (range_split z9_24 (z9_32))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z10_0 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z10_8 : ∀ i, 8 ≤ i → i < 16 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z10_16 : ∀ i, 16 ≤ i → i < 19 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 3 16 = true)
theorem z10 : ∀ i, 0 ≤ i → i < 19 → Z 10 i = true := range_split z10_0 (range_split z10_8 (z10_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z11_0 : ∀ i, 0 ≤ i → i < 7 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 7 0 = true)
theorem z11 : ∀ i, 0 ≤ i → i < 7 → Z 11 i = true := z11_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z12_0 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := z12_0
theorem checked (s : Nat) (hs : s ≤ 12) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
  · exact fun i hi => z11 i (Nat.zero_le i) hi
  · exact fun i hi => z12 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_51 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 8 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 12) (h : RunD dom_51 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_51 roots_51 goal_51 13 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_51 goal_51 := by
    have h0 : isConstB dom_51 goal_51 = false := by decide +kernel
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

end S_51

theorem low_51 : Lower dom_51 roots_51 goal_51 13 := S_51.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_51_bits : ∀ r : Fin 64, roots_51.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_51_lt : ∀ r : Fin 64, dom_51.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_51 T)
    (hlow : Lower dom_51 roots_51 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_51, Avail mask256 roots_51 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_51 hfan 0 roots_51 roots_51 rfl hsup0
  set out := (execN C.gates roots_51).getD C.output 0
  have hout : out &&& dom_51 = T &&& dom_51 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_51_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_51 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_51_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_51).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_51)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_51.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_51 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_51).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_51 &&& mask256 = dom_51 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_51 = T &&& dom_51 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_51, hd63, hout]
  have hnc_m : ¬ IsConst dom_51 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_51 roots_51 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_51, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_51 roots_51 0 roots_51 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_51.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 13 ≤ t :=
  lower_to_circuit6 fG goal_51 13 hT6 (by unfold IsConst; decide) low_51

def wit : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [17, 14]⟩], 18⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 13 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_12126_aux

theorem PEqualNP.Outside.L_meta_12126 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_12126_aux.wit, PEqualNP.Outside.L_meta_12126_aux.wmono, le_trans PEqualNP.Outside.L_meta_12126_aux.wsize (PEqualNP.Outside.L_meta_12126_aux.lower s hs), PEqualNP.Outside.L_meta_12126_aux.weval⟩
