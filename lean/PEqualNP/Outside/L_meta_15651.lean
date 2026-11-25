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

namespace PEqualNP.Outside.L_meta_15651_aux

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

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xe8e0e8e0c8c0c8c0e8e0e8e0c8c0c8c0e8e0e8e0c8c0c8c0e8e0e8e0c8c0c8c0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xee008800aa008800ee008800aa008800ee008800aa008800ee008800aa008800
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xeee0e8e0eac0c8c0eee0e8e0eac0c8c0eee0e8e0eac0c8c0eee0e8e0eac0c8c0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_47
def pairsG : List (Nat × Nat) := [(2, 6), (3, 7), (3, 11), (4, 6), (5, 7), (5, 37), (9, 11), (10, 11), (10, 14), (12, 14), (13, 15), (13, 45), (33, 37), (34, 38), (35, 39), (35, 43), (36, 37), (36, 38), (41, 43), (41, 45), (42, 43), (42, 46), (44, 45), (44, 46)]
def r1sG : List Nat := [2, 3, 3, 4, 5, 5, 9, 10, 10, 12, 13, 13, 33, 34, 35, 35, 36, 36, 41, 41, 42, 42, 44, 44]
def r2sG : List Nat := [6, 7, 11, 6, 7, 37, 11, 11, 14, 14, 15, 45, 37, 38, 39, 43, 37, 38, 43, 45, 43, 46, 45, 46]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [46236013234950, 48529540843045, 46236063565323]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x3b576e79
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfff0000000000000000000000000000000000000000000000000000000000000fc0fc00000000000000000000000000000000000000000000000000000000000c30e38000000000000000000000000000000000000000000000000000000000030e18700000000000000000000000000000000000000000000000000000000000cdc76
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff8200000000000000000000000000000000000000000000000000000000000fc8fc40000000000000000000000000000000000000000000000000000000000eb7f3b0000000000000000000000000000000000000000000000000000000000b6e7df00000000000000000000000000000000000000000000000000000000005ddcf6
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_47 == dom_47) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_47 goalM u ys) : RunD dom_47 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_47 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 6 := by
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

theorem low_47 : Lower dom_47 roots_47 goal_47 6 := S_47.noCircuit

namespace S_59
def pairsG : List (Nat × Nat) := [(3, 11), (9, 11), (9, 25), (10, 11), (17, 25), (19, 27), (24, 25), (26, 27), (26, 58), (35, 43), (41, 43), (41, 57), (42, 43), (42, 58), (49, 57), (50, 58), (51, 59), (56, 57), (56, 58)]
def r1sG : List Nat := [3, 9, 9, 10, 17, 19, 24, 26, 26, 35, 41, 41, 42, 42, 49, 50, 51, 56, 56]
def r2sG : List Nat := [11, 11, 25, 11, 25, 27, 25, 27, 58, 43, 43, 57, 43, 58, 57, 58, 59, 57, 58]
def mpG : Nat := 0x7ffff
def pool6G : List Nat := [46356525357323, 45192354335513]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xf0260ba
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7fe00000000000000000000000000000000000000000000000000000000000007c1f00000000000000000000000000000000000000000000000000000000000063dce000000000000000000000000000000000000000000000000000000000001b3a90000000000000000000000000000000000000000000000000000000000014e37
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7ff00000000000000000000000000000000000000000000000000000000000007e9f4000000000000000000000000000000000000000000000000000000000007ffff000000000000000000000000000000000000000000000000000000000005b7ab0000000000000000000000000000000000000000000000000000000000035eff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59 == dom_59) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_59 goalM u ys) : RunD dom_59 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_59 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_59 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59 roots_59 goal_59 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_59 goal_59 := by
    have h0 : isConstB dom_59 goal_59 = false := by decide +kernel
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

end S_59

theorem low_59 : Lower dom_59 roots_59 goal_59 6 := S_59.noCircuit

namespace S_63
def pairsG : List (Nat × Nat) := [(2, 6), (3, 7), (3, 11), (4, 6), (5, 7), (5, 37), (9, 11), (9, 25), (10, 11), (10, 14), (12, 14), (13, 15), (13, 29), (13, 45), (17, 25), (18, 22), (19, 23), (19, 27), (20, 22), (21, 23), (21, 29), (21, 53), (24, 25), (26, 27), (26, 30), (26, 58), (28, 29), (28, 30), (33, 37), (34, 38), (35, 39), (35, 43), (36, 37), (36, 38), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (49, 53), (49, 57), (50, 54), (50, 58), (51, 55), (51, 59), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [2, 3, 3, 4, 5, 5, 9, 9, 10, 10, 12, 13, 13, 13, 17, 18, 19, 19, 20, 21, 21, 21, 24, 26, 26, 26, 28, 28, 33, 34, 35, 35, 36, 36, 41, 41, 41, 42, 42, 42, 44, 44, 49, 49, 50, 50, 51, 51, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [6, 7, 11, 6, 7, 37, 11, 25, 11, 14, 14, 15, 29, 45, 25, 22, 23, 27, 22, 23, 29, 53, 25, 27, 30, 58, 29, 30, 37, 38, 39, 43, 37, 38, 43, 45, 57, 43, 46, 58, 45, 46, 53, 57, 54, 58, 55, 59, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [14552057645849, 14513134503461, 23309478333190, 66190094960186, 45192654947851, 46291378051386, 48529273329189, 14551789210405, 66190431692038, 14513048454667, 45192589220107, 38539431840518, 46437406148154, 56295077517574, 28845355107898, 28643845344025, 46236331218443, 66190178846245]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 4 => 1
  | 5 => 109
  | 6 => 717
  | 7 => 646
  | 8 => 44
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x298bdf30
  | 5, 0 => 0x91733f418f4176b689eae0ce89beb43388f7a4fc86498cae823b5ff97e01281a7ddfc3857cc18c927645deb7741116616e9c17f96b88b7446a0153b267332564661cc806647d01535f4a80325bd133a759df37c5572064cc552e2a51513775a45011ac214fadc8374d79b8ee4c2c90404ba9d394467933714594facc457a83133e57d660377d550c377c4b0134b4d5893420ed1032b8bc7b31418f212fd712a92f3bdeab2d027e762ca0f4c32a1476232952ef83282d260027caaac5248b11f0223c33ee202215df1f749daa1dd13bd91adc96db19116f4f179128230fb0432e0d213aee0ca3b5de0aed73e00966de8b0836b8a00774a41006f786ca028b8c4b
  | 5, 1 => 0xfdebe546fb393400f768c78bf71c1030ec52d795ea98dd8ee9f897d9e86dcc35e76bc468e6a53697e449d097e22d262ae182586ae1481fd6e1425ccade3631aedd1a5b1cd899566dd52671f5d1a50474ce1a23c7cba49ca0ca7b12d3c5f7428ac49223abc36c5a28c1f6bcedba346190b79dbc8cb6d6bb8eb5a82bdcb434601db0325f05ab23472da73d5e7fa2ff1743a2d483c19f86b0f49f36a4059c139ea799bd0b2a975225f296b86c5f9617042c95de1d13
  | 6, 0 => 0x12e6d71512a8906c1213c7bd1182c6e910fafe6d10ee9665108dfb000f90e7c10f856abc0eccb7400e615dc80dbee7360db0d3410da2053a0d8687440d7be6840cd408630c76b2fc0c5be1980aa50bd80a9320a80a3edfed0a07784409c80e50097f42550966de8b095e84ee08eb11d108a714d3083137aa0816162107c7e419071ebcc6070b6e2706eb193b06e4120e06a5dad806a21a9606974e47068dc3d406533b14063e36ac05ecc2ee05eb793805c54fb805810d2f0573298d0567fa510524aa2c0496165b045a056d03fe10b50390b6ab0330b353032dcf4702ef67e502d338cd02d05800027b432e023e59480135cd9e0012918d0010041b0004ac72
  | 6, 1 => 0x2b8ad2742aa184d62a4887a3298caa2529676491283a5cab27bf8f0326c8b869264570c025ccaadc254dc783241a1c8a23a42b1a22fc9bdb22725c4621f924cf21f40ce021d6d258213afd3d212acd6b203f2ac82039fdd72014b8841fe205301fbbaa661ed2190f1e8569621e68e75a1d7550671d5b97f41cb356241c0b1db81bdc203c1bb968751b30be7f1ae554351ac720e31a81704b1a61430919f7a8a219f58fc0195f86c5191a749218917f9418667dc9185ae16017db655f17912823178f9dc81788ef501783d36c1772a8cc1765f31f170095b51675fec31658ec56164cdf49153447dd1411bdaa140ca09813e889c513e23a6c13b13c8e12f06c8b
  | 6, 2 => 0x433fa33f4197cdb1417c5d42417ae7e741794a504103154f409f53bf4090fe93405380cd3ebf5c103e51fe3b3de6e0fa3d4cb9023cc117773c5d338d3c394efb3bcc4b8e3bc2caa43b9858393b5ae4283b3a508c3b1a26273a48ea8e39f45ca439aa4f6c39a6d15b39955ad5395f96ae39368b3738650d42380ca0353803efc037ff5c8b37c9a81037b7d278371fff3136e64155364134b435e35c6635e23bea35bd9f703582312935389f9734bd92e33459aef93456a4b4340c055d33bf6f8233bde23332a284ca32998b1f329818b0325dd81632008a2930bf5dbd2f4894ad2f16dd022e631e682e2316352d7eac952cfd4cb22cb09bf72c05dd8b2bf0eb49
  | 6, 3 => 0x569d4e59563267f6559b0952558acbc4557784d6554c7d9d54b428df549d984f54248837540cc15553ddd8b053b9ba0952b7de0e52138bae51a7fdc351901126515ad697514d96cf50fcb6f250e482755051ca7b4f8a3cb44f5a6fd74ed591294eb4a9274e8eef6e4e2ee3624d8edfa44d37755d4ce69ba94cd1cab54ccd68b54c7d48184c4ad1124c353f404bfbcd8a4ba07d3a4b3060ba4b014a6c4a01e9b9499b5245496afadf494735504894832747a969a6479899714762397846c1b2c8465d31f045eb319d45d63c9845701e22454771924516d08944e317154487986f4479c3844421a80f43cfd02243bdc42543b89a5d43a5743a43a4ce57439cf8a6
  | 6, 4 => 0x706fc19e6ff442ca6f043d436ee8d5556df384186d19a2926cff97826c9f13a56c5e9d666c55d0e46b74c2336aca05646a4ef8b06a145e3369c4a3f969627b62689eda76689495456821124f680a94f06700302366e4cb6d6694b153667b89e26539ae4664f83f6464ef0a7e648f1a2b648c06136452eb0d641272976303200662f60e5762d8cb5d628562b16242053b622d70af6130f73c60c081b75fc4a3aa5fae7b465f3c4a0f5f2086105f16df6a5e656a0e5e29836f5d9e8de65d915def5d4a6e025d03b9ec5c173fbb5bfa05395bdf984a5ba056165a2cc3f45a1ac1b1599395ba592a4abf58dbfe4c58d7e68458c2049758bcfd2357d8b5165773bdf3
  | 6, 5 => 0x87347efa862eae4f862295548577d885853111ac84fccbd1849fcae68498e7e7847b5ba08409e61483f66258839ce2a782e41c91827719248232a1da81ef6bed819b4b088103242c80420fc27fcf8a267f91f7df7f5b88137ee26c7b7e78e3fe7e6b005c7e3c1c8b7dd4c7e17d39201b7d380a9d7cd889d67cc86c177cc18c927c43d7c97be78f457bdfce387bb3936c7b585cdd7ae670257acc2fde7a98c0657a3b1f977a2be2bb7a2269da79cd3ffc7976ef1678fc834178b944807891b1e4788ff4d6787c201278734632776a2b53744fee3074391d8f736c3eab7361579772d87a34729330ea71fe05ed718e49e4716d6767715db15b71347e7f70fd72ea
  | 6, 6 => 0x9dccd3d09d1ecbc39cf1c6669cc4bb989c6f54319c224ca49c029e899b6995939b5bb1f19b52b2589b3c76da9af0fb9e99428cac99179fc898b5e8a79794217295ed34d6958ffed795826379952250039419aea494135e45936a0d26934f2dc49309a0c392f9ae4292b50c7c91d7069f91d301e19180cfe5915e54989129b39190d03781902d5b0c8f8431c68f1475508e8f081c8e4e62f08e26e5f78d71ad8a8ce6acb38c833b648c0b847c8ba0673b8b7565708b4987898b34a47b8b02f4388ae435ad8ad5b1988ac8737d8a7a9db88a7a9a9d8a4f9bed8a0a542789f2d53c89e9d6fb8972fedf89082d8288fcfe5588dc7bf188567ac08804873d8779fbe0
  | 6, 7 => 0xb53b688ab533f09fb40a363cb2c3a900b2a179deb2a00218b1c9a275b13c9edfb0325f05b02a2632b0167aacafedb434afc57384af81c9c5af5aa227af451055aecae8e0aeb1faadae7a07f8ae651889ae4f062dae414461ad81abe0ad818e10ad245454ac637b96ac207a85ac0d8531abe61769ab94a992ab42051eab3a3f82aaf860f8aa9e82cda9d0c5fca8fc3611a89a1b07a89118d0a826a19ea8255610a76b4f4da70aed3fa6e386d1a6768364a655fa48a5e581dda5da4240a4c46b8ca4bc745ba463c125a406231da3e292d5a32908c7a2dee76ea296fa28a22d274ca1cf4a14a0fdb8f1a08d943c9f67cab99efdaaf79ed629319e6e1c509e2dbe58
  | 6, 8 => 0xcf363de9cf2c69f5cf104267ce6a62a9cd0d9aa2cd029b64cc3c097fcb69fc21cad7f953ca011952c9ac6cdec949a14ac8bf4a13c89ff666c85246a6c82744dbc80b3e80c803b5f7c7e9128dc786c63dc7198c7bc5c9a184c582e40ac576664ec4f09b0fc4d78a53c4a941b9c4374b3ac406c3f6c360b222c2eff310c2d474bfc2c2898fc269577ec23ae89fc1fd94bec1f6bcedc1438dfbc0eb8503c0aefa8cc0a3db5dbff74d00bebd2cbbbe6de1bebe1dd4cebd47c05ebcf80b4bbc9980eebb9554cdbb3f33faba0abab5b9a1b450b9719e2ab95247afb906c6e1b8a2345fb8852f28b7e1ad33b7c8f818b792a617b75e26bbb749d50ab6187b80b541d441
  | 6, 9 => 0xe64c55b1e54da7b3e542f83be526679de4ec07f4e4e004dee4db98e8e47e070fe47777d2e460b090e4529733e3e26edde3c6f487e2fd77ace1c1513be182586ae112c699e0b0c46fe0a41ba4df9bd708df64b88bdeb9fbbcde53d5edde3eef08de3480bcdd580b4fdcc9e4eedcb029fddbc78eb0dba5c180db2c04c2db14ea86dabbd5f9d91bb4dfd8cca263d83420ded7fdf225d7eecd68d761bad8d6d828a2d6985041d67cc18dd5fbd232d5dcd35bd5881eb6d5348835d454066cd3dc1b95d3ca8f6fd2d38b51d2b65212d290422dd24b31b6d23889ebd228ce82d222218ed1b9ebe1d1adc1ced1256833d1085540d000bef7cfd29977cfa8f22ecf6ae6fb
  | 6, 10 => 0xfda5e45cfd90beb6fd76da79fd5cace3fd03f230fc9291c7fc7d7b9efc697111fc02cecffba0428cfb964055fad792e2fad3ffe0facfb439fac0f34cfa9321d7fa8559f5fa1b5c1bf9a8b337f9997546f9963cc4f943fd5ff8cfc7b4f886c02cf7f56088f760f6a9f6b5bc52f61649e1f6045146f5f4fc2af5c42351f5ad2c0ef556203ef524d273f4fbad49f4e87bcaf471a2adf421cbc3f3f7bc57f3a6e4e0f2ab5983f0cccd2aefe872aaefa703a7ef8bcdfbef6b2279ef12d323eec8be8beea08ed6ee12c54dedf3b601ec9c2465ec5ed828ec41d777eb9e1ad9eb6474eceb1a9bc8ea72c138ea45d64ae9c4d5cfe932f617e69d8a9ce68f2b45e6527f1c
  | 6, 11 => 0xffe602bdffc21017ffa3c156ff99db15ff844943ff6a265dff2ee50eff1a6c23ff0d80a2fe6faf54fe4fb680fdf4a2a0fdaefc54
  | 7, 0 => 0x14c25be7147be17a14445611141f8fdd140ddc3213ec0a3313b478a2122bc8a911f546a611c9fc59108cbea2106602d20f90e7c10f88aeee0f52f7e70ed96cbf0ecd7e060eccb7400e62c7b30e5b66e90de1f81f0db6ae630db3a33c0d359d660d31a8270c11c00d0b8bbf6b0b5d6d290a6e47250a5133e10a4a180909d69a7109c8d28f093db6800879d88b0801277907f908f707852a5a07540f080700687906e4120e06d33f7406533b140626d89105a02dba058c8cb80544cdf6052b8f990499b2c1046cf47e045a056d0451cc9a0402104d03edab4903490f6b0346c6ec02fbbdeb02f5fddb02c7e1c60218385101dd076b01c0cf2f00f26ece002f4827
  | 7, 1 => 0x2dc35a212d6782ad2cfda1512cf45da32ceb381e2cc710002cbbaac62c9d909e2b5379482b42fd002ad82ba32ad2a9b42ac299d12aa950482944441728f2496d28a5bcb426c74c0626b60929257200952563fe192538d78525029ba324f1d90e24c4815c242a74e0241a19e723bebf2123a42b1a22f2b39022d42c94225227cd21f40ce0212bd53220bd10b42039fdd71f601c511ed943511eb180c41d0c61251c91f0b51c7f660e1c1160c61c0b1db81c02e4e51b9b06e31b96e8611ae554351a1b5c1a19b15e6819728323196939d2196926bf194d07b418bc18ae18b98c20189246be1780280516ed244d169ad4dc168319a41658ec56159b56a615303b88
  | 7, 2 => 0x4667b1cb4541e848452bb7f64514c0b444aae862448b58424488eff64433319843cfd02243a4ce5742a809fe417604ab40fe68b240fd5c89409f8ab4408d44063fd89f2f3f1911403ef2c9303eca17bc3e51fe3b3e22f7d83de6e0fa3dad5fbf3d7b1e3a3cc117773ca49d893c5cd0913c394efb3c05e1c63bcc4b8e3ba453603b8c25f93aefec363a9cdd1a3a2919be3913ae5c3889bf72386dc67538495668376a4f693661bf2535e35c6635db2393358f846f35895b0434d1c21a34bd92e333ac494933513a603284d74d31dfadd331c32ec331b30d7c31740dfc315f0dca30c2219f30bf5dbd30b17a1b30a941483092a0e22ff00c9c2f474c872ee5f83b
  | 7, 3 => 0x6139bdd860c081b7608a602b6013f4555faaa4325db7a25f5d3edab75d017f515bcd8fcd5b8b47325b1760205a910ab55a0f56b159bf3e1358bcfd2357c4634856713ef9563d6c9d563a363755fdc57d55e7a0d6559741d6555e780a538ed0be537f76e65310cae852e2f8d752b23514526f455b5164663951529dc450c1bb7d509f8ca3509cfade50429db54f85907a4f2308104f1c75a54e31041e4def43ed4d37755d4d2f3c8a4d2885244cfebf194cd3f7294cae6cf64c8d80f44c50a0f34c1021324b8b4c2a4b36c4a04b0d465449d837ae49c137dd48be36e948a30f4847e5621747c09368479295b9477294e6470ecdb246e757da46d9577146cd9c50
  | 7, 4 => 0x7c3a52057b901b097b7c8fb07ac3e1087a98c06579ff8fe979fc07f679cd3ffc795af53878e4f5a278101b4377cbd182773a3b4c770282c076abcfae764d3db575d4877f75a33707739f2b397278be2071e3fb2171cfbe3471cfa26f71cce639711403f870f150466f36b6b86f1f7e7a6f014b916ee55b736d7b8cdc6cb455396c96dad26bfb0bf96bf88c416bee9c076bbf6b7e6afb3f026ad542766a9da52b6a75398c69da458569904ec9690b0d3968f8c50e6874221a686021f667e36ec2679e3ab8679b211f6722ad0067108e5267103ec5664a2e4d6608c413655e0be164bb1a68644d15206438425e63ff7f4763d8096f62a89ff762125aeb61b3740a
  | 7, 5 => 0x95546bd094ffe11f94ea215094dbd1b494acc9529492ddb29353153f93494f8992a935379244de839242763790dec3a290943691902d5b0c8f8b65ae8f0950aa8ed4acb68ea9ee8a8d8425078cc0460f8cac4f718c8c40a78c5bef5b8c0b847c8b9a7c8c8b3625d88b1d15ca8b02f4388ae474e18ac1d3288a7a9a9d895dd9a188c8f8608875e2ba878389bf86c36049868acfaf86229554861a5c8185db428985b3ccb1859d96c6857f377784fccbd184d8e40084689b4d84135e9584013fe783b31a7d8374ea7983490ab0831991368302b3d6824f20f6824ebd768130b34b8128f3f380b18522809d616c8077f7197f2d59fd7dd7bdf57db0481d7d601b88
  | 7, 6 => 0xadf62d26adf473f8ad7136f2acd99b96ac719787ac584a90aba7945fab7128a0aabb0592aa793710aa6baa8ba99d0106a9536d8da8fc3611a8aceb64a888922ba7de7870a77db8c7a64e8b36a5ef21d7a5dd0329a5cfa42ba5312b42a4d2166aa4a77657a42a80b8a4234630a3ac4ce7a32c9765a304b735a1f4e361a0e18795a0c6aa12a039bc45a022680c9e60f45a9deb9d439de491ff9dd97e959cee05e09ce2885c9ca6bdbc9c31e4e49c26fc249bea8a5f9bca85189b500dff9b4c7f429b0e75849b0132a19a31aaa699d4553f9972845b993e76f198fd6fd79839f57d97e410729794217297941ecf967edfc8966e67f096019b3795feb81b956af0e4
  | 7, 7 => 0xc82a4e78c7abb727c708d5a6c66c1ee5c629c73fc58557c3c5825014c4cca2acc3753fb4c3101f35c2d474bfc2157f87c1959e42c18ac36bc169a7a0c11b76cfc0a94172c088584ac060a091c02871dec026c9e4bff74d00bfb0bb14bf9c689bbf75efa6bf1a8222bebd2cbbbe769f18be620e8cbd15572dbc1d1430bc0e880fbb5f66ffbab4727aba47a138ba427f45ba2b822dba11faf3b9653685b8db3bf4b8b93da7b7f96484b7794bf6b749d50ab6e02c80b5e0fc76b5c668b8b49043bcb40748eeb401a675b37b151bb275c1e6b1838f47b160e5e2b158ad0fb14a7c74b0bd8805b0b62913b0b06ff8b03b1c5fafd73875af359018af0a244eae08364c
  | 7, 8 => 0xe4e004dee4386609e3412cc1e2760958e1f09bdde1df1b87e183f5d5e173acfee010dfbade53bb01ddb2f137dd44ebefdd21c15adcf66048dc07acb5dc06615adb7c6105db4ac3addb2c04c2dae1e332dabcacbbdab6ff36da067d68d982c8fbd916e5cfd80e38fad7fdd228d75bfcc7d6363344d5fbd361d5f72ec6d43a869fd35f5289d358ca24d2c7c583d2b37aa2d2925225d271ba71d24ac501d175aa0ed11892ced111535ad0bc3a17d03a22d3cff609b7cfa211b3cedaf033ce16f6e3cdef810bcd52d7cdcd0d9aa2cc3c097fcbd6d1cbcbbcb7cecb78c448cad7f953cad34aefc9d81675c9ad816cc9ac6cdec98e47ffc972257ac90dcec6c87c4895
  | 7, 9 => 0xfe3ef46efdf4a2a0fd76da79fd1304b1fcd4c3e5fcbe9363fc4e4806fbd7e007fbadfa39fab21684fa4e329afa359d84f9a8b337f92dd199f9294428f8ec2452f8a2ddc1f8037aa5f75ba0adf61649e1f46969daf3caa704f3498f0ef303c3f4f1dccc71f0a9d6b2f071128bf05ab396efb5a3deef2e9b0feee8ad45eeca28f2ee9b0dd6ee18b783ee12c54dedacebaced6973f8ece046c1ec663512ec4ae460ec01c0ebebf3dd49ebed4b1aeb5f51f7eb406b8feace13c6eac36ef1eab44034ea5d0618e9e3dfc4e9a376e3e9877a69e9430aa7e8f3ed30e8b21eaee8a202a5e78c552be7311744e72b167be6527f1ce604fcffe5f93c5de5f2c308e50d18f3
  | 7, 10 => 0xffb3f673ff1a6c23ff123350ff0a3806fee73185febb539e
  | 8, 0 => 0xfe971ab2f9554771f92dd199f61649e1ee12c54deab44034e5f2c308d43a869fc708d5a6c68acfd0c43bc065c0a94172c02871debc1d1430ba47a138b749d50ab40748eeb160e5e2b158ad0fb03b1c5fa4234630a0e187959437159c8ff96af68f8b65ae8302b3d677cbd18269904ec962a89ff75d017f514e31041e46d9577144efaef6448b58423ef2c9303e51fe3b3d084ce73ba45360358f846f242a74e0196926bf1957081117a485a0167ebc1d
  | 9, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffff00000000000000000000000000000000000000000000000000000000ffc0c0c0ffc0c0c0000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000ffffffff88888888000000000000000000000000000000000000000000000000ff008800ff008800000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee
  | 0, 1 => 0xff00aa00aa00aa00000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000aa22aa22aa22aa22000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000cccccccccccccccc00000000000000000000000000000000000000000000000055555555aaaaaaaa
  | 0, 2 => 0xccc0ccc0ccc0ccc00000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000cccc3333cccc3333000000000000000000000000000000000000000000000000c3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0000000000000000000000000000000000000000000000000cccccccc88888888000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000aaaaaaaaaa00aa00
  | 0, 3 => 0x5555555555ff55ff000000000000000000000000000000000000000000000000ff0000ffff0000ff000000000000000000000000000000000000000000000000ff00c800ff00c800000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000fff0f0f0ff000000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa00000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000333f333f333f333f
  | 0, 4 => 0xccccc0c0ccccc0c0000000000000000000000000000000000000000000000000ffc00000ffc0000000000000000000000000000000000000000000000000000000ffffff00ffffff000000000000000000000000000000000000000000000000ff00ff00aa00aa000000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000555f555f555f555f000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000aaa0aaa0aa00aa00
  | 0, 5 => 0x33333333cccccccc000000000000000000000000000000000000000000000000cc33cc33cc33cc3300000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e00000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ff00cc00ff00cc00
  | 0, 6 => 0xf8f0f8f0f8f0f8f0000000000000000000000000000000000000000000000000ffaaffaa0000000000000000000000000000000000000000000000000000000055ff55ff55ff55ff000000000000000000000000000000000000000000000000a5a5a5a5a5a5a5a5000000000000000000000000000000000000000000000000ffff0000ff000000000000000000000000000000000000000000000000000000ccccccc0ccccccc000000000000000000000000000000000000000000000000000ff00ffff00ff00000000000000000000000000000000000000000000000000f0f0f0f00f0f0f0f
  | 0, 7 => 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000ee00ee00aa00aa0000000000000000000000000000000000000000000000000055555555ffffffff000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000aaaaaaaaaaaa8888000000000000000000000000000000000000000000000000aaaa5555aaaa555500000000000000000000000000000000000000000000000000ff00ffffffffff
  | 0, 8 => 0xfaf0faf0faf0faf0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000eeaaeeaa00000000000000000000000000000000000000000000000000000000aaaaaaa0aaaaaaa0000000000000000000000000000000000000000000000000ffaaaaaa00000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ff00aa00ff00aa00
  | 0, 9 => 0x550055ffffffff00000000000000000000000000000000000000000000000033cc33cc33cc33cc000000000000000000000000000000000000000000000000aaaaaaaa55555555000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000000ff77ff00ff77ff000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000aaaaaaaa88888888000000000000000000000000000000000000000000000000ffff00000000ffff
  | 0, 10 => 0xaa55aa55aa55aa55000000000000000000000000000000000000000000000000ff000000aa000000000000000000000000000000000000000000000000000000ff00ff0000ff00ff000000000000000000000000000000000000000000000000aaaa8888aaaa888800000000000000000000000000000000000000000000000055aa55aa55aa55aa0000000000000000000000000000000000000000000000009999999999999999000000000000000000000000000000000000000000000000f00ff00ff00ff00f000000000000000000000000000000000000000000000000f0f00f0ff0f00f0f
  | 0, 11 => 0xc0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000000ff00ff55ff55ff000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000cccccccc33333333000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000eeeeeeee000000000000000000000000000000000000000000000000000000006666666666666666000000000000000000000000000000000000000000000000fff00000ff000000
  | 0, 12 => 0xfafafafafafafafa00000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000ffa0ffa000000000000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0
  | 0, 13 => 0xffffff00ffffff00000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000aaa8aaa8aaa8aaa8000000000000000000000000000000000000000000000000fffff0f0ffff00000000000000000000000000000000000000000000000000000000ffcc0000ffcc000000000000000000000000000000000000000000000000ffa0ffa0ffa0ffa000000000000000000000000000000000000000000000000000003f3f00003f3f000000000000000000000000000000000000000000000000003f003f003f003f
  | 0, 14 => 0xffff00ccffff00cc00000000000000000000000000000000000000000000000000ff00aa00ff00aa000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000ff00fff0ff00fff0000000000000000000000000000000000000000000000000ffff00ffffff00ff000000000000000000000000000000000000000000000000ffffaaaaffff0000000000000000000000000000000000000000000000000000ecececec00000000000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea
  | 0, 15 => 0xffccffccffccffcc00000000000000000000000000000000000000000000000033ff33ff33ff33ff000000000000000000000000000000000000000000000000fff0f0f000000000000000000000000000000000000000000000000000000000ff00ff00ffffffff00000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000ffccccccffcccccc000000000000000000000000000000000000000000000000ffff000fffff000f000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0
  | 1, 0 => 0xffffcc00ffffcc0000000000000000000000000000000000000000000000000000ff55ff00ff55ff000000000000000000000000000000000000000000000000f0fff0fff0fff0ff00000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000cccc0000cccc000000000000000000000000000000000000000000000000000000cc00cc00cc00cc000000000000000000000000000000000000000000000000ffff0033ffff0033
  | 1, 1 => 0xff000000ff00000000000000000000000000000000000000000000000000ff00c000ff00c000000000000000000000000000000000000000000000000000ffff00ffffff0000000000000000000000000000000000000000000000000000aaeeaaeeaaeeaaee0000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fff0fff0ff00ff00
  | 1, 2 => 0x88888888ffffffff000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa000000000000000000000000000000000000000000000000ff00ee00ff00ee00000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ff00ff00ee00ee00000000000000000000000000000000000000000000000000333033303330333000000000000000000000000000000000000000000000000000005555ffffffff
  | 1, 3 => 0xffffccccffffcccc000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000ee000000ee000000000000000000000000000000000000000000000000000000ffffffff0000cccc000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000ffffffff555555550000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000ff00fa00ff00fa00
  | 1, 4 => 0xff00ff00ff55ff550000000000000000000000000000000000000000000000000000ffff0000aaaa00000000000000000000000000000000000000000000000055555555550055000000000000000000000000000000000000000000000000000000ffaa0000ffaa000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000fe00fe00fe00fe0000000000000000000000000000000000000000000000000003030303ffffffff000000000000000000000000000000000000000000000000ccc8ccc8ccc8ccc8
  | 1, 5 => 0xffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffffffff00cc00cc000000000000000000000000000000000000000000000000000000003f3f3f3f000000000000000000000000000000000000000000000000ff33ff33ff33ff33000000000000000000000000000000000000000000000000ff00f000ff000000000000000000000000000000000000000000000000000000aaaaaaaaffffffff00000000000000000000000000000000000000000000000000000000aaaaaaaa000000000000000000000000000000000000000000000000ffffffff88008800
  | 1, 6 => 0xaa00aa00aa00aa0000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000ee00aa00ee00aa00000000000000000000000000000000000000000000000000ffffffff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000fcfcfcfcf0f0f0f0000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000ffffffff00550055
  | 1, 7 => 0x5555000055550000000000000000000000000000000000000000000000000000ffffaaaaaaaaaaaa000000000000000000000000000000000000000000000000cccfcccfcccfcccf000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000fcfcfcfccccccccc000000000000000000000000000000000000000000000000aaaaa8a8aaaaa8a8000000000000000000000000000000000000000000000000aaffaaffaaffaaff
  | 1, 8 => 0xffc0ffc0ffc0ffc000000000000000000000000000000000000000000000000000000f0fffffffff000000000000000000000000000000000000000000000000ff000000ffff0000000000000000000000000000000000000000000000000000ffff00f0ffff00f00000000000000000000000000000000000000000000000000000eeee0000eeee000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f50000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000ffff5555ffff5555
  | 1, 9 => 0xffff333300000000000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000eecceecceecceecc000000000000000000000000000000000000000000000000ffff0000ffffcccc000000000000000000000000000000000000000000000000f0f0f0f0f3f3f3f3000000000000000000000000000000000000000000000000ffffffffaa00aa00000000000000000000000000000000000000000000000000fff0fff0f0f0f0f0000000000000000000000000000000000000000000000000fff00000fff00000
  | 1, 10 => 0x11111111ffffffff0000000000000000000000000000000000000000000000000f000f000f000f00000000000000000000000000000000000000000000000000ffffffffc8c8c8c80000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000ffff0000333300000000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000ffffffff03030303
  | 1, 11 => 0xfffafffa00000000000000000000000000000000000000000000000000000000ccffccffccffccff000000000000000000000000000000000000000000000000ffffffff0a0a0a0a000000000000000000000000000000000000000000000000ff00ff00cc00cc00000000000000000000000000000000000000000000000000ff55ff55ff55ff55000000000000000000000000000000000000000000000000ffff1111ffff1111000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000f0f00000f0f00000
  | 1, 12 => 0xff00ff33ff00ff33000000000000000000000000000000000000000000000000aaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000ff00ff00ff00cc00000000000000000000000000000000000000000000000000ffffffaa00000000000000000000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000f0f0000ffff000000000000000000000000000000000000000000000000ffffffffffffcccc
  | 1, 13 => 0xffff00aaffff00aa000000000000000000000000000000000000000000000000ccccc0c0c0c0c0c0000000000000000000000000000000000000000000000000ff550000ff550000000000000000000000000000000000000000000000000000ff33ff3300000000000000000000000000000000000000000000000000000000ff00ff00ff00aa00000000000000000000000000000000000000000000000000ff11ff11ff11ff110000000000000000000000000000000000000000000000008800880088008800000000000000000000000000000000000000000000000000000f000f00ff00ff
  | 1, 14 => 0xffff0000ffff5555000000000000000000000000000000000000000000000000ffff3333ffff33330000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000aaafaaafaaafaaaf00000000000000000000000000000000000000000000000000000000fcfcfcfc000000000000000000000000000000000000000000000000ffff8800ffff8800000000000000000000000000000000000000000000000000ffffffff000f000f0000000000000000000000000000000000000000000000000000fff00000fff0
  | 1, 15 => 0xffffffff00000f0f0000000000000000000000000000000000000000000000001515151515151515000000000000000000000000000000000000000000000000ffff0000ffff00ff000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000cccccc00cccccc0000000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000aaaaaa00aaaaaa000000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c
  | 2, 0 => 0xaaaaaaaaaaffaaff000000000000000000000000000000000000000000000000ee00cc00ee00cc00000000000000000000000000000000000000000000000000ffffffff00005555000000000000000000000000000000000000000000000000fffffcfc00000000000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000ff00ff00fa00fa00000000000000000000000000000000000000000000000000000000007777777700000000000000000000000000000000000000000000000000000000fffff0f0
  | 2, 1 => 0xee00ee00ee00ee000000000000000000000000000000000000000000000000ccccccccffffffff00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ffffaaaa000000000000000000000000000000000000000000000000f5f5f5f500000000000000000000000000000000000000000000000000000000ccccccccccc0ccc0000000000000000000000000000000000000000000000000f0f0f0f0ffffffff00000000000000000000000000000000000000000000000000000000f0f0f0f0
  | 2, 2 => 0x555555550000000000000000000000000000000000000000000000000000ffff0000ff00000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa000000000000000000000000000000000000000000000000ffff0000ffffffff00000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000011ff11ff11ff11ff00000000000000000000000000000000000000000000000000ff000000ff0000
  | 2, 3 => 0xffffa0a000000000000000000000000000000000000000000000000000000000fffcfffc00000000000000000000000000000000000000000000000000000000ffaaffaaaaaaaaaa000000000000000000000000000000000000000000000000ffff0055ffff00550000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000ff00fc00ff00fc00000000000000000000000000000000000000000000000000aaaaaaaaaaa0aaa0000000000000000000000000000000000000000000000000ccccccccc8c8c8c8
  | 2, 4 => 0x2222222222222222000000000000000000000000000000000000000000000000fcf0fcf00000000000000000000000000000000000000000000000000000000000ff00cc00ff00cc0000000000000000000000000000000000000000000000000000777700007777000000000000000000000000000000000000000000000000ffffaa00ffffaa00000000000000000000000000000000000000000000000000eeeeaaaa00000000000000000000000000000000000000000000000000000000fcfcf0f000000000000000000000000000000000000000000000000000000000ffaaffaaff00ff00
  | 2, 5 => 0x33003300330033000000000000000000000000000000000000000000000000fefefefe00000000000000000000000000000000000000000000000000000000fffff0f0f0f0f0f0000000000000000000000000000000000000000000000000ccccc8c8ccccc8c8000000000000000000000000000000000000000000000000dddddddddddddddd0000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000eeeeeeeecccccccc000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbb
  | 2, 6 => 0xff330000ff330000000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c80000000000000000000000000000000000000000000000005550555055505550000000000000000000000000000000000000000000000000f3f3f3f3f3f3f3f30000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000ccccccccc0c0c0c0000000000000000000000000000000000000000000000000ff50ff50ff50ff5000000000000000000000000000000000000000000000000033333333ffffffff
  | 2, 7 => 0xffffffff50505050000000000000000000000000000000000000000000000000ffff5050ffff5050000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000ff33ff00ff33ff000000000000000000000000000000000000000000000000c0ffc0ffc0ffc0ff000000000000000000000000000000000000000000000000ffffeeee00000000000000000000000000000000000000000000000000000000ffff8888ffff0000000000000000000000000000000000000000000000000000aaaaaaaaaa88aa88
  | 2, 8 => 0xff00ff55ff00ff55000000000000000000000000000000000000000000000000c0c0c0c0ffffffff000000000000000000000000000000000000000000000000ff888888ff888888000000000000000000000000000000000000000000000000f0fff0ff00ff00ff000000000000000000000000000000000000000000000000f1f1f1f1f1f1f1f1000000000000000000000000000000000000000000000000ffffc8c8ffffc8c8000000000000000000000000000000000000000000000000fffffafa00000000000000000000000000000000000000000000000000000000000f000fffffffff
  | 2, 9 => 0xffffffff33333333000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000000000000ffaaffaa000000000000000000000000000000000000000000000000777777777777777700000000000000000000000000000000000000000000000000000000fff0fff0000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000ffeeffee000000000000000000000000000000000000000000000000000000007777777700000000
  | 2, 10 => 0xeeeeeeeeaaaaaaaa00000000000000000000000000000000000000000000000000ff00ff00aa00aa000000000000000000000000000000000000000000000000d5d5d5d5d5d5d5d50000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e00000000000000000000000000000000000000000000000000000000eeeeeeee000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000001111111111111111
  | 2, 11 => 0xfefefefefefefefe0000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000fafafafaaaaaaaaa000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000fffff000fffff000000000000000000000000000000000000000000000000000ff00f000ff00f000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000faaafaaafaaafaaa
  | 2, 12 => 0xffffffffff000000000000000000000000000000000000000000000000000000ffffffffcc00cc00000000000000000000000000000000000000000000000000ffccff00ffccff00000000000000000000000000000000000000000000000000fffffafafffffafa0000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000ffffff00ff00ff00000000000000000000000000000000000000000000000000cc88cc88cc88cc88000000000000000000000000000000000000000000000000ffffffffcccc0000
  | 2, 13 => 0xffffffffaaaa0000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000000000000000000000000000000000000000000aaaa0000aaaa000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000fffffffff0f000000000000000000000000000000000000000000000000000000000cccc0000cccc000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ffccffcccccccccc
  | 2, 14 => 0xfafaaaaafafaaaaa0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000ffccffccff00ff00000000000000000000000000000000000000000000000000cccccccccccc0000000000000000000000000000000000000000000000000000ffffa0a0ffffa0a0000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f80000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000cccccccccc00cc00
  | 2, 15 => 0xfff0ff00fff0ff00000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000ffffcccc000000000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000ffffffaaffffffaa000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000ffffffffa0a0a0a0000000000000000000000000000000000000000000000000fcfcccccfcfccccc
  | 3, 0 => 0xfffffffffff0fff0000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0000000000000000000000000000000000000000000000000fffffffff000f000000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffff0000000000
  | 3, 1 => 0xffffffffffaaffaa000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000fffcfffcfffcfffc000000000000000000000000000000000000000000000000ffffff00ffff0000000000000000000000000000000000000000000000000000ff00ff00ff000000000000000000000000000000000000000000000000000000fcccfcccfcccfccc000000000000000000000000000000000000000000000000fafafafaf0f0f0f0000000000000000000000000000000000000000000000000ffffccccffff0000
  | 3, 2 => 0xaa00aa0000000000000000000000000000000000000000000000000000000000ffffffffffccffcc000000000000000000000000000000000000000000000000fffffcfcfffffcfc0000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000fffffffffffff0f0000000000000000000000000000000000000000000000000fffffffffcfcfcfc000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa
  | 3, 3 => 0xfcfcf0f0fcfcf0f00000000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000ffffffccffffffcc000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0
  | 3, 4 => 0xffffcccccccccccc000000000000000000000000000000000000000000000000ff00ff00f000f000000000000000000000000000000000000000000000000000aaaaaaaaa0a0a0a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x180802004
  | 5, 0, 0 => 0x584402090fa81c3c010481140e1d0082408a1c0d8281204503834121a0ca81c1a010206140e0d0085c08a07010040816503828021502281c160a0a0114160a0984808a0b08804121050583c020907281c1a01048314160a0082410a07030040a045
  | 5, 0, 1 => 0x3834020910282c1401020bd40e0b008b808a0d00824342d503828582b15282c420104841406290500400a07140044e04505890020e0b281c4c010b81140e020481032a07008243425512034020907289002090708d40e0d0082444a0b1080412205
  | 5, 0, 2 => 0x580412101c281c1a3704811406020082408a0b1b004123550382c14091a282c22010805940e0d008302ca11068041210508804121011a8cc22010484140e0d008c808a0b120241c19505804120418a8080209020b54420d0085c08a0b050c012045
  | 5, 0, 3 => 0x38042e0412a92014010481140e0d238248ca0b00914123e503834020922282c8601048f940e0d0b81032a07059082e1a52090002091fa82c6c01048f9416011e8241ca0b08824201950589002091e28ec1401048e940e0a0082472a0701004002a5
  | 5, 0, 4 => 0x383456091f281c16010494d40e0b05004a4a0706804121a50382ca20902282c48010492540e0a2802408a0b008247c4f5208a0020902281c16010213941a010b8105aa0b05004124d525090020907281c04010493140e010481096a4a0500412495
  | 5, 0, 5 => 0x2d8a00209022834025a048f94420d0082434a07058280259525028260902281cb0010488140e0d0085c34a4306804123e50382c02092ba82c6c011f05944856008241ca3606804123e51b004123e11a81c040104811416550082408a410500412545
  | 5, 0, 6 => 0x7068043416505844020910282cc601048f940e0b310ac54a07068042e4c503984021702282c48130481140e0d3017c08a0b1b0247c19505804120e2f28d8ba01048f94160a0097008a0b12004120e5
  | 6, 0, 0 => 0x1c160a00824dac00039b0020902199800073283402090230000e0a00824086b60001cd40d0082408c000590c1401048118000705004120434b0000e0b00824086860001c166704918ccc00038ccca01048118000705004002c1530001621050240819600070140d3202408c00058282609020b58001c05190120411b0000e0a0082498256
  | 6, 0, 1 => 0x70160a320102cc0003828ea5f0208d8000705034027004b000060b05004120460002c14012282408c000382802090808d800073a004120411b0000e6e06804123e60001ce60104810ccc00038cc140104841800721d8280209023000160a009c4120460001c14013802446c000382c480104931800073783402092630000e6e008247c236
  | 6, 0, 2 => 0x1c160a009c02cc000382cdc011f0598000b3e00412043db000140d00824982d60001cf40d0081408c00039e41401048118000a0096858090230000e7805004081660002802092608c5ac000002c220104841400073b8041204333000c20a00824082d60001c160104810ecc00038281a752f811800070584c12043330000e0a0680412106
  | 6, 0, 3 => 0x16c14010481046c0003834020926199800070302802090230000e0104930cc2360002c14830082498c00039840209021998000b05004981616b0000e0d00824083e60002c14010b8105ac000382c1401000a9800071400412820230000e0d00824088160001c160a008402cc0003a0014010481180007059fc02043f3000167d0500412046
  | 6, 0, 4 => 0x1d1440008247ec000382c021702199800891d82812040cb0000e8806804120460001c520a008102cc002082c020902199800070583402090d3000160a00968120460001d10010481046c0003890ac010481180007438340209023000b60a06804120460001c022c3102408c000382c0209022198000705a1412044230000e0b3280412106
  | 6, 0, 5 => 0x1c16920082408c000382c1401022458000b0500412044830000e0a04810322360001c1401020591ec00038cc140902065800070523802090230000e8d00824086660016c160a008102cc000382c140104a318000706804120e1f30000e0b009302c6660001c16400082498c000382802091fa2d8000705a2002091030000007068042e045
  | 6, 0, 6 => 0x1c160a0205832c00039fc02050208d80007069800209023001360b05004120460001cc2010481408c000382c0262048118009a0582802094cb0000e0b4c004120460002c1401048109ec00039741401020598000b0500412044bb0000e9606804123e60001c16950082408c000382d100102059800940580526043330000e0a0682408196
  | 6, 0, 7 => 0x1c50010481046c000382c140908065800070582856091f30000e0b05005400460001c166e048f832c000382c040104811800074f82904040cb0013c0b10804120460001cdc5d008247cc00039941a010b81180007009893a09023000162100824086660001c160a0082434c00039fc1a01028118009c05004120411b0000e0d008240a4c6
  | 6, 0, 8 => 0x1c140d1582408c000382c140104a9580007058a002040b30000e0a158240823600194420d0082408c0003828022c04931800070589002090230000e5d00824083e60001c14010481148c00038ec500104811800a3050340209073000160a04930322d60028c14010483846c00038a01a01048118000705a880209023000160a0082408a16
  | 6, 0, 9 => 0x1d580d008102cc00038295601048118000705024081947b000160a0082554a960016c160a0481032c005402c1401048118000a06804120416b0000e0b00824085e60001c16a70082408c000382c124c0c9998000b32908120416b000140104810462d6000cc1401048105ac00038a4140902065800a305828020e0b30000e0a0082408a66
  | 6, 0, 10 => 0x2c1401020585ac00039741409020658000706ac40209023000b69f0500412046002c0160a0082408c00578281a0104811800070589002090730015e0a0082408236002b8160104810ccc000382c142b020598000b05004120456b001123b00824086660001d14280082408c0003a7c500141011800072000412041fb000163605004123e6
  | 6, 0, 11 => 0x2cdc01048f85ac004f8280282020b5800070580412b85bb0000e0b008247cb66000d8140d0082408c005782c14010205980007058056a09023000f00a00824082d6000d814010481046c005a02c0209022cd800070582802092630000e0d00824086660002c14b23202408c000380412043308d80007198041204333000160a4180412046
  | 6, 0, 12 => 0x1c160a00af408c000e02cc8090219980007059fc0a040cb001780b050041204600278220d0082408c000382c14010b8698000b051d4be0416b0000ebb06804120460002c1401048405ac004f04402090208d800070580408163330013c3308804120460002c14ba00a4c08c000382c140104ae580007059000209023000160a009c0122d6
  | 6, 0, 13 => 0x1c160104840ccc0003b2014010b8118000705b1c0217023000160a0082408c660001c160138024ccc004f02c2201020598004305034020902300014c500824082d60001d3e0141010ccc0003b100209021998000705004120461b0000e7800824086660001c160a6102582c0003b00140104afd8000b1b02802040b30017c0b05004120e6
  | 6, 0, 14 => 0x1c1a850082408c0003a28140104951800a305828120e0cb0000e0b3f8042e0460001c160a0982498c000382c5009020658000b00824986616b000166e1b004123e60000c140d0082408c00039cc1401049318002905004120416b000060a00824082360001c1a010481408c000382cea5f021998000736028020926300016c90519012046
  | 6, 0, 15 => 0x1c140d0080054c00038a40209021998005d05004120416b001980a00824082d60001c1401000a846c003e8281a01048118000b05004b4091f3000060b05004081660002d1001048105ac00039cc02040b1998009e0584402090830000e0b0532c1204600328160a008241cc00039941a01020598000b1082802090d30001401048111e2d6
  | 6, 1, 0 => 0x1c1a01020f82cc0005004b4090208d800cf0582802090230000e9f050059c0460001c160a3017c08c00250280264048118009e0580412041c3000160a09825260460001c0209021991ec0003984140104931800216402802090230000e0b00b340a0460016c160104810ccc000582812040c8b58000b1b00412041f30000e0b0780412046
  | 6, 1, 1 => 0x354160a0082408c00058440209023518000706804120469b0000ed205004081660001c16110082420c001b174140104811800070582408193330000e0b050042e4c60002cfe01028105ac002082c1401049318000706804123e2330000e0b0517c08d1600228820a008247ec0005034025a04811800072e8041204333001a00b0500412046
  | 6, 1, 2 => 0x1c14040b06446c0003b701a01048118009e0584412040cb0000e0d00988120460000c520a0082408c0003804c4090208d800076d83402092630000eda05004120460001db20a6c0102cc000582802090235d80094058280293263000820b20004120460001c1a0104811acc00058d81409020658000b05004b4040b30000e1b0500412046
  | 6, 1, 3 => 0x2c142b048105ac0005b7c140104811800073283412040cb0000e2905004002a60001c1601310102cc00039281401020598000b12004c8090230000e7306804120460001c16016f01102c0005884140104931800070503402090d30000e0b32908121a60001c14010486846c006e82c140902065800070503408160cb000162800824082d6
  | 6, 1, 4 => 0x1c480d0082408c000382d8e010205980007058ac12043330000e2400824082360002cc60a0082408c0005828c80902389800a30582802091e30000e0a0082408e160028c160104838ccc0003b1c1a01048118000732b208409023000060b05024081960001d8e010481046c000382c14010d059800e01d82802090230000e730481032666
  | 6, 1, 5 => 0x1c1a0104811d2c000382c0209023a18000705b9c02090230000e0b0500412e660001c1ae50082408c000382c140104831800070582802091d3000160104810cc2d60001c1a09020f832c006c96c14d8048118000705b9002090230000e7305004120460001c160a000a832c000382802040b095800e30582802090230000ec80500408166
  | 6, 1, 6 => 0x224760a0082498c0005828b409020658000b0504426090230015e0b00824086660001c1a0104810fcc000382dd60104811800410500412041fb0000e0b12004081660001cde0d008102cc0003994020902095800070583402170230000e0a01004120460001c1a010297c08c00039dc1401048118000705ba80209023000000b1b004123e5
  | 6, 1, 7 => 0x3c4160a0082408c00058d8020902199800070503402092630000e0b32908124c60001c1a01000247cc000382802092608d800070500412047830000e3305004124c60001dde0104810ccc000503506010481180e0b0500412ee023800140d008102c2d60002906010481046c00050040816118b58000776828020926300016ec0500412046
  | 6, 1, 8 => 0x1c16620481032c00398041204330b5800070582802097a30000e0102058cc23600104160a0082408c000390002090208d800072502812040cb000160a41804081660001d3e0a0089c08c000380412041f095800076400412041f3000160a0082408f36001941a01048105ac00038a4040104811800076389802090230000ef20500412046
  | 6, 1, 9 => 0x1cf00a0082498c004a02c140149811800070680412047cb0000e0b0502408f860001dee0a0082408c000382c14090d0658001c05828c8092630000e8d05004120460001dec0a00811eac000382c1401020618000705828024c0b30000e0d008102c6660001c800d0082408c00038340209020698000745028023f0b30000e0b050042e046
  | 6, 1, 10 => 0x1c1409020644ac000382c140104bf9800076402812040cb0000e0b051d4be4c60001dfa0a0082408c000680412041f0b580003058041204333000160a00800542d60002c14754197c08c000382c8409023f1800070680412fb0230000e9f05005044c60001db60d0082408c0003829b009023e9800070590002040b30000e0b05000562a6
  | 6, 1, 11 => 0x1c166e008246ac000382e04010481180007010041204153000160a12004120e60002c14010481202c0051928140104839800d905360120416b0000e0b12024081960001cde0d0481032c000382c020015199800070582802091130000e0d00814081660002c14010481200c007f82c1401048118000b05168560902300016210500412046
  | 6, 1, 12 => 0x2c0262048105ac000382d100104931800076cb601204333000940a00824082d60001c1a470082408c0005804b4090219980007059885609023001280b0504d260460001c1401049311ec002d82c1401049318000a06824081916b000140902064462d600414160a0082408c008202c14010481180007148280209263000760a0082409036
  | 6, 1, 13 => 0x1c1401160102cc000582a160104931800cf0582802040b30000e0b05024981960001c160a00c2808c000383412040c9998000b05004121a16b0000e8a050247e1960001c12040c99846c000582a1209024218000b0520c12040cb000160a02058322d60001c160a008260ec000382c020946199800072e82802092630000e0b00c1812046
  | 6, 1, 14 => 0x2c14830497c08c000382d58010244980007058102c193330000e0b00824091160001c16400481032c0003a20b0010481180007398041204883001460b12004120e6002b8160a0082408c000382c02090243d80003058280200153001460b05004124960001c940104810ccc0005828030e024358000b050041204863000940a00824080e6
  | 6, 1, 15 => 0x1c171a0082408c00378340209020b5800070582802098cb0000e9f20004120460001c160a00c6008c000582802090745d800070582802091030000e0a0082409166000000e0d0082434a000382c02090d19980007058062a091f30000e0b3f8040a4c6000280209020945ac008a02802090244d800c805004120416b00016c700824082d6
  | 6, 2, 0 => 0x2c14010016854c0005c80220104811800942502802090230000e0b14004124c60047c160a0082408c0005c781401048118000b1082802170230000e0b8e804123e600224b60a0082408c0003834120502065800070082408253330000f1c05004120460001d900104810ccc000382c1401020598000705b6c02098db000162400824082d6
  | 6, 2, 1 => 0x1c167a0081408c00068041204330b5800070504c120411b001140a008247e2d6000000e020082408a00008240866118b5800070582802320230000e0b050ac124c60016c1401048107ec000382c14010484180007059b802091f30000e6506804121a60001c140d338248cc000582a420104811800070519c124611b000162400824080e6
  | 6, 2, 2 => 0x2bc160a0082498c000382c02090249580007050b012040cb0000e7305004081660001c0209028104ac00039b014010205980007058047a090230000e0b00800c42a60001c14010481248c0003c8c1a01048118000b050440209083000160a00c88120460001c160a339182cc00038281a130481180007068041217023000160a00824982d6
  | 6, 2, 3 => 0x1c1a0902065acc000582a4c01048118006c1d8280209023000163605004124c60001c1401048111ec0005804b462048118005b058280209023001280b12004120460001c160104930ccc0003a2802091f999800071482802090230000e0b0504c081660002d060104810ccc000382c1401060598000b008102c6616b000164000824082d6
  | 6, 2, 4 => 0x1c160a00cb008c00038281a010b8118000705004981611b000163b0504c1204600104140d0082408c004f02c220104931800070599484170230000e610500408166000340209028105ac000382802170208d8004105004120411b0000ecc05004120460001c160a00cae54c00058280329498118000b7602802040b30000e0b0500651276
  | 6, 2, 5 => 0x1b0b60a0082408c00039941a0104931800070582802090fb000820b050040816600250140d00a4c08c000382c14370481180007329840209023001280a00a4c082360001c1696008247cc000382d8e01028118000b08804120e1f3000160a85804120460001c1636008247cc0003b645001048118000b4404402090230000e0a0680498166
  | 6, 2, 6 => 0x1c160a008266ac000382c1534024cd8000b0519013320230000e0a160ac1204600084140d0082408c00059944242048118000705cc40209263000420a008240823600250160a0081260c000382c0205024bd8000b054b802090230025a0b051901204600270160a0082408c000182c14010493180007059fc02050230000e730082498666
  | 6, 2, 7 => 0x2e3a0a008241cc00058841401020598000b04810326616b0000e0b00826760460001d900a0082434c000382c5001048118013a058280209023000161100824081060001ce60a0481032c0003ce41401048118000706804123e2630000e0b05004133860001e6e0a008102cc000382c1401004d98000a008b0120416b000000b12004120e5
  | 6, 2, 8 => 0x1c1a01048106ac00058280209020b58013f0582802092630000f3e05004124c600250160a0084808c0003b6414d804931800070500504049eb001940b08804120460002c14012d02498c000382c0209024f1800075603402090230000e0116024086660001c16010b8107cc00038340209023f180007250900209023001460b05004120e6
  | 6, 2, 9 => 0x1e8a0a0082408c002082c1409020658000705804c4092630000e0b90004123e60001c1a01048116ec00039281401049318000705d10020902302c760a00ca4120470001c160aa182408c00038281a092606580007a102802090230000e0a049303223600504160a0082408c0005828020902501800073082812040cb001460b0504c12046
  | 6, 2, 10 => 0xec14010481294c000382cd401048f98000b1b02802090230013e4105004120460002e920a0082408c00058280209025218000705d1c02090230000e6506908120460001dde0a0082408c000399484090208d800070582898160cb0000e0b00824086660001cfe610081408c00058280209a30118000b1080412041f30000e0b0505c08196
  | 6, 2, 11 => 0x2d10210082408c00038cc1401020598009e0584402090230000e0b0511c124660002c140149812a2c00360280209020b5800940582803320230000e0b05004124460001c160a008aaa0c00a782c1401025398000b050041204a6b001280b0524c081960001c160a0080298c0005828ce09230b58000b050041204a5b001123b0500408166
  | 6, 2, 12 => 0x160a00d5c120e60001c160104812acc000382c1401aa825800076402802092630000e0b63804124c600374160a0082408c000382c140902551800070503402040b3000160a00824095360001c1665210102cc00398280209020b58000705004081611b0000e0b050248d526
  | 7, 0, 0 => 0x382c14010205a9ce07ad82c140104811c000732834020902301c166500824086670382c155a0082408e89038281a0104811c160a08804c80902381c160a00826b20470382c15580082408e07058280209023e5d120705004120411b81c140d00800120470382c1401048122ee9e0382c140102059c0e0a00800120411bd3c0e0b0500408167
  | 7, 0, 1 => 0x382c14010481294e079682c140104811c0e0a06804120502381c160a008000816703b64140d0082408e0b0500412041f0b5c0e0a008240a0411ba780e0b32804120470000c160a0082408c076c82802090208dc000739804120433301c160a00825f60474481c760a0082408e073f984140104811c0e0b6d828020902381c160a3380400097
  | 7, 0, 2 => 0x39bc160a0481032e000382c1401000a980e0b050040a040b381c140d009081204703b64160a008102ce0705804120433205c0e0a08804120411b81c140121024082370382c140104cc808e07058280209022a5c0e0b0502526040cb81c160aae804120474f01c160a0082420ea30382c140104931eb807058280209023a240e0b0500408167
  | 7, 0, 3 => 0x382c1411008102ce0b05005b009020b5c0e0b0500484040b381c160aaf8041204705828ce01048105ae0705828020902125c0e9f0582802092638700e0b05190120470382c1401020fc2ce0705828020926065c0e0b052e8020902381c166e05004124c70001c1a01048107cc070580412041f199c0e0b050041204af381c14110680412047
  | 7, 0, 4 => 0x39e8140d0082408e070582802092f931c0e0b05004136102381c160a0082408d470382c14010481098e0705828020915131c0e0b05004133602382c1401048108c2d703a281401048107ee0003b6414d80481180e0b050041204a9381c160a2380412047b001c160a0082408e0005828025a0481180e0b05004120495381ce40b0500412047
  | 7, 0, 5 => 0x1c160a0205832c0705828020902449c0e0b0082408463338000e0b00988120460001c940a0082408c07058041205020f9d3c070582812040cb81ec80b05004120470382c140104812c6e0705805b00902199c0e0b3380412043338000e0a06824081960382c140902064cce07058280209260b5c0f620582802090238000e0a0481032236
  | 7, 0, 6 => 0x3782c1401048105ae890382c140902065ecc0705828020902381c17650500412047058280209498105ae07058440209020f9c0e5b05828020902381c160a00024081975a01c160a0082408e074502c140104811c0e0b00824086659b81c160a00824083870001c160a0082434c0705828020907131db25b05828020902381cf00b0500412047
  | 7, 0, 7 => 0xe01c140d0082408e0705804129302199c0e0b050062a0902381c160a00824096a70382ed20a0082408e0705da0140104811c160a0082526040738700e0a00824082370382c14090281032e00038280209020958000764028020902301db20b05024081970001c16c70082408c0705828020926265ece0705034020902381c160a0082409277
  | 7, 0, 8 => 0xe01c160a008102ce070582802090223dc0e7f05034020902381c166505004121a74a01c160a0082498e0705828220902065c0f6c05034020902381cfe0a0082408237b581c160a0082408e000382c4801048118000737834020902301cde0b00824086670382c14010481298e071482c140104811c0ed94f828020902381c160a048107e197
  | 7, 0, 9 => 0x4a02c140104a4c08f6f0382c140104811edc0705828020902381c160a0082408fa703995900a0082408e9e058280209020b5c0e0b3f82802040b381e460b05004120470382c1401049302ce070582802090b811c000a06804120416b02c140104810cc2d75181c160a0082408e0705c74140104811c0e0b050041204b6b800140104810462d6
  | 7, 0, 10 => 0x3828ea010481046ea30382c140104839c0e9f05828020902382c140100024082d70001c160a0082498c07058280209b8011c000706804120433301c16653f804120470001d140a008247ec000380412043308d80e0b050005609023a680e0b05004124c70002c14830082408c07059f0140104811c000b05004081616b01c166e0500412047
  | 7, 0, 11 => 0x38281a013202408e0705004c8090208dc160a008240a0416ba28820b05004120476c82c1401048105ae07058280209020a9c0e0b054d00209023c50160a00824082d70001c160102058ccc000382c80010481180e0b0502408196b381d800b05004124c7038281a750082408e07058280209025c5d120b05004120416ba780e0b0082408667
  | 7, 0, 12 => 0x5781c160a0082408e0b050440209020b5c0e0b050041204bb382c140121024082d70382eea0a0082408e07058280209ba011c160a00824083f16ba240e0b00824086670382c02de04810cce07b982c140104811c160a00c38120416b81c160ab9004120470382c1401410102ce0705828ea0102059c0e0b05004120416b81c16010002408667
  | 7, 0, 13 => 0x382ef40a0082408e1c0382c140902065ef20705828020902381c160a61004124c70382c1401ab82408e0705828020926305c0e0b05004120407381c160a00824087b70001c1a010481408c0705804120502199c0e0b055e0020902382c140104aa8082d70382c15770082408e076c82c020902199c0e0b32828020926381c160a0099008167
  | 7, 0, 14 => 0x382c140104812f8e9e0382c220104811c0e0b05004120486b81c140104810475e70382c14010481132e0b1d828026404811c0e0b3f82812040cb81c161100824086670382d2c0a0082408e0705804840902199c160a08804120407381ef60b05004120470382c6c0a0082408e0705828ce0902119c0e0b42804120433381c1601048107e667
  | 7, 0, 15 => 0x38281a010481098e000382c12040c999b020705828020902381c140104810982370181c160a0082408e0705ab0140104811c00070500458090232500e0b050041204703e00160a0082408e0705dfc140104811c0e0bbf028020902381c160a0082498bf70382c140104811f8e07be82c140104811c000b05024081916b01c160a008247c4c7
  | 7, 1, 0 => 0x382c14010205a66e9a0382c140104811c0e0b05004084c0b381c163b05004081670582802002d02408e0705828020902609c0e0b00825700433381c160a06804081670382c14016c02498e0705828ce0104931c0e0b05004081611b81c160a04a08081970382c14750481032e0705828020902059c0e0b0500412041aba50160a0880412047
  | 7, 1, 1 => 0x39cc160104810cce07450281a0104811c0e0b32828840902381c160a84804120470382c14750497c08f830382c140104811c0e8a05004120411b81c166506804120470e02c1401048105ae0705829640104811c000705828020902301c160104810cc8470382c14010491898e074f828020941011c0e0b050059a0902381c160a0082408b77
  | 7, 1, 2 => 0x382c1a01048107ce0705828020949931c0e0a008240823b538700e0b008240866703a28160a008102cea305828026404811c0e0b900280209023870160a00824080e7c201c160a0082408e0705804006204811c167f05004120416b81c160a00968120474a01c160a0982408e070582802040b449c0e0b0500412049eb81d800b0500412047
  | 7, 1, 3 => 0x5181c14010481046e000382c14130481180e0a008240823b6b81c160a61004120470002c0209021985ac07059b81401048f9c0e0a00824082347b8000e7305004120460382d920a0082408e073782c140104931c000736028020902301c166505004120470382cfe0104810cce07059a8140104811c0e0b05004081693b8000e0b0519c12466
  | 7, 1, 4 => 0x382802090206446e07370281a0104811d46070582802040b382c140132024082d70382c1401048107ce073702802090208dc0e0b0503412040cb81c160a00824088170382c14090206446e0705828020902615c3894058280209023b800e0b05004120470382c14019582498e0b050041282020b5c160a3a804120416ba8c0e0a0680412047
  | 7, 1, 5 => 0x4f01c160a0082498e074f8ec140104811c0e8705828020902381d3e0a06804120470382cfe010481408e00038281a010493180e0b05004124c33381c160104a08086670382cea0104810cce074f82802090208dc0e0b05004124c8db8000e0a0082498236038281a010481032e000398414010481180e0b05024084c0cb81c163b0502408197
  | 7, 1, 6 => 0x3a28160a0481032e07050340209020b5c0e0a00824082316b81c140d00824be04703a7c160a008102ce07058280209070f9c0e0a0680412041538000e0b05004981660382802092f81046e070500412041508dc0e0b0099012043338000e0b050042e0460382d100a0082408e070582802040b065c004105828020902301c166e0500408167
  | 7, 1, 7 => 0xc381c160a0082408e0705829060104811c0ed905828020926381c1401048101c2370382c14600082408e070582802040b0b5c0e0b050070c0902381d3e8a05004120470382c14012f8102ce0705828020415059c0e0b054d002040b3a240e0b05004124c7058280209020b552e004a02c14014981180e0b0519c020902381c160a00800124c7
  | 7, 1, 8 => 0x382c14010481020e0b050041204118b5c0e0b05004e00902381c166e00824083e703e20160a0082408e070599414010b811c0e0b05004123f26381c160a008259c0470382c140104811a2e000588414010481180e0b05004120459b81c160a00826500470382cfe0a0081408e0705034020902039c0ebe05828020902381c160a008240a4c7
  | 7, 1, 9 => 0x382c140104811c4ea30382c140902065c0e0b050a0020902381f180b0500412047058280209021305ae070582b160104811c163b05004120416b82c1401048105b1370382c158a0082408e0705828032904811c0e0b05624020902382c140d00824082d70382c1401020382ce0705828220104931c0e9605034020902381c160a00908124c7
  | 7, 1, 10 => 0x382c140102059eae0705828020902541c0e0b3702812040cb81c160104810986670382c760104810cce0b32884140104811c163b050041204073a500e0a0680412047038a414010481054e0705834020902199c0e6f058280209023a500e0a0082408237039b8ba0a0082408e070580412043308dd940705828020902381c160a0082526047
  | 7, 1, 11 => 0x382802001602408e077b02c140104811c0e0b05004120481b801123b05004120464481db20a0082408e0705e38140104811c0e0b050240819b8b81c16ac05004081674a01c160a008102ce0705034020902059c0e0b05006560902381d3e0b05024081970382802090205846e000382c1409260659140b05004120416b81c178d0500412047
  | 7, 1, 12 => 0x4f01c160a0082408e94058ec140104811c0e0b068041205023d3c0e0b05004120470382c1409020645ae00038281a010481180e0b050041204333ad00e0b00824086670382c14010481236e000382cca420481180e8a0580412043338000e0a00824082360001c660a0082408c0705828120415065c0e0b052c40209023e3c0e0b0500412047
  | 7, 1, 13 => 0x382c14016f02408e1c0382c140104931c0e0b05004000902381d3e0b14004120470382c14010002454ea3058280209020b5c001c05828c80902301c160a048101c1974f02c14110082408e075d82c140104811f22070582802090238000e0b05004081660382c1401048129ce070582812040cdd9c0e0b05007200902381db20a00824083f7
  | 7, 1, 14 => 0x382c14010481408e0b3e0280209020b5c000705828ea5f02301db20b0500412047059b81401048105ae000382c14010484180f1405828020902381cca0a06804120470382cfe0a0082498e000382c14013802580007059b802091f301cca0a00824082370382c1401048116ce0003a7c140141011912070582802090238000e780500412046
  | 7, 1, 15 => 0x382cdc0104810cce940382c140902065c0e0b05044020902381f260b05004120470382c14010489c08e0705994140102059f240705828020902381c160a42804120474f82c1401048105ae0705828030e04811c000b05004124c16b28c0e0b0082408667039cc140104810cce0b0500412040c8b5d460b05004120407381c160a04810337c7
  | 7, 2, 0 => 0x382c14750082498e070582812040b065c000705004120447b000b60b050041204605828ea830082408e0b370d8140104811c0e9f0580412043338000e0b0082498666038281a01048107ce0705828020902545c0e0a00824083e11b8000e2905004120460382c020902064cce0b05004125f020b5c160a00824082a16b81c160a0082554047
  | 7, 2, 1 => 0x382c0209021985ae0705828026404931f2c0705828020902382c1401048101c2d70382c1401048f88ce0b050041204169edc0e0b3d028020902381c16010497c086670001cba0a0082408c0705804120415199c0e0b05004083e0b3a51460b050041204703e54160a0082408e000382d10010481180e0b050240819ca381c160a00825044c7
  | 7, 2, 2 => 0x382c14013102408e07058280209020f1c0007059fc020502301c1401048108c237058280209020b61ae0705804120407199c0e0b6d828020926381c160a00825700470382c1401048132ee0705828020902151c0e0b0500412046b381c140d338041204703828ce010481046e07059940209020f9c0e0b05004120469b8000e0b0502408196
  | 7, 2, 3 => 0x1c16280082408c0705828032802059c0e4105828020902381c166505024081970382c1401021182ce03058280209020a9d280b05004120416bd9c0e0b0500412047039cc160a0082408e073602c140104811c0e0b05005b0040b381c160a338040816705828026404a4c08e070582b300104811c0e0a06804120423381c160a6e00412047
  | 7, 2, 4 => 0x382c14010493254e07058280200020a9c0e0bb60280209023a500e0b00824086670382f380a0082408e940382c140149811c0e0a06804129302381c160a00e6c120470382802094981046e070582b340104811c160a00824081616b801460b05004120e60382d8e0a0082408e0705828020902665c380705828020902381c160104810cd107
  | 7, 2, 5 => 0x382c1401498102ce07058ec140104931c000b05004120416b01c160a048107c1970382802090208f3ce07058280209024bdc0e0b05034020926381f3a0b05004120470382c14240082408e07378281a0104811c000705828560902328c0e4a05004120470382c14010493046e073782802090208dc160a00824082d84381c167f0500412047
  | 7, 2, 6 => 0x382c1401000247ce070500412043308dc0e0b050041204d038000e0b00824086660382c0209021996ee070582b3e0104811c00af05828020902301c160a00824087e7039bc160a008102ce070582802052f811c160a84804120416b81c162105004120470382c140104811d2e070580412040b199c0e0b05004120498381c160a7280412047
  | 7, 2, 7 => 0x3a2816400082408e000382802040b08d8009e05844020902301c160a00824240470382c15a10082408ea30382c480104811c166505004120416ba780e0a068041204703bd8160a008102ce9e0382802090208dd3c0719828020902381c160a33824081970002c6c0a0082408c0705828ea0104811c0e0a06804120433381d140b05004124c7
  | 7, 2, 8 => 0xfa20582802090238000e0a06804081660382c140102058cce070582802090222dc0e0b05100020902381c160a00824081a7
  | 8, 0, 0 => 0x382c1401048102ce940382c140104811c0e0b05004120407381c160a00824082d70382c14010497c08e07058280209020a9c0e9f0582802090238000e0b05004124c60382c14010481032e07059b8140104811d460705828020902381d140b05004120470382c14010481098e07058ec140104811c0e0b05034020902381c160a0082408237
  | 8, 0, 1 => 0x3b64160a0082408e890382c140104811c0e0b0500400090238000e0b05004081664f01c160a0082408e00038281a010481180e0b0500412043338000e0a0082408236039bc160a0082408e0705828020949811c0e0b05004120423381c160a00b60120470382c14670082408e07058280209020f9c0e0b3282802090238000e0b0500412046
  | 8, 0, 2 => 0x382c14013202408e0705828020941011c0e0b051d402090238000e0b00824086660002c1401048105ac07059fc140104811c38070582802090238000e0b05024081960382c14110082408e0705828024204811c0e0b0500412041fb81c160a008240a047
  | 9, 0, 0 => 0xe0b0500412046
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 40
  | 5 => 49
  | 6 => 67
  | 7 => 67
  | 8 => 67
  | 9 => 58
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 9 0) :: stateWires n (ids >>> 9)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3ffffff0000000000000000000000000000000000000000000000000000000003c00000fc00000000000000000000000000000000000000000000000000000000000e0038003000000000000000000000000000000000000000000000000000000cc1cd03b78f6000000000000000000000000000000000000000000000000003ffffff0030006000000000000000000000000000000000000000000000000003c00000fc00000000000000000000000000000000000000000000000000000003303030c3c3c380000000000000000000000000000000000000000000000000000fcfcf3bbfbf7
  | 0, 1 => 0x3c001c000038c00000000000000000000000000000000000000000000000000000cc1cd0000000000000000000000000000000000000000000000000000000003c00000fc0000000000000000000000000000000000000000000000000000000000c1c103878f0000000000000000000000000000000000000000000000000003ffc000fffc000000000000000000000000000000000000000000000000000003c03fc0fc03fc00000000000000000000000000000000000000000000000000000f0e0e3838307000000000000000000000000000000000000000000000000003f33e3203b78f6
  | 0, 2 => 0xe003800300000000000000000000000000000000000000000000000000003f0f1f1c7c7cf80000000000000000000000000000000000000000000000000000f31f1383bcf8000000000000000000000000000000000000000000000000000c0c1c104040c000000000000000000000000000000000000000000000000000330303000000000000000000000000000000000000000000000000000000000000f0e0e0030006000000000000000000000000000000000000000000000000003c03fc000000000000000000000000000000000000000000000000000000000000cc1cd00038c0
  | 0, 3 => 0x3f33e32fffc73f000000000000000000000000000000000000000000000000003c0003ffc0003f000000000000000000000000000000000000000000000000003c00000fc00000000000000000000000000000000000000000000000000000003ffffffc3c3c38000000000000000000000000000000000000000000000000003f03030fc000000000000000000000000000000000000000000000000000000000001c003838f0000000000000000000000000000000000000000000000000000cfcfcf3c3c3c7000000000000000000000000000000000000000000000000003fff1ffc7ffcff
  | 0, 4 => 0xf00003838000000000000000000000000000000000000000000000000000003c00000fc000000000000000000000000000000000000000000000000000000003fffff03fffff000000000000000000000000000000000000000000000000003c03fc000038c0000000000000000000000000000000000000000000000000000003fff0003fff000000000000000000000000000000000000000000000000003fffe3ffc7c70f000000000000000000000000000000000000000000000000003f03ff000000000000000000000000000000000000000000000000000000000000001c000038c0
  | 0, 5 => 0x3f0f1f1383830700000000000000000000000000000000000000000000000000030ce313bc4338000000000000000000000000000000000000000000000000000000000fffffff0000000000000000000000000000000000000000000000000000fc0003bbc00000000000000000000000000000000000000000000000000000000000003838300000000000000000000000000000000000000000000000000000c000c0030006000000000000000000000000000000000000000000000000003ffc00cfffc006000000000000000000000000000000000000000000000000003c00e00fc00300
  | 0, 6 => 0x3303030c3c3c38000000000000000000000000000000000000000000000000003ccffcd0000000000000000000000000000000000000000000000000000000003fffe3ffffc73f000000000000000000000000000000000000000000000000000c30e023f8bb31000000000000000000000000000000000000000000000000003ffc000fc000000000000000000000000000000000000000000000000000000000f0e0038383000000000000000000000000000000000000000000000000000003fc03ffc03fc00000000000000000000000000000000000000000000000000033030303c3c3c7
  | 0, 7 => 0xcc00003b40000000000000000000000000000000000000000000000000000000001c000038c0000000000000000000000000000000000000000000000000000000fc000038c0000000000000000000000000000000000000000000000000003f33e32fffffff000000000000000000000000000000000000000000000000003ffc00000000000000000000000000000000000000000000000000000000000000cc1cd03b40060000000000000000000000000000000000000000000000000000cfe3203b47090000000000000000000000000000000000000000000000000003fc03ffffffff
  | 0, 8 => 0x33031f0c3c3cf800000000000000000000000000000000000000000000000000000000003838300000000000000000000000000000000000000000000000000000ccfcd00000000000000000000000000000000000000000000000000000000000cc1c003b78f0000000000000000000000000000000000000000000000000003ccc1cd0000000000000000000000000000000000000000000000000000000003003000c003c00000000000000000000000000000000000000000000000000003ffc1cd0000000000000000000000000000000000000000000000000000000003c001c0fc038c0
  | 0, 9 => 0x330032fffffff000000000000000000000000000000000000000000000000003cf31cec43bcc70000000000000000000000000000000000000000000000000000cc1cdfc48709000000000000000000000000000000000000000000000000003f33e32fc487090000000000000000000000000000000000000000000000000003fffff03fffff000000000000000000000000000000000000000000000000003ffc00003b40000000000000000000000000000000000000000000000000000000cc1cd0030006000000000000000000000000000000000000000000000000003ffc0000003fff
  | 0, 10 => 0x3301f2004b8c9000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000003c03fc003fc03f0000000000000000000000000000000000000000000000000000cc00c03b4006000000000000000000000000000000000000000000000000003ccfe0dffb4736000000000000000000000000000000000000000000000000003fc303cc47040e0000000000000000000000000000000000000000000000000030ff00fc03fc07000000000000000000000000000000000000000000000000003300fcfc3c03c7
  | 0, 11 => 0x3fc03ffffc73f000000000000000000000000000000000000000000000000003ccc000ffb40000000000000000000000000000000000000000000000000000000f0e0ec7c7cf8000000000000000000000000000000000000000000000000003fff03000000000000000000000000000000000000000000000000000000000000fcfcf000000000000000000000000000000000000000000000000000000000003cfc33b8fbf1000000000000000000000000000000000000000000000000003f00000fc00000
  | 0, 12 => 0x33cf1fdc3f7cfe0000000000000000000000000000000000000000000000000003fc03f03fc03f000000000000000000000000000000000000000000000000003f03ff0ffc3ff80000000000000000000000000000000000000000000000000033030300000000000000000000000000000000000000000000000000000000003c03fc00000000000000000000000000000000000000000000000000000000000000fc03803bc0000000000000000000000000000000000000000000000000003cf0000fc38000000000000000000000000000000000000000000000000000003303e30fbc3f38
  | 0, 13 => 0x3ffffc0fffffc0000000000000000000000000000000000000000000000000003ccffcdffb7ff60000000000000000000000000000000000000000000000000000c01cc03b38f6000000000000000000000000000000000000000000000000003fff030fffc000000000000000000000000000000000000000000000000000000003fce0003fc7000000000000000000000000000000000000000000000000003c03fc0ff83ff0000000000000000000000000000000000000000000000000000003fff0003fff0000000000000000000000000000000000000000000000000003fc03f03fc03f
  | 0, 14 => 0x3ffc00efffc0070000000000000000000000000000000000000000000000000003fc00d03fc0360000000000000000000000000000000000000000000000000033f3e3efbfbf3f000000000000000000000000000000000000000000000000003c03ff0fc03ff8000000000000000000000000000000000000000000000000003ffc03ffffc03f000000000000000000000000000000000000000000000000003ffc1cdfffc0000000000000000000000000000000000000000000000000000000f0e0e00000000000000000000000000000000000000000000000000000000000cc1cd03b78f6
  | 0, 15 => 0x3cf3fcefc3bfc7000000000000000000000000000000000000000000000000003fff1ffc7ffcff000000000000000000000000000000000000000000000000003f030300000000000000000000000000000000000000000000000000000000003c03fc0fffffff000000000000000000000000000000000000000000000000000000000fc03fc0000000000000000000000000000000000000000000000000003cf0e0efc38307000000000000000000000000000000000000000000000000003ffc00ffffc007000000000000000000000000000000000000000000000000003ffc000fffc000
  | 1, 0 => 0x3ffce00fffc3000000000000000000000000000000000000000000000000000003ffe3f03fc73f0000000000000000000000000000000000000000000000000033ff03fc3ffc3f00000000000000000000000000000000000000000000000000030003003c00380000000000000000000000000000000000000000000000000033f3e3e00000000000000000000000000000000000000000000000000000000000f000038380000000000000000000000000000000000000000000000000000000f000e0038007000000000000000000000000000000000000000000000000003ffc031fffc038
  | 1, 1 => 0x3fc00003fc0000000000000000000000000000000000000000000000000003c00000fc00000000000000000000000000000000000000000000000000000003ffc03ffffc0000000000000000000000000000000000000000000000000000000fc1cf03bf8f7000000000000000000000000000000000000000000000000000003e320000709000000000000000000000000000000000000000000000000003ffc1cdffff8f6000000000000000000000000000000000000000000000000003fffffffffc000000000000000000000000000000000000000000000000000003f03ff0fc03fc0
  | 1, 2 => 0xc000cfffffff000000000000000000000000000000000000000000000000003ccc1cdffb78f6000000000000000000000000000000000000000000000000003c00fc0fc03bc0000000000000000000000000000000000000000000000000003ffffff38383070000000000000000000000000000000000000000000000000000f0e0e0000000000000000000000000000000000000000000000000000000003c03fc03803bc0000000000000000000000000000000000000000000000000003f031f0c7c3cf8000000000000000000000000000000000000000000000000000003e32fffffff
  | 1, 3 => 0x3ffce0efffc307000000000000000000000000000000000000000000000000003fffffffc03fc00000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000003ffffff0000307000000000000000000000000000000000000000000000000003ffffffc440408000000000000000000000000000000000000000000000000003fffffffc48709000000000000000000000000000000000000000000000000003f33e320000000000000000000000000000000000000000000000000000000003c031c0fc03cc0
  | 1, 4 => 0x3c03fc0fc4bfc9000000000000000000000000000000000000000000000000000003fff00038f6000000000000000000000000000000000000000000000000003f33e32fc00700000000000000000000000000000000000000000000000000000003fcd0003ff6000000000000000000000000000000000000000000000000003ffffff03b78f6000000000000000000000000000000000000000000000000003003fc0f803fc0000000000000000000000000000000000000000000000000000c0c1c1fffffff0000000000000000000000000000000000000000000000000000c0e0c3830306
  | 1, 5 => 0x3ffffff0000000000000000000000000000000000000000000000000000000003ffffff0038007000000000000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000003f0fff1ffc7ff8000000000000000000000000000000000000000000000000003c03000fc000000000000000000000000000000000000000000000000000000000cc1cdfffffff00000000000000000000000000000000000000000000000000000000003b78f6000000000000000000000000000000000000000000000000003ffffff0000000
  | 1, 6 => 0xcc00d03b403600000000000000000000000000000000000000000000000000033003200480090000000000000000000000000000000000000000000000000000001c038038c0000000000000000000000000000000000000000000000000003ffffff03fc03f0000000000000000000000000000000000000000000000000003fc03f00000000000000000000000000000000000000000000000000000000033f3e3ec3c3c380000000000000000000000000000000000000000000000000030031c0c003cc0000000000000000000000000000000000000000000000000003ffffff0048009
  | 1, 7 => 0x3f30000fc48000000000000000000000000000000000000000000000000000003ffc1cd03b78f60000000000000000000000000000000000000000000000000000fce0f383c307000000000000000000000000000000000000000000000000003fffff00000000000000000000000000000000000000000000000000000000003fffff0ffffff80000000000000000000000000000000000000000000000000033f3e3e38383070000000000000000000000000000000000000000000000000000cc00c03b78360000000000000000000000000000000000000000000000000003fc1ff03ff8ff
  | 1, 8 => 0x3c03fc0fc03fc0000000000000000000000000000000000000000000000000000000fcffffffff000000000000000000000000000000000000000000000000003c00000fffc000000000000000000000000000000000000000000000000000003ffc030fffc038000000000000000000000000000000000000000000000000000000fcf0003bf7000000000000000000000000000000000000000000000000003f33e32ffcbf39000000000000000000000000000000000000000000000000003303030c040408000000000000000000000000000000000000000000000000003fffe32fffc709
  | 1, 9 => 0x3fff1f100000000000000000000000000000000000000000000000000000000000f000c38380060000000000000000000000000000000000000000000000000000f0fce383bbc7000000000000000000000000000000000000000000000000003ffc000fffc307000000000000000000000000000000000000000000000000003303030c7c7cf8000000000000000000000000000000000000000000000000003ffffff00038c0000000000000000000000000000000000000000000000000003f03ff0c3c3c38000000000000000000000000000000000000000000000000003f00000ffc0000
  | 1, 10 => 0x3f03030fffffff000000000000000000000000000000000000000000000000000c00fc03c003c0000000000000000000000000000000000000000000000000003ffffff003000600000000000000000000000000000000000000000000000000000000003fc03f00000000000000000000000000000000000000000000000000000003f000003f000000000000000000000000000000000000000000000000003ffc000c7c4000000000000000000000000000000000000000000000000000000c0c1c104040c0000000000000000000000000000000000000000000000000003ffffff04040c0
  | 1, 11 => 0x3fcfffd00000000000000000000000000000000000000000000000000000000003fce3f3bfc33f000000000000000000000000000000000000000000000000003ffffff00340c6000000000000000000000000000000000000000000000000003c03fc03800300000000000000000000000000000000000000000000000000003f33ff2fc4bfc9000000000000000000000000000000000000000000000000003fff030fffc408000000000000000000000000000000000000000000000000003fff030ffffc38000000000000000000000000000000000000000000000000003300000c3c0000
  | 1, 12 => 0x3c03ff1fc03ff80000000000000000000000000000000000000000000000000000cc1cd03b78c0000000000000000000000000000000000000000000000000003003e00f803f00000000000000000000000000000000000000000000000000003c03fc0fc00300000000000000000000000000000000000000000000000000003ffffcd00000000000000000000000000000000000000000000000000000000000000003c3c3c7000000000000000000000000000000000000000000000000000000fcf0003fff000000000000000000000000000000000000000000000000003fffffffffc307
  | 1, 13 => 0x3ffc00dfffc0360000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000003f30000fc48000000000000000000000000000000000000000000000000000003f0fff10000000000000000000000000000000000000000000000000000000003c03fc0fc038c0000000000000000000000000000000000000000000000000003f03ff0fc43fc800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fc00f03fc03f
  | 1, 14 => 0x3ffc000fffc709000000000000000000000000000000000000000000000000003fff1f1ffffcf8000000000000000000000000000000000000000000000000003f0c000c7c40000000000000000000000000000000000000000000000000000000fc1cf03bf8f7000000000000000000000000000000000000000000000000000000000fbfbf3f000000000000000000000000000000000000000000000000003ffc000fffc000000000000000000000000000000000000000000000000000003ffffff003c007000000000000000000000000000000000000000000000000000003ff00003ff8
  | 1, 15 => 0x3ffffff00003c7000000000000000000000000000000000000000000000000003f33e32fc48709000000000000000000000000000000000000000000000000003ffc000fffc03f0000000000000000000000000000000000000000000000000000fc00f003c0070000000000000000000000000000000000000000000000000000f0e003838300000000000000000000000000000000000000000000000000000000fcf00003c70000000000000000000000000000000000000000000000000000cc1c003b78c0000000000000000000000000000000000000000000000000000cfcfcf3838307
  | 2, 0 => 0xcc1cd03ff8ff000000000000000000000000000000000000000000000000000000e003800300000000000000000000000000000000000000000000000000003ffffff0000709000000000000000000000000000000000000000000000000003fffe3e00000000000000000000000000000000000000000000000000000000000000000003fff000000000000000000000000000000000000000000000000003c03fc0c003cc0000000000000000000000000000000000000000000000000000000000ffcfff9000000000000000000000000000000000000000000000000000000000ffffc38
  | 2, 1 => 0xfc00f03bc0370000000000000000000000000000000000000000000000000000f0e0efffffff0000000000000000000000000000000000000000000000000000000003838307000000000000000000000000000000000000000000000000000000000ffff8f6000000000000000000000000000000000000000000000000003f33e3200000000000000000000000000000000000000000000000000000000000f0e0e3800300000000000000000000000000000000000000000000000000003303030fffffff000000000000000000000000000000000000000000000000000000000c3c3c38
  | 2, 2 => 0xfc48709000000000000000000000000000000000000000000000000000003fff0003fc00000000000000000000000000000000000000000000000000000ccfcd3bb7bf6000000000000000000000000000000000000000000000000003ffc000fffffff000000000000000000000000000000000000000000000000000000000fffc000000000000000000000000000000000000000000000000000003c031c0c403cc0000000000000000000000000000000000000000000000000003fff03fc7fc43f0000000000000000000000000000000000000000000000000003fc00003fc000
  | 2, 3 => 0x3ffc0000000000000000000000000000000000000000000000000000000000003ff3ffe0000000000000000000000000000000000000000000000000000000003ccffcd03b78f6000000000000000000000000000000000000000000000000003ffc032fffc009000000000000000000000000000000000000000000000000003c03e00fc00700000000000000000000000000000000000000000000000000003c03e00fc03f000000000000000000000000000000000000000000000000000000cc1cd03838f00000000000000000000000000000000000000000000000000000f0e0e0030006
  | 2, 4 => 0xc1c103878f0000000000000000000000000000000000000000000000000003303e3000000000000000000000000000000000000000000000000000000000003fc00e03fc007000000000000000000000000000000000000000000000000000003ff30003ff9000000000000000000000000000000000000000000000000003ffc1c0ffff8c00000000000000000000000000000000000000000000000000000fc1cd00000000000000000000000000000000000000000000000000000000033f30300000000000000000000000000000000000000000000000000000000003ccffcdfc03fc0
  | 2, 5 => 0x30c03103c40380000000000000000000000000000000000000000000000000033fffff0000000000000000000000000000000000000000000000000000000003fff030c3c3c380000000000000000000000000000000000000000000000000000f000c3838006000000000000000000000000000000000000000000000000003ff3e3efc7870f000000000000000000000000000000000000000000000000000030e0238083010000000000000000000000000000000000000000000000000000fcfcf3838307000000000000000000000000000000000000000000000000003fcf1fdc7f7cfe
  | 2, 6 => 0x3f0c000ffc40000000000000000000000000000000000000000000000000000000c000c0030006000000000000000000000000000000000000000000000000003f03e30fc40708000000000000000000000000000000000000000000000000003f0f1f1c7c7cf8000000000000000000000000000000000000000000000000003303030c3c3c380000000000000000000000000000000000000000000000000000f0e0e0000000000000000000000000000000000000000000000000000000003f03ff0fc43fc8000000000000000000000000000000000000000000000000003f0f1f1fffffff
  | 2, 7 => 0x3ffffffc040408000000000000000000000000000000000000000000000000003fff030fffc4080000000000000000000000000000000000000000000000000000031f10003cf80000000000000000000000000000000000000000000000000003ff1ff03ffcff0000000000000000000000000000000000000000000000000003fc03f03fc03f000000000000000000000000000000000000000000000000003ffcfcf0000000000000000000000000000000000000000000000000000000003ffc00cfffc0000000000000000000000000000000000000000000000000000000cc1cd00338c6
  | 2, 8 => 0x3c03ff2fc03fc9000000000000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000003cc000cfc300060000000000000000000000000000000000000000000000000033ff03f03fc03f000000000000000000000000000000000000000000000000003f03030c7c3c38000000000000000000000000000000000000000000000000003ffc00cfffc006000000000000000000000000000000000000000000000000003fff1fd00000000000000000000000000000000000000000000000000000000000fc00ffffffff
  | 2, 9 => 0x3ffffffc7c7cf8000000000000000000000000000000000000000000000000003f0f1f10000000000000000000000000000000000000000000000000000000000000000ffb7ff6000000000000000000000000000000000000000000000000003f3fff3ffcfff9000000000000000000000000000000000000000000000000000000000ffc3ff80000000000000000000000000000000000000000000000000000cc1cd03b4000000000000000000000000000000000000000000000000000003cfffcf0000000000000000000000000000000000000000000000000000000003f3fff30000000
  | 2, 10 => 0xfcfcf03b78f60000000000000000000000000000000000000000000000000003fc03f03b4036000000000000000000000000000000000000000000000000003f33e32fc487090000000000000000000000000000000000000000000000000000fcfcf383c3c70000000000000000000000000000000000000000000000000000000003bbfbf7000000000000000000000000000000000000000000000000000c30e023c08301000000000000000000000000000000000000000000000000000000000c7c7cf8000000000000000000000000000000000000000000000000003f03030c440408
  | 2, 11 => 0x33ffffffbfffff000000000000000000000000000000000000000000000000000003fff00000000000000000000000000000000000000000000000000000000033cf1fd03b78f6000000000000000000000000000000000000000000000000003ffffffc3f7cfe000000000000000000000000000000000000000000000000003fff000ffffc00000000000000000000000000000000000000000000000000003c03000fc03c00000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000030cf1cdc3b7cf6
  | 2, 12 => 0x3fffffffc00000000000000000000000000000000000000000000000000000003ffffff3800300000000000000000000000000000000000000000000000000003cf3fc0fc3bfc0000000000000000000000000000000000000000000000000003fff1fdffffcfe0000000000000000000000000000000000000000000000000000c000c0000000000000000000000000000000000000000000000000000000003ffffc0fc03fc00000000000000000000000000000000000000000000000000000c0e0c3830306000000000000000000000000000000000000000000000000003ffffff3838000
  | 2, 13 => 0x3ffffff03b4000000000000000000000000000000000000000000000000000003fffffffffffc00000000000000000000000000000000000000000000000000000001cd00038f6000000000000000000000000000000000000000000000000003f03030ffc3c38000000000000000000000000000000000000000000000000003ffffffc3c0000000000000000000000000000000000000000000000000000000000e0e0000307000000000000000000000000000000000000000000000000003cc3fccfc33fc6000000000000000000000000000000000000000000000000003cf3fce3838307
  | 2, 14 => 0x33cc1cdc3f78f60000000000000000000000000000000000000000000000000000f0e0e3838307000000000000000000000000000000000000000000000000003cf3fcefc03fc00000000000000000000000000000000000000000000000000000f0e0e3838000000000000000000000000000000000000000000000000000003ffc000ffff8300000000000000000000000000000000000000000000000000033c303cc3f3c3e000000000000000000000000000000000000000000000000000cfcfcf00000000000000000000000000000000000000000000000000000000000f0e0e3800300
  | 2, 15 => 0x3f03fc0ffc3fc0000000000000000000000000000000000000000000000000003fcfffdfff7ffe000000000000000000000000000000000000000000000000003ffce0e00000000000000000000000000000000000000000000000000000000000cc1cd00340c6000000000000000000000000000000000000000000000000003ffffcdffffff6000000000000000000000000000000000000000000000000003cfffcfffbfff7000000000000000000000000000000000000000000000000003ffffff03838300000000000000000000000000000000000000000000000000033f0e0efbf8307
  | 3, 0 => 0x3ffffffffc3ff80000000000000000000000000000000000000000000000000000f0e0e3bbbb370000000000000000000000000000000000000000000000000000cc00003b7830000000000000000000000000000000000000000000000000003ffffffc003c00000000000000000000000000000000000000000000000000003ffffffffff8f60000000000000000000000000000000000000000000000000000c01cc00338c6000000000000000000000000000000000000000000000000003ffffff3bbfbf7000000000000000000000000000000000000000000000000003ffffc00000000
  | 3, 1 => 0x3ffffffffb7ff6000000000000000000000000000000000000000000000000003cf3fce0000000000000000000000000000000000000000000000000000000003ff3ffefffbfff000000000000000000000000000000000000000000000000003ffffc0fffc000000000000000000000000000000000000000000000000000003c03fc0fc000000000000000000000000000000000000000000000000000000030f3e0ef83bf070000000000000000000000000000000000000000000000000033cf1fdc3c3c38000000000000000000000000000000000000000000000000003ffce0efffc000
  | 3, 2 => 0x1c00000000000000000000000000000000000000000000000000000000003fffffffc3bfc7000000000000000000000000000000000000000000000000003fffe3efffff3f000000000000000000000000000000000000000000000000000cfc0003c3c000000000000000000000000000000000000000000000000000003ffcfcfffffbf7000000000000000000000000000000000000000000000000003ffffffffffc38000000000000000000000000000000000000000000000000003fffffffbfbf3f0000000000000000000000000000000000000000000000000000fc1cd3bbf8f6
  | 3, 3 => 0x33f3030fbfbc380000000000000000000000000000000000000000000000000000030300003c38000000000000000000000000000000000000000000000000003ffffcefffffc7000000000000000000000000000000000000000000000000003ccffc0ffb7fc00000000000000000000000000000000000000000000000000000fce0e3bbc3070000000000000000000000000000000000000000000000000033cf1fd00000000000000000000000000000000000000000000000000000000000c000c03b38360000000000000000000000000000000000000000000000000033cf030c3f7c38
  | 3, 4 => 0x3ffce0e3838307000000000000000000000000000000000000000000000000003c03fc0c003c000000000000000000000000000000000000000000000000000000cc1cd0383830
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ffffff2202020000000000000000000000000000000000000000000000000003efad26fdfde9b0000000000000000000000000000000000000000000000000028a2e48b820f440000000000000000000000000000000000000000000000000015cd3dd4fb79f6000000000000000000000000000000000000000000000000003ffffff2ab2976000000000000000000000000000000000000000000000000003ca8b48fd259c40000000000000000000000000000000000000000000000000033574b7d3dbe3b000000000000000000000000000000000000000000000000003fffffffffffff
  | 0, 1 => 0x3ca9bc86d279c40000000000000000000000000000000000000000000000000015cd3dd0202020000000000000000000000000000000000000000000000000003ca8900fd2508000000000000000000000000000000000000000000000000000158d3d94f279e4000000000000000000000000000000000000000000000000003ffc900fffd080000000000000000000000000000000000000000000000000003cabfc8fd27fc4000000000000000000000000000000000000000000000000002af2e6eb8f8f5f000000000000000000000000000000000000000000000000002a32c226db59d6
  | 0, 2 => 0x2af2e6eb8f8f5f00000000000000000000000000000000000000000000000000150d19147070a0000000000000000000000000000000000000000000000000002af1891b8fa02000000000000000000000000000000000000000000000000000265a52694dce9b0000000000000000000000000000000000000000000000000033574b792dae3b000000000000000000000000000000000000000000000000002af2e6e28b0956000000000000000000000000000000000000000000000000003cabfc820020000000000000000000000000000000000000000000000000000015cd3dd4f279e4
  | 0, 3 => 0x2a32c22b0d861b000000000000000000000000000000000000000000000000003ca8937fd250bb000000000000000000000000000000000000000000000000003caaf48fd25fc4000000000000000000000000000000000000000000000000003fffffff3dbe3b000000000000000000000000000000000000000000000000003fffdb7ff270a00000000000000000000000000000000000000000000000000015cd3dd4fb79f6000000000000000000000000000000000000000000000000000ca8b482c241c400000000000000000000000000000000000000000000000000150d19147070a0
  | 0, 4 => 0x2af2c26b8f8e1b000000000000000000000000000000000000000000000000003ef8900fdfd0800000000000000000000000000000000000000000000000000003576ff02daf7f000000000000000000000000000000000000000000000000003cabfc86d279c40000000000000000000000000000000000000000000000000000036ff0002f7f000000000000000000000000000000000000000000000000002a32c22b048609000000000000000000000000000000000000000000000000003ffffff22020200000000000000000000000000000000000000000000000000015cd3dd4f279e4
  | 0, 5 => 0x150d1919afaf7f0000000000000000000000000000000000000000000000000029a6e59ba20f64000000000000000000000000000000000000000000000000000000000ddfdfdf000000000000000000000000000000000000000000000000003ffc900fffd0800000000000000000000000000000000000000000000000000033574b7d3dbe3b0000000000000000000000000000000000000000000000000000c024c08b0956000000000000000000000000000000000000000000000000003ffcb4cfffd9d6000000000000000000000000000000000000000000000000003caaf48fd25fc4
  | 0, 6 => 0x33d76ffdbfbf7f000000000000000000000000000000000000000000000000003deffdd2202020000000000000000000000000000000000000000000000000002b76c37b2d863b0000000000000000000000000000000000000000000000000019658956393832000000000000000000000000000000000000000000000000003ffc900ff25080000000000000000000000000000000000000000000000000002af2e6eb8f8f5f000000000000000000000000000000000000000000000000000354037df25fe40000000000000000000000000000000000000000000000000033574b70e261e4
  | 0, 7 => 0x15cc1004fb50800000000000000000000000000000000000000000000000000014893c84d279c4000000000000000000000000000000000000000000000000003cabfc86d279c4000000000000000000000000000000000000000000000000002a32c22fdfdfdf000000000000000000000000000000000000000000000000003ffc90022000000000000000000000000000000000000000000000000000000015cd3dd4fb79f60000000000000000000000000000000000000000000000000015ce5224fb5689000000000000000000000000000000000000000000000000000354037dffdfff
  | 0, 8 => 0x37df7ffdffffff0000000000000000000000000000000000000000000000000011450954393832000000000000000000000000000000000000000000000000003deffdd22020200000000000000000000000000000000000000000000000000015cd3dd4fb79f6000000000000000000000000000000000000000000000000003dedbdd2202020000000000000000000000000000000000000000000000000003003480d103e00000000000000000000000000000000000000000000000000003ffdbdd2202020000000000000000000000000000000000000000000000000003ca9bc8fd279c4
  | 0, 9 => 0x210022ddfdfdf0000000000000000000000000000000000000000000000000016591a645df09b0000000000000000000000000000000000000000000000000015cd3dd924a629000000000000000000000000000000000000000000000000002a32c22b0486090000000000000000000000000000000000000000000000000003574b702da63b000000000000000000000000000000000000000000000000003ffc9006fb50800000000000000000000000000000000000000000000000000015cd3dd0ab2976000000000000000000000000000000000000000000000000003ffc9002200f5f
  | 0, 10 => 0x16993ea4d6f9cd000000000000000000000000000000000000000000000000003ca89006d25080000000000000000000000000000000000000000000000000003cabfc820da01b0000000000000000000000000000000000000000000000000015cc34c4fb59d6000000000000000000000000000000000000000000000000002966c15b2906320000000000000000000000000000000000000000000000000000c024c08b0956000000000000000000000000000000000000000000000000003003480d103e00000000000000000000000000000000000000000000000000003354248d3d9144
  | 0, 11 => 0x225242690d8e1b00000000000000000000000000000000000000000000000000035403792d863b000000000000000000000000000000000000000000000000003dec900ffb5080000000000000000000000000000000000000000000000000002af2e6e6505080000000000000000000000000000000000000000000000000003fffdb72202020000000000000000000000000000000000000000000000000003ffffff2202020000000000000000000000000000000000000000000000000003f3fdb3f74f6a9000000000000000000000000000000000000000000000000003ffc900ff25080
  | 0, 12 => 0x37df7ffdffffff00000000000000000000000000000000000000000000000000035403702d803b000000000000000000000000000000000000000000000000003fffffffffffff0000000000000000000000000000000000000000000000000033574b70202020000000000000000000000000000000000000000000000000003deffdd2202020000000000000000000000000000000000000000000000000003cabfc8fd27fc4000000000000000000000000000000000000000000000000003ef8900fdfd080000000000000000000000000000000000000000000000000003bf7efffbfbf7f
  | 0, 13 => 0x3ffffc8fffffc4000000000000000000000000000000000000000000000000003deffddffb7ff60000000000000000000000000000000000000000000000000015cd3dd4fb79f6000000000000000000000000000000000000000000000000003fffdb7ffff0a00000000000000000000000000000000000000000000000000000036ee0002f5f000000000000000000000000000000000000000000000000003deffddffb7ff60000000000000000000000000000000000000000000000000000012d900021640000000000000000000000000000000000000000000000000001040110200020
  | 0, 14 => 0x3ffc926fffd09b00000000000000000000000000000000000000000000000000035401502d8032000000000000000000000000000000000000000000000000003bf7efffbfbf7f000000000000000000000000000000000000000000000000003cabffffd27fff000000000000000000000000000000000000000000000000003ffc937fffd0bb000000000000000000000000000000000000000000000000003ffdbddffff0a0000000000000000000000000000000000000000000000000003bf7eff22020200000000000000000000000000000000000000000000000000037df7ffdffffff
  | 0, 15 => 0x3efbfeefdfffdf00000000000000000000000000000000000000000000000000175d1b747df0bb000000000000000000000000000000000000000000000000003fffdb72202020000000000000000000000000000000000000000000000000003cabfc8fdfffdf000000000000000000000000000000000000000000000000000000000dd25fc4000000000000000000000000000000000000000000000000003efaf6efdfdfdf000000000000000000000000000000000000000000000000003ffc900fffd080000000000000000000000000000000000000000000000000003ffed26fffde9b
  | 1, 0 => 0x3ffef48fffdfc400000000000000000000000000000000000000000000000000035643702d863b0000000000000000000000000000000000000000000000000033574b7d3dbe3b00000000000000000000000000000000000000000000000000035403702d803b000000000000000000000000000000000000000000000000003bf7eff2202020000000000000000000000000000000000000000000000000002af0800b8f800000000000000000000000000000000000000000000000000000025002600d801b000000000000000000000000000000000000000000000000003ffc911fffd0a0
  | 1, 1 => 0x36c80002f44000000000000000000000000000000000000000000000000003caad00fd25e80000000000000000000000000000000000000000000000000003ffc937fffd0a00000000000000000000000000000000000000000000000000017dd3ff4fff9ff0000000000000000000000000000000000000000000000000000024220000609000000000000000000000000000000000000000000000000003ffdbddffff9f6000000000000000000000000000000000000000000000000003ffffffffff0a0000000000000000000000000000000000000000000000000003ffffffff27fe4
  | 1, 2 => 0xc024cddfdfdf000000000000000000000000000000000000000000000000003dedbddffb79f6000000000000000000000000000000000000000000000000003cabfc8fd27fc4000000000000000000000000000000000000000000000000003ffffffbafaf7f000000000000000000000000000000000000000000000000002af2e6e2000000000000000000000000000000000000000000000000000000003cabfc8fd27fc400000000000000000000000000000000000000000000000000150d19147070a0000000000000000000000000000000000000000000000000000002422ddfdfdf
  | 1, 3 => 0x3ffef6efffdfdf000000000000000000000000000000000000000000000000003ffffffff27fe4000000000000000000000000000000000000000000000000003ca8900fd25080000000000000000000000000000000000000000000000000003ffffff2202f7f000000000000000000000000000000000000000000000000003ffffff2202020000000000000000000000000000000000000000000000000003ffffffb24a629000000000000000000000000000000000000000000000000002a32c222000000000000000000000000000000000000000000000000000000003cabfc8fd27fc4
  | 1, 4 => 0x3cabfc8fd6ffcd0000000000000000000000000000000000000000000000000000036ff0002976000000000000000000000000000000000000000000000000002a32c22b0006000000000000000000000000000000000000000000000000000000036dd0002f76000000000000000000000000000000000000000000000000003ffffff6fb79f6000000000000000000000000000000000000000000000000003cabfc8fd27fc4000000000000000000000000000000000000000000000000000408100ddfdfdf000000000000000000000000000000000000000000000000002af2e6eb8f8f5f
  | 1, 5 => 0x3ffffffb2dae3b000000000000000000000000000000000000000000000000003ffffff22da03b0000000000000000000000000000000000000000000000000000000004d251c4000000000000000000000000000000000000000000000000003daffd9ff27fe4000000000000000000000000000000000000000000000000003cabd80fd270800000000000000000000000000000000000000000000000000015cd3dddffffff0000000000000000000000000000000000000000000000000000000004db59d6000000000000000000000000000000000000000000000000003ffffff2a22964
  | 1, 6 => 0x14401502900320000000000000000000000000000000000000000000000000002100220048009000000000000000000000000000000000000000000000000003ca9bc8fd279c4000000000000000000000000000000000000000000000000003ffffff22da03b0000000000000000000000000000000000000000000000000003540370200020000000000000000000000000000000000000000000000000003bf7efff3dbe3b00000000000000000000000000000000000000000000000000348b7c8dd27fc4000000000000000000000000000000000000000000000000003ffffff224a029
  | 1, 7 => 0x2a30800b048000000000000000000000000000000000000000000000000000003ffdbdd6fb79f6000000000000000000000000000000000000000000000000002af2e6eb8f8f5f000000000000000000000000000000000000000000000000003ffffff2202020000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003bf7effbafaf7f0000000000000000000000000000000000000000000000000015cd3dd4fb79f60000000000000000000000000000000000000000000000000017dd3ff4fff9ff
  | 1, 8 => 0x3efbfeefdfffdf000000000000000000000000000000000000000000000000000000248ddfdfdf000000000000000000000000000000000000000000000000003ca8900fdfd080000000000000000000000000000000000000000000000000003ffc937fffd0bb0000000000000000000000000000000000000000000000000000036ff0002f7f000000000000000000000000000000000000000000000000003b77cb7f3dbe3b0000000000000000000000000000000000000000000000000022124229048609000000000000000000000000000000000000000000000000003ffed22fffd689
  | 1, 9 => 0x3ffd9912202020000000000000000000000000000000000000000000000000002af0a4cb8f8956000000000000000000000000000000000000000000000000003efbfeefdfffdf000000000000000000000000000000000000000000000000003ffc900fffdfdf0000000000000000000000000000000000000000000000000033574b7d7dfebb000000000000000000000000000000000000000000000000003ffffff6f279e4000000000000000000000000000000000000000000000000003fffffff3dbe3b000000000000000000000000000000000000000000000000003ffc900fffd080
  | 1, 10 => 0xddfdfdf000000000000000000000000000000000000000000000000000ca8b482c241c4000000000000000000000000000000000000000000000000003ffffffbafaf7f00000000000000000000000000000000000000000000000000000000000d801b000000000000000000000000000000000000000000000000000000037000003b000000000000000000000000000000000000000000000000003ffc90067050800000000000000000000000000000000000000000000000000004081000404080000000000000000000000000000000000000000000000000003ffffff26060a0
  | 1, 11 => 0x3ffffff2202020000000000000000000000000000000000000000000000000002bf6e7fbaf8f7f000000000000000000000000000000000000000000000000003ffffff2e261e4000000000000000000000000000000000000000000000000003cabfc8b822f44000000000000000000000000000000000000000000000000003ebbfeafd6ffcd000000000000000000000000000000000000000000000000003ffc900fffd080000000000000000000000000000000000000000000000000003fffdb7ffffebb000000000000000000000000000000000000000000000000003354000d3d9000
  | 1, 12 => 0x3cabfd9fd27fe40000000000000000000000000000000000000000000000000015cd3dd4fb79e40000000000000000000000000000000000000000000000000038a3ec8f923f44000000000000000000000000000000000000000000000000003cabfc8fd27fc4000000000000000000000000000000000000000000000000003ffffdd22020200000000000000000000000000000000000000000000000000000000000c241c40000000000000000000000000000000000000000000000000000002480000f5f000000000000000000000000000000000000000000000000003fffffffffffff
  | 1, 13 => 0x3ffc915fffd0b2000000000000000000000000000000000000000000000000002af2c26b0d8e1b000000000000000000000000000000000000000000000000003eb8900fd6d080000000000000000000000000000000000000000000000000003daffd92202020000000000000000000000000000000000000000000000000003cabfc8fd279c4000000000000000000000000000000000000000000000000003cabfc8fd27fc4000000000000000000000000000000000000000000000000000080248082094400000000000000000000000000000000000000000000000000000000000d801b
  | 1, 14 => 0x3ffc900fffd689000000000000000000000000000000000000000000000000003ffd991ffff0a000000000000000000000000000000000000000000000000000150c10047050800000000000000000000000000000000000000000000000000015cd3dd4fb79f6000000000000000000000000000000000000000000000000000000000d9f9f5f000000000000000000000000000000000000000000000000003ffcb48fffd9c4000000000000000000000000000000000000000000000000003ffffff22020200000000000000000000000000000000000000000000000000000036ff0002f7f
  | 1, 15 => 0x3ffffff22021640000000000000000000000000000000000000000000000000008208002000000000000000000000000000000000000000000000000000000003ffc900fffd09b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002af2e48b8f8f4400000000000000000000000000000000000000000000000000000024800001440000000000000000000000000000000000000000000000000015cd3c84fb79c4000000000000000000000000000000000000000000000000000ca8b482820144
  | 2, 0 => 0x15cd3dd4fff9ff000000000000000000000000000000000000000000000000003caaf48fd25fc4000000000000000000000000000000000000000000000000003ffffff2202629000000000000000000000000000000000000000000000000003ffffff22020200000000000000000000000000000000000000000000000000000000000000f5f000000000000000000000000000000000000000000000000003cabfc8fd27fc4000000000000000000000000000000000000000000000000000000000d54d689000000000000000000000000000000000000000000000000000000000ddfde9b
  | 2, 1 => 0x35403702d803b000000000000000000000000000000000000000000000000002af2e6efdfdfdf00000000000000000000000000000000000000000000000000000000098f8f5f000000000000000000000000000000000000000000000000000000000ddfd9d6000000000000000000000000000000000000000000000000003b77cb72202020000000000000000000000000000000000000000000000000002af2e6eb8f8f5f0000000000000000000000000000000000000000000000000033574b7dffffff000000000000000000000000000000000000000000000000000000000d1d9e1b
  | 2, 2 => 0x90486090000000000000000000000000000000000000000000000000000036ff0002f64000000000000000000000000000000000000000000000000003deffddffb7ff6000000000000000000000000000000000000000000000000003ffc900fffdfdf000000000000000000000000000000000000000000000000000000000ddfd080000000000000000000000000000000000000000000000000001409180450708000000000000000000000000000000000000000000000000000035403702d803b00000000000000000000000000000000000000000000000000035400002d8000
  | 2, 3 => 0x3ffd9952202020000000000000000000000000000000000000000000000000003ffffff2202020000000000000000000000000000000000000000000000000003deffdd6fb79f6000000000000000000000000000000000000000000000000003ffc922fffd089000000000000000000000000000000000000000000000000002822c00b000600000000000000000000000000000000000000000000000000003cabfc8fd27fc40000000000000000000000000000000000000000000000000015cd3dd4fb79f6000000000000000000000000000000000000000000000000002af2e6eb8f8f5f
  | 2, 4 => 0x150d19147070a0000000000000000000000000000000000000000000000000003bf7eff220202000000000000000000000000000000000000000000000000000035402602d801b0000000000000000000000000000000000000000000000000000034b30002629000000000000000000000000000000000000000000000000003ffdbc8ffff9c4000000000000000000000000000000000000000000000000003ffdbdd2202020000000000000000000000000000000000000000000000000003bf7cb72202020000000000000000000000000000000000000000000000000003deffddff27fe4
  | 2, 5 => 0x1040110200020000000000000000000000000000000000000000000000000003ffffff2202020000000000000000000000000000000000000000000000000003fffdb7f3dbe3b000000000000000000000000000000000000000000000000002af2e6eb8f8f5f000000000000000000000000000000000000000000000000002af2e6eb8f8f5f000000000000000000000000000000000000000000000000002a32c22b048609000000000000000000000000000000000000000000000000003ffffffbafaf7f0000000000000000000000000000000000000000000000000015cd3dd4fb79f6
  | 2, 6 => 0x3dac900ff250800000000000000000000000000000000000000000000000000022d266e98f8f5f000000000000000000000000000000000000000000000000002a32c22b04860900000000000000000000000000000000000000000000000000375f5b7d7dfebb0000000000000000000000000000000000000000000000000011050914303020000000000000000000000000000000000000000000000000002af2e6eb0d8e1b000000000000000000000000000000000000000000000000003ebbfeafd6ffcd00000000000000000000000000000000000000000000000000150d191dffffff
  | 2, 7 => 0x3ffffffb24a629000000000000000000000000000000000000000000000000003ffed22fffd68900000000000000000000000000000000000000000000000000000109100020200000000000000000000000000000000000000000000000000003550b702da03b00000000000000000000000000000000000000000000000000235643792d8e3b000000000000000000000000000000000000000000000000003ffffff2202020000000000000000000000000000000000000000000000000003ffcb4cfffd0800000000000000000000000000000000000000000000000000015cd3dd4fb79f6
  | 2, 8 => 0x3cabfeafd27fcd000000000000000000000000000000000000000000000000002252426ddfdfdf000000000000000000000000000000000000000000000000003ce8b4cfdb59d60000000000000000000000000000000000000000000000000033574b702da03b0000000000000000000000000000000000000000000000000033574b7d3dbe3b000000000000000000000000000000000000000000000000003ffef6efffdfdf000000000000000000000000000000000000000000000000003ffffff2202020000000000000000000000000000000000000000000000000000000000ddfdfdf
  | 2, 9 => 0x3ffffff67070a000000000000000000000000000000000000000000000000000150d1910202020000000000000000000000000000000000000000000000000000000000ddb5fd6000000000000000000000000000000000000000000000000003f3fdb3f74f6a9000000000000000000000000000000000000000000000000000000000ddfdfdf0000000000000000000000000000000000000000000000000015cd3dd4fb70a0000000000000000000000000000000000000000000000000003ffffff2202020000000000000000000000000000000000000000000000000003f3fdb32202020
  | 2, 10 => 0x3ffffff6fb79f60000000000000000000000000000000000000000000000000003540370290032000000000000000000000000000000000000000000000000002a72c26b0d8e1b000000000000000000000000000000000000000000000000000ca8b482c241c4000000000000000000000000000000000000000000000000000000000ddfdfdf000000000000000000000000000000000000000000000000000820800200000000000000000000000000000000000000000000000000000000000000045050800000000000000000000000000000000000000000000000000000000000000000
  | 2, 11 => 0x3fffffffffffff0000000000000000000000000000000000000000000000000000036ff00020200000000000000000000000000000000000000000000000000037df7ff4fb79f6000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffd80ffffe80000000000000000000000000000000000000000000000000003cabd80fd27e800000000000000000000000000000000000000000000000000028a2e4820000000000000000000000000000000000000000000000000000000035cf7dddfb7ff6
  | 2, 12 => 0x3ffffffff270a0000000000000000000000000000000000000000000000000003ffffffba22f64000000000000000000000000000000000000000000000000003efbfc8fdfffc4000000000000000000000000000000000000000000000000003fffffffffffff0000000000000000000000000000000000000000000000000000c024c0000000000000000000000000000000000000000000000000000000003ffffc8ff27fc40000000000000000000000000000000000000000000000000028e2e4cb8b0f56000000000000000000000000000000000000000000000000003ffffffbafa020
  | 2, 13 => 0x3ffffff6fb70a0000000000000000000000000000000000000000000000000003fffffffffffe40000000000000000000000000000000000000000000000000000012dd0002976000000000000000000000000000000000000000000000000003fffdb7ffffebb000000000000000000000000000000000000000000000000003fffffff3db02000000000000000000000000000000000000000000000000000000266e0000f5f000000000000000000000000000000000000000000000000003cebfccfdb7fd6000000000000000000000000000000000000000000000000003efbfeeb8faf5f
  | 2, 14 => 0x37dd3dddfff9f60000000000000000000000000000000000000000000000000008a0a482820144000000000000000000000000000000000000000000000000003efbfeefd27fc4000000000000000000000000000000000000000000000000002af2e6eb8f8000000000000000000000000000000000000000000000000000003ffd995ffff8b20000000000000000000000000000000000000000000000000033d76ffdbfbf7f000000000000000000000000000000000000000000000000000ca8b482000000000000000000000000000000000000000000000000000000002af2e6eb820f44
  | 2, 15 => 0x3ffffc8fffffc4000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffef6e22000000000000000000000000000000000000000000000000000000004883480c241c4000000000000000000000000000000000000000000000000003ffffddffffff6000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffff6393832000000000000000000000000000000000000000000000000003bf6e6efbf9f5f
  | 3, 0 => 0x3fffffffffffff000000000000000000000000000000000000000000000000003bf7efffbfbf7f0000000000000000000000000000000000000000000000000015cd1954fb78b2000000000000000000000000000000000000000000000000003fffffff303e20000000000000000000000000000000000000000000000000003ffffffffff9f60000000000000000000000000000000000000000000000000014c93cc4db79d6000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffc82202000
  | 3, 1 => 0x3ffffffffb7ff6000000000000000000000000000000000000000000000000003efbfee2002000000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffc8ffff080000000000000000000000000000000000000000000000000003cabfc8fd27080000000000000000000000000000000000000000000000000003af3eeef9fbf5f0000000000000000000000000000000000000000000000000037df7ffd3dbe3b000000000000000000000000000000000000000000000000003ffef6efffd080
  | 3, 2 => 0x14893c80002000000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000000ca89002c24080000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffffffffebb000000000000000000000000000000000000000000000000003fffffffbfbf7f000000000000000000000000000000000000000000000000003ffdbddffff9f6
  | 3, 3 => 0x3bf7cb7fbfbe3b0000000000000000000000000000000000000000000000000000034b70002e3b000000000000000000000000000000000000000000000000003ffffeefffffdf000000000000000000000000000000000000000000000000003deffc8ffb7fc4000000000000000000000000000000000000000000000000003ffef6efffdfdf0000000000000000000000000000000000000000000000000037df7ff02020200000000000000000000000000000000000000000000000000011c52dd4bb39760000000000000000000000000000000000000000000000000037df5b7dfffebb
  | 3, 4 => 0x3ffef6ebaf8f5f000000000000000000000000000000000000000000000000003cabfc8f103e000000000000000000000000000000000000000000000000000015cd3dd4393832
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 419 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 419 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 419 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 419 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 9 0) :: stateWiresD n (ids >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 9 0) :: stateWiresS n (ids >>> 9)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 6 => 135
  | 7 => 125
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0x7603a2dd75d13e9271c71b6c6ed9c95b6ea418756cd0204069904ec969749347684ea6b866c490a25f4a5e6d5df3c6e45d3edab75a85e437564bdcd354aaacd3527c9356506d52fe4ecd1a174e94f1084e0538e94c70991f4a19e0d6482f817746f8474e41777e7340fb2d0a3fa021c53f313b653d7b1e3a3d3209773b2a790d3a4c498939c1856936d1397b30b17a1b2bac739c2b42fd002ad82ba32ac299d129c9f84529c4b9f826b8bfe5253f8be523a8da941f8294af1f76f96f1f601c511b086a1c1a3d0b5f19b9c86817802805167b58e815ead3ea14887efa146dd67812ded9d70ce919930a5a9dcf088b9c3706b6b95905495b4e01eda1a00115eb39
  | 6, 1 => 0xebed4b1ae8197b1de59a4bdce458c67ce319d0ffe2ba5319deea4cc4d7bf8d9ad78489b0d43a869fd2303464d2011c2fd11892cecfa211b3cf171212cb7a0fdfc89d7b8fc7e502ffc6fa342cc6d23c35c57f7335c463bb14c3248b03c060a091bfdf6e4bbf1a8222bd15572dbc0e880fbbf07120bb8a5aaaba5fe039b9720104b9653685b574c2ceb2003480b160e5e2b0b62913b03b1c5fafd73875af58ea2faf4f6175ad70f268acd99b96aa939139aa4ba25ea8cc5a0fa8251c4ca1745b989f2bfd24960d6e46956cd1a78f7e124988d60512863595e384689b4d836e2af58341e6cc8192eb9980f382ad7b901b0978101b437751c4e1772d50a8764d3db5
  | 6, 2 => 0xfd93ab53f5ece40cf3ea6d26f36d449cf34bcd0cf3498f0ef2a008ca
  | 7, 0 => 0x84d2c175804dee4d7dc3c7c37a5ac63378ba6f2e7128b4976986998d694152886640f86d64a8dd9c6430b85d61b0ce8d61279f2a603fd0126001d5a75fecffb25eec2d245e4f53365e4e7aea5ab5abb15a24f22f595bb8d458871ddb560409b254bb116252652dd550d632f74b550f714704685f46f3f1d645d1eda144efaef64125de8a400015073d084ce73b9517d9375c328c3578c84e313507a6292e66d9264ce74e2358f6eb2232fccd21da3c201dbf2e791a28899f19e4b4771983ef5b19570811186b8f5c17c2485d17a485a0167ebc1d161ad833147387c8131d3b54126595bb0dbed9ef0d16e72c0c0c577e0ae68dfb06c8af810621f9fe0122554d
  | 7, 1 => 0xff33d146fee14d72fe971ab2fba0a51cfaa3a2ccf9554771f542c7dcf29bf981edbd194fec58a0dbebacd05deaac3b0be7baf5ffe45de151e1edd638df1b03fdde7c5035dccedae9dc851221dc5b1b28db27b5cbda5e734ed95733d7d7ca020fd7c3a15ed71460e3d6a4388ccea8ef3bcdc8ba32ca94fea2c8357a45c68acfd0c5ca4838c43bc065c3827a75c09467eac08ae272b7aa7e56b19e29acb0316723afe37ca7af99e6ccaa7319c3a837e8f9a6ea9da8a6bea662a3dc3944a3bebdf8a07a6a939c0a3ca09a79e24f976de83c96f519d99437159c91ffdd0791869cbe911bcb618ff96af68726336285cf5b4385a3bc0f
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x1000000000000000000000000010000000000001000000000000100000000000010000000000000000000000000100000000000000000000000000000000000000100000000000000000000000000000000000000000000000000010000000000001000000000000100000000000010000000000000000000000000000000000000000000000000001000000000000000000000000000000000000001000000000000000000000000010000000000000000000000000000000000000000000000000001
  | 6, 1 => 0x10000000000001000000000000100000000000010000000000001000000000000100000000000000000000000000000000000000100000000000010000000000000000000000000000000000000010000000000000000000000000100000000000000000000000001000000000000100000000000000000000000000000000000000100000000000010000000000000000000000000100000000000010000000000000000000000000100000000000000000000000000000000000000100000000000010000000000001
  | 6, 2 => 0x1000000000000100000000000010000000000000000000000000100000000000010000000000001000000000000100000000000010000000000001000000000000100000000000000000000000000000000000000100000000000010000000000000000000000000100000000000000000000000001000000000000100000000000000000000000001000000000000100000000000010000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000
  | 6, 3 => 0x1000000000000100000000000010000000000001000000000000000000000000010000000000000000000000000100000000000000000000000001000000000000000000000000010000000000000000000000000100000000000010000000000001000000000000000000000000000000000000001000000000000100000000000010000000000000000000000000000000000000010000000000000000000000000100000000000000000000000000000000000000100000000000010000000000001
  | 6, 4 => 0x1000000000000100000000000000000000000001
  | 7, 0 => 0x10000000000001000000000000000000000000000000000000001000000000000100000000000000000000000000000000000000100000000000010000000000000000000000000100000000000010000000000000000000000000000000000000000000000000001000000000000100000000000000000000000001000000000000100000000000010000000000001000000000000100000000000010000000000001000000000000000000000000010000000000001000000000000000000000000000000000000000
  | 7, 1 => 0x100000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000001000000000000100000000000010000000000001000000000000100000000000000000000000000000000000000100000000000010000000000000000000000000100000000000010000000000001000000000000000000000000000000000000000000000000000100000000000010000000000001000000000000000000000000000000000000000
  | 7, 2 => 0x10000000000000000000000000000000000000000000000000001000000000000100000000000010000000000001000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000100000000000010000000000001000000000000000000000000000000000000000000000000000100000000000000000000000001000000000000100000000000010000000000000000000000000000000000000010000000000001
  | 7, 3 => 0x10000000000000000000000000000000000000000000000000000000000000000100000000000000000000000001000000000000100000000000000000000000001000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000100000000000000000000000001000000000000100000000000000000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_59 roots_59 6 s ws hint
  | 1 => checkCutEntry dom_47 roots_47 6 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : ∀ i, 48 ≤ i → i < 64 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_64 : ∀ i, 64 ≤ i → i < 80 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_80 : ∀ i, 80 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_96 : ∀ i, 96 ≤ i → i < 109 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 96 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 109 → Z 5 i = true := (range_split (range_split z5_0 (range_split z5_16 z5_32)) (range_split (range_split z5_48 z5_64) (range_split z5_80 z5_96)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_80 : ∀ i, 80 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 112 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_112 : ∀ i, 112 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : ∀ i, 144 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_160 : ∀ i, 160 ≤ i → i < 176 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_176 : ∀ i, 176 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 208 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_208 : ∀ i, 208 ≤ i → i < 224 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_224 : ∀ i, 224 ≤ i → i < 240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_240 : ∀ i, 240 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_256 : ∀ i, 256 ≤ i → i < 272 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_272 : ∀ i, 272 ≤ i → i < 288 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_288 : ∀ i, 288 ≤ i → i < 304 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_304 : ∀ i, 304 ≤ i → i < 320 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_320 : ∀ i, 320 ≤ i → i < 336 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_336 : ∀ i, 336 ≤ i → i < 352 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_352 : ∀ i, 352 ≤ i → i < 368 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_368 : ∀ i, 368 ≤ i → i < 384 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_384 : ∀ i, 384 ≤ i → i < 400 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_400 : ∀ i, 400 ≤ i → i < 416 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_416 : ∀ i, 416 ≤ i → i < 432 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_432 : ∀ i, 432 ≤ i → i < 448 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_448 : ∀ i, 448 ≤ i → i < 464 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_464 : ∀ i, 464 ≤ i → i < 480 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_480 : ∀ i, 480 ≤ i → i < 496 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_496 : ∀ i, 496 ≤ i → i < 512 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_512 : ∀ i, 512 ≤ i → i < 528 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_528 : ∀ i, 528 ≤ i → i < 544 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_544 : ∀ i, 544 ≤ i → i < 560 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_560 : ∀ i, 560 ≤ i → i < 576 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_576 : ∀ i, 576 ≤ i → i < 592 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_592 : ∀ i, 592 ≤ i → i < 608 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_608 : ∀ i, 608 ≤ i → i < 624 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_624 : ∀ i, 624 ≤ i → i < 640 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_640 : ∀ i, 640 ≤ i → i < 656 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_656 : ∀ i, 656 ≤ i → i < 672 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_672 : ∀ i, 672 ≤ i → i < 688 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_688 : ∀ i, 688 ≤ i → i < 704 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_704 : ∀ i, 704 ≤ i → i < 717 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 13 704 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 717 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 (range_split z6_48 z6_64))) (range_split (range_split z6_80 (range_split z6_96 z6_112)) (range_split z6_128 (range_split z6_144 z6_160)))) (range_split (range_split (range_split z6_176 z6_192) (range_split z6_208 (range_split z6_224 z6_240))) (range_split (range_split z6_256 (range_split z6_272 z6_288)) (range_split z6_304 (range_split z6_320 z6_336))))) (range_split (range_split (range_split (range_split z6_352 z6_368) (range_split z6_384 (range_split z6_400 z6_416))) (range_split (range_split z6_432 (range_split z6_448 z6_464)) (range_split z6_480 (range_split z6_496 z6_512)))) (range_split (range_split (range_split z6_528 (range_split z6_544 z6_560)) (range_split z6_576 (range_split z6_592 z6_608))) (range_split (range_split z6_624 (range_split z6_640 z6_656)) (range_split z6_672 (range_split z6_688 z6_704))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_80 : ∀ i, 80 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_112 : ∀ i, 112 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : ∀ i, 144 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_160 : ∀ i, 160 ≤ i → i < 176 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_176 : ∀ i, 176 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 208 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_208 : ∀ i, 208 ≤ i → i < 224 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_224 : ∀ i, 224 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : ∀ i, 240 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 272 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_272 : ∀ i, 272 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_288 : ∀ i, 288 ≤ i → i < 304 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_304 : ∀ i, 304 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_336 : ∀ i, 336 ≤ i → i < 352 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_352 : ∀ i, 352 ≤ i → i < 368 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_368 : ∀ i, 368 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 400 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_400 : ∀ i, 400 ≤ i → i < 416 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_416 : ∀ i, 416 ≤ i → i < 432 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_432 : ∀ i, 432 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_448 : ∀ i, 448 ≤ i → i < 464 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_464 : ∀ i, 464 ≤ i → i < 480 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_480 : ∀ i, 480 ≤ i → i < 496 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_496 : ∀ i, 496 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_512 : ∀ i, 512 ≤ i → i < 528 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_528 : ∀ i, 528 ≤ i → i < 544 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_544 : ∀ i, 544 ≤ i → i < 560 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_560 : ∀ i, 560 ≤ i → i < 576 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_576 : ∀ i, 576 ≤ i → i < 592 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_592 : ∀ i, 592 ≤ i → i < 608 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_608 : ∀ i, 608 ≤ i → i < 624 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_624 : ∀ i, 624 ≤ i → i < 640 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_640 : ∀ i, 640 ≤ i → i < 646 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 640 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 646 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 (range_split z7_48 z7_64))) (range_split (range_split z7_80 z7_96) (range_split z7_112 (range_split z7_128 z7_144)))) (range_split (range_split (range_split z7_160 z7_176) (range_split z7_192 (range_split z7_208 z7_224))) (range_split (range_split z7_240 z7_256) (range_split z7_272 (range_split z7_288 z7_304))))) (range_split (range_split (range_split (range_split z7_320 z7_336) (range_split z7_352 (range_split z7_368 z7_384))) (range_split (range_split z7_400 z7_416) (range_split z7_432 (range_split z7_448 z7_464)))) (range_split (range_split (range_split z7_480 z7_496) (range_split z7_512 (range_split z7_528 z7_544))) (range_split (range_split z7_560 (range_split z7_576 z7_592)) (range_split z7_608 (range_split z7_624 z7_640))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 44 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 32 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 44 → Z 8 i = true := (range_split z8_0 (range_split z8_16 z8_32))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
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
  scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_63 roots_63 goal_63 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_63 := by
    have h0 : isConstB dom_63 goal_63 = false := by decide +kernel
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

end S_63

theorem low_63 : Lower dom_63 roots_63 goal_63 10 := S_63.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_63_bits : ∀ r : Fin 64, roots_63.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_63_lt : ∀ r : Fin 64, dom_63.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_63 T)
    (hlow : Lower dom_63 roots_63 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_63, Avail mask256 roots_63 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_63 hfan 0 roots_63 roots_63 rfl hsup0
  set out := (execN C.gates roots_63).getD C.output 0
  have hout : out &&& dom_63 = T &&& dom_63 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_63_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_63 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_63_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_63).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_63)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_63.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_63 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_63).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_63 &&& mask256 = dom_63 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_63 = T &&& dom_63 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63, hout]
  have hnc_m : ¬ IsConst dom_63 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_63 roots_63 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_63 roots_63 0 roots_63 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 14]⟩], 15⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 10 := by decide

theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4007717088 * 2 ^ 32 + 3938502848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4007717088 * 2 ^ 32 + 3938502848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717088 * 2 ^ 32 + 3938502848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 10 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4007717088 * 2 ^ 32 + 3938502848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 10 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_15651_aux

theorem PEqualNP.Outside.L_meta_15651 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717088 * 2 ^ 32 + 3938502848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717088 * 2 ^ 32 + 3938502848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_15651_aux.wit, PEqualNP.Outside.L_meta_15651_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_15651_aux.wit_sz (PEqualNP.Outside.L_meta_15651_aux.lower s hs), PEqualNP.Outside.L_meta_15651_aux.wit_ev⟩
