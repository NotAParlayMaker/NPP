import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3334_37
    (firstBound : ∀ (m : Nat) (op : Fin m → Bool) (a b : Fin m → Nat × Bool)
    (out : Nat × Bool) (w : (Fin 9 → Bool) → Nat → Bool), m ≤ 12 →
    (∀ j, (a j).1 < 10+j.val ∧ (b j).1 < 10+j.val) → out.1 < 10+m →
    (∀ x (i : Fin 9),w x i.val = x i) → (∀ x,w x 9 = false) →
    (∀ x j, let v := fun p : Nat × Bool => w x p.1 ^^ p.2
       w x (10+j.val) = if op j then v (a j) && v (b j) else v (a j) || v (b j)) →
    ∃ x, (w x out.1 ^^ out.2) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (canonical : ∀ (n c t : Nat) (root : Bool) (op : Fin n → Bool) (a b : Fin n → Nat × Bool)
    (w : (Fin 9 → Bool) → Nat → Bool), 12 ≤ n → n ≤ 13 → 10 ≤ t → t < 9+n →
    (∀ j, (a j).1 < 10+j.val ∧ (b j).1 < 10+j.val) →
    (∀ j, ∀ p∈[a j,b j], p.2=true → p.1=0 ∨ p.1=9 ∨ (n=12 ∧ p.1=c)) →
    (∀ x (i : Fin 9),w x i.val = x i) → (∀ x,w x 9 = false) →
    (∀ x j, let v := fun p : Nat × Bool => w x p.1 ^^ p.2
       w x (10+j.val) = if op j then v (a j) && v (b j) else v (a j) || v (b j)) →
    (∀ bit : Bool, ∃ x, w x t=bit ∧ w x (9+n)=!bit) →
    ¬∀ x, (if root then w x t && w x (9+n) else w x t || w x (9+n)) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => List.foldl (fun (x2 : Bool) (x3 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x2 || x1 x3.1 && x1 x3.2) Bool.false [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))]; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ)) → Bool) (x4 x5 : Fin (x2 + (1 : ℕ)) → ℕ × Bool) (x6 : Bool) (x7 : Finset ℕ) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x7.card ≤ (3 : ℕ) →     x2 + (1 : ℕ) + x7.card ≤ (14 : ℕ) →       (∀ (x11 : Fin (x2 + (1 : ℕ))), (x4 x11).1 < (10 : ℕ) + ↑x11 ∧ (x5 x11).1 < (10 : ℕ) + ↑x11) →         (have x12 : ℕ × Bool → Prop := fun (x12 : ℕ × Bool) => x12.2 = Bool.true → x12.1 = (0 : ℕ) ∨ x12.1 = (9 : ℕ) ∨ x12.1 ∈ x7;           x12 ((10 : ℕ) + x2, x6) ∧ ∀ (x13 : Fin (x2 + (1 : ℕ))), x12 (x4 x13) ∧ x12 (x5 x13)) →           (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x8 x13 ↑x14 = x13 x14) →             (∀ (x14 : Fin (9 : ℕ) → Bool), x8 x14 (9 : ℕ) = Bool.false) →               (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (x2 + (1 : ℕ))),                   have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x8 x15 x17.1 ^^ x17.2;                   x8 x15 ((10 : ℕ) + ↑x16) = if x3 x16 = Bool.true then x17 (x4 x16) && x17 (x5 x16) else x17 (x4 x16) || x17 (x5 x16)) →                 (9 : ℕ) ≤ (x4 (Fin.last x2)).1 → (9 : ℕ) ≤ (x5 (Fin.last x2)).1 → ¬∀ (x18 : Fin (9 : ℕ) → Bool), (x8 x18 ((10 : ℕ) + x2) ^^ x6) = x1 x18 := by
  let F (x : (Fin 9 → Bool)) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
      x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let bound (s high : Bool) (i : Fin 9) : Bool := if i=0 then s else high
  have edgeLow (s : Bool) : F (bound s false) = false := by cases s <;> rfl
  have edgeHigh (s : Bool) : F (bound s true) = true := by cases s <;> rfl
  let ord (x y : (Fin 9 → Bool)) := x 0 = y 0 ∧ ∀ i, x i = true → y i = true
  have lowOrd (x : (Fin 9 → Bool)) : ord (bound (x 0) false) x := by
    refine ⟨by simp [bound],?_⟩; intro i h
    by_cases hi : i=0
    · subst i;exact h
    · simp [bound,hi] at h
  have highOrd (x : (Fin 9 → Bool)) : ord x (bound (x 0) true) := by
    refine ⟨by simp [bound],?_⟩; intro i h
    by_cases hi : i=0
    · subst i;exact h
    · simp [bound,hi]
  let ev (w : (Fin 9 → Bool) → Nat → Bool) (x : (Fin 9 → Bool)) (p : (Nat × Bool)) := w x p.1 ^^ p.2
  let comb (op u v : Bool) := if op then u && v else u || v
  let wires {m : Nat} (a b : Fin m → (Nat × Bool)) :=
    ∀ j, (a j).1 < 10+j.val ∧ (b j).1 < 10+j.val
  let legal (paid : Finset Nat) (p : (Nat × Bool)) := p.2 = true → p.1=0 ∨ p.1=9 ∨ p.1∈paid
  let emits {m : Nat} (op : Fin m → Bool) (a b : Fin m → (Nat × Bool)) (w : (Fin 9 → Bool) → Nat → Bool) :=
    ∀ x j, w x (10+j.val) = comb (op j) (ev w x (a j)) (ev w x (b j))
  let small := ∀ (m : Nat) (op : Fin m → Bool) (a b : Fin m → (Nat × Bool)) (out : (Nat × Bool)) (w : (Fin 9 → Bool) → Nat → Bool),
    m ≤ 12 → wires a b → out.1 < 10+m → (∀ x (i : Fin 9),w x i.val = x i) →
    (∀ x,w x 9 = false) → emits op a b w → ∃ x, ev w x out ≠ F x
  have monotone {m : Nat} (op : Fin m → Bool) (a b : Fin m → (Nat × Bool)) (w : (Fin 9 → Bool) → Nat → Bool)
      (paid : Finset Nat) (c : Nat) (hc : ∀ t ∈ paid, t=c)
      (ww : wires a b) (ok : ∀ j, legal paid (a j) ∧ legal paid (b j))
      (raw : ∀ x (i : Fin 9), w x i.val = x i) (zero : ∀ x, w x 9 = false) (ee : emits op a b w)
      (x y : (Fin 9 → Bool)) (xy : ord x y) (i : Nat) (ic : i ≤ c) (im : i < 10+m) :
      w x i = true → w y i = true := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases hi : i < 9
      · let t : Fin 9 := ⟨i,hi⟩
        change w x t.val = true → w y t.val = true
        rw [raw,raw]; exact xy.2 t
      by_cases h9 : i = 9
      · subst i; simp [zero]
      let j : Fin m := ⟨i-10,by omega⟩
      have ji : 10+j.val = i := by dsimp [j];omega
      have pin (p : (Nat × Bool)) (lt : p.1 < i) (pp : legal paid p) : ev w x p = true → ev w y p = true := by
        cases sig : p.2 with
        | false => simpa [ev,sig] using (ih p.1 lt (by omega) (by omega))
        | true =>
          rcases pp sig with h|h|h
          · have same : w x 0 = w y 0 := (raw x 0).trans (xy.1.trans (raw y 0).symm)
            simp [ev,h,same]
          · simp [ev,h,zero]
          · have := hc _ h; omega
      have pa := pin (a j) (by simpa only [← ji] using (ww j).1) (ok j).1
      have pb := pin (b j) (by simpa only [← ji] using (ww j).2) (ok j).2
      have ex := ee x j
      have ey := ee y j
      rw [ji] at ex ey
      rw [ex,ey]
      cases op j <;> simp only [comb,Bool.false_eq_true,ite_false,ite_true,Bool.or_eq_true,Bool.and_eq_true]
      · exact Or.imp pa pb
      · exact And.imp pa pb
  have unique (s : Finset Nat) (lim : s.card ≤ 1) (c : Nat) (mem : c∈s) : ∀ t∈s,t=c := by
    obtain ⟨v,hv⟩ := Finset.card_le_one_iff_subset_singleton.mp lim
    have hx := Finset.mem_singleton.mp (hv mem)
    intro i hi; exact (Finset.mem_singleton.mp (hv hi)).trans hx.symm
  have neutral (op : Bool) (u v : (Fin 9 → Bool) → Bool) (E : ∀ x, comb op (u x) (v x) = F x)
      (anti : ∀ x y, ord x y → u y = true → u x = true) : ∀ x, v x = F x := by
    intro x
    cases h : op with
    | true =>
      have et := E (bound (x 0) true)
      rw [edgeHigh] at et
      have uh : u (bound (x 0) true) = true := (Bool.and_eq_true_iff.mp (by simpa [comb,h] using et)).1
      have ux := anti _ _ (highOrd x) uh
      simpa [comb,h,ux] using E x
    | false =>
      have et := E (bound (x 0) false)
      rw [edgeLow] at et
      have ul : u (bound (x 0) false) = false := by
        cases hh : u (bound (x 0) false)
        · rfl
        · simp [comb,h,hh] at et
      have ux : u x = false := by
        cases hh : u x
        · rfl
        · have := anti _ _ (lowOrd x) hh; simp [ul] at this
      simpa [comb,h,ux] using E x
  have terminal (lo : small) (n : Nat) (op : Fin (n+1) → Bool) (a b : Fin (n+1) → (Nat × Bool))
      (sign : Bool) (paid : Finset Nat) (w : (Fin 9 → Bool) → Nat → Bool) (budget : n+1+paid.card ≤ 14)
      (ww : wires a b) (out : legal paid (10+n,sign)) (ok : ∀ j, legal paid (a j) ∧ legal paid (b j))
      (raw : ∀ x (i : Fin 9), w x i.val = x i) (zero : ∀ x, w x 9 = false) (ee : emits op a b w)
      (al : 9 ≤ (a (Fin.last n)).1) (bl : 9 ≤ (b (Fin.last n)).1)
      (correct : ∀ x, (w x (10+n) ^^ sign) = F x) :
      12 ≤ n ∧ sign = false ∧
        ∀ p ∈ [a (Fin.last n), b (Fin.last n)], 9 ≤ p.1 ∧ (p.1=9 → n=13) ∧ (p.2=true → p.1=9) := by
    have low : 12 ≤ n := by
      by_contra! bad
      obtain ⟨x,hx⟩ := lo (n+1) op a b (10+n,sign) w (by omega) ww (by simp) raw zero ee
      exact hx (correct x)
    have size : paid.card ≤ 1 := by omega
    have pos : sign = false := by
      cases hh : sign with
      | false => rfl
      | true =>
        have mem : 10+n ∈ paid := by rcases out hh with h|h|h <;> first | omega | exact h
        let x := bound false false
        let y := bound false true
        have xy : ord x y := by simpa [x,y,bound] using lowOrd (bound false true)
        have m := monotone op a b w paid (10+n) (unique paid size _ mem) ww ok raw zero ee x y xy
          (10+n) (by omega) (by omega)
        have rx := correct x
        have ry := correct y
        rw [show F x=false from edgeLow _,hh] at rx
        rw [show F y=true from edgeHigh _,hh] at ry
        have wx : w x (10+n) = true := by
          cases hx : w x (10+n)
          · simp [hx] at rx
          · rfl
        have wy := m wx
        simp [wy] at ry
    refine ⟨low,pos,?_⟩
    let k := Fin.last n
    have seen (p q : (Nat × Bool)) (ltp : p.1 < 10+n) (ltq : q.1 < 10+n)
        (pl : 9 ≤ p.1) (allow : legal paid p)
        (E : ∀ x, comb (op k) (ev w x p) (ev w x q) = F x) :
        9 ≤ p.1 ∧ (p.1=9 → n=13) ∧ (p.2=true → p.1=9) := by
      have shorten (bn : n≤12) (anti : ∀ x y, ord x y → ev w y p = true → ev w x p = true) : False := by
        have trimmed := neutral (op k) (fun x => ev w x p) (fun x => ev w x q) E anti
        obtain ⟨x,hx⟩ := lo n (fun j => op j.castSucc) (fun j => a j.castSucc)
          (fun j => b j.castSucc) q w bn (fun j => ww j.castSucc) ltq raw zero (fun x j => ee x j.castSucc)
        exact hx (trimmed x)
      refine ⟨pl,?_,?_⟩
      · intro h
        by_contra ne
        apply shorten (by omega)
        intro x y _; simp [ev,h,zero]
      · intro s
        by_contra ne
        have mem : p.1∈paid := by rcases allow s with h|h|h <;> first | omega | assumption
        have positive := Finset.card_pos.mpr ⟨_,mem⟩
        apply shorten (by omega)
        intro x y xy
        have m := monotone op a b w paid p.1 (unique paid size _ mem) ww ok raw zero ee x y xy
          p.1 (by omega) (by omega)
        intro ny
        have fy : w y p.1 = false := by
          cases hy : w y p.1
          · rfl
          · simp [ev,hy,s] at ny
        cases hx : w x p.1
        · simp [ev,hx,s]
        · have yy := m hx; simp [fy] at yy
    have step (x : (Fin 9 → Bool)) : comb (op k) (ev w x (a k)) (ev w x (b k)) = F x := by
      have h := (ee x k).symm
      exact h.trans (by simpa [pos,k] using correct x)
    intro p mem
    rcases (by simpa [k] using mem : p = a k ∨ p = b k) with rfl|rfl
    · exact seen _ _ (ww k).1 (ww k).2 al (ok k).1 step
    · apply seen _ _ (ww k).2 (ww k).1 bl (ok k).2
      intro x
      simpa [comb,Bool.and_comm,Bool.or_comm] using step x
  let slice (i : Fin 9) (s high : Bool) (j : Fin 9) : Bool := if j=i then s else high
  have cofactor : ∀ i : Fin 9, ∀ s : Bool,
      F (slice i s false) = false ∧ F (slice i s true) = true := by decide +kernel
  have noRaw (w : (Fin 9 → Bool) → Nat → Bool) (raw : ∀ x (i : Fin 9),w x i.val=x i) (p q : (Nat × Bool))
      (op sign : Bool) (E : ∀ x, (comb op (ev w x p) (ev w x q) ^^ sign) = F x) : 9 ≤ p.1 := by
    by_contra! h
    let i : Fin 9 := ⟨p.1,h⟩
    let s := (!op) ^^ p.2
    have force (t v : Bool) : comb op (((!op) ^^ t) ^^ t) v = !op := by cases op <;> cases t <;> rfl
    have same (hi : Bool) : F (slice i s hi) = ((!op) ^^ sign) := by
      rw [← E]
      have hp : w (slice i s hi) p.1 = s := (raw (slice i s hi) i).trans (by simp [slice])
      simp only [ev,hp,s,force]
    have z := (same false).trans (same true).symm
    rw [(cofactor i s).1,(cofactor i s).2] at z
    contradiction
  let witness (m : Nat) := ∃ (op : Fin m → Bool) (a b : Fin m → (Nat × Bool)) (out : (Nat × Bool)) (paid : Finset Nat)
      (w : (Fin 9 → Bool) → Nat → Bool), m+paid.card ≤ 14 ∧ wires a b ∧ out.1 < 10+m ∧ legal paid out ∧
      (∀ j,legal paid (a j) ∧ legal paid (b j)) ∧ (∀ x (i : Fin 9),w x i.val=x i) ∧
      (∀ x,w x 9=false) ∧ emits op a b w ∧ ∀ x, ev w x out = F x
  have dropUnused (n : Nat) (op : Fin (n+2) → Bool) (a b : Fin (n+2) → (Nat × Bool)) (w : (Fin 9 → Bool) → Nat → Bool)
      (paid : Finset Nat) (budget : n+2+paid.card≤14) (ww : wires a b)
      (ok : ∀ j,legal paid (a j) ∧ legal paid (b j)) (raw : ∀ x (i : Fin 9),w x i.val=x i)
      (zero : ∀ x,w x 9=false) (ee : emits op a b w) (correct : ∀ x,w x (10+(n+1)) = F x)
      (la : (a (Fin.last (n+1))).1 < 10+n) (lb : (b (Fin.last (n+1))).1 < 10+n) : witness (n+1) := by
    let idx : Fin (n+1) → Fin (n+2) := fun j => if j.val=n then Fin.last (n+1) else j.castSucc
    let v := fun (x : (Fin 9 → Bool)) (i : Nat) => if i=10+n then w x (10+(n+1)) else w x i
    have bk (j : Fin (n+1)) : (a (idx j)).1 < 10+j.val ∧ (b (idx j)).1 < 10+j.val := by
      by_cases h : j.val=n
      · simpa [idx,h] using And.intro la lb
      · simpa [idx,h] using ww j.castSucc
    refine ⟨fun j => op (idx j),fun j => a (idx j),fun j => b (idx j),(10+n,false),paid,v,
      by omega,bk,by simp,by simp [legal],fun j => ok (idx j),?_,?_,?_,?_⟩
    · intro x i
      have h : i.val ≠ 10+n := by have := i.isLt;omega
      simpa [v,h] using raw x i
    · intro x; simpa [v,show 9≠10+n by omega] using zero x
    · intro x j
      have ha : (a (idx j)).1 ≠ 10+n := by have := (bk j).1;have := j.isLt;omega
      have hb : (b (idx j)).1 ≠ 10+n := by have := (bk j).2;have := j.isLt;omega
      have base := ee x (idx j)
      change v x (10+j.val) = comb (op (idx j)) (ev v x (a (idx j))) (ev v x (b (idx j)))
      simp only [ev,v,if_neg ha,if_neg hb]
      by_cases h : j.val=n
      · simpa [idx,h,ev] using base
      · simpa [idx,h,ev] using base
    · intro x; simpa [ev,v] using correct x
  let hard := ∀ (n c t : Nat) (root : Bool) (op : Fin n → Bool) (a b : Fin n → (Nat × Bool)) (w : (Fin 9 → Bool) → Nat → Bool),
    12 ≤ n → n ≤ 13 → 10 ≤ t → t < 9+n → wires a b →
    (∀ j, ∀ p∈[a j,b j], p.2=true → p.1=0 ∨ p.1=9 ∨ (n=12 ∧ p.1=c)) →
    (∀ x (i : Fin 9),w x i.val=x i) → (∀ x,w x 9=false) → emits op a b w →
    (∀ bit : Bool, ∃ x, w x t=bit ∧ w x (9+n)=!bit) →
    ¬∀ x, comb root (w x t) (w x (9+n)) = F x
  have noWitness (lo : small) (H : hard) (existsW : ∃ m,witness m) : False := by
    classical
    let m := Nat.find existsW
    have hm : witness m := Nat.find_spec existsW
    have least : ∀ k < m, ¬witness k := fun k hk => Nat.find_min existsW hk
    obtain ⟨op,a,b,out,paid,w,budget,ww,ol,outOk,ok,raw,zero,ee,correct⟩ := hm
    have ml : 13 ≤ m := by
      by_contra! lt
      obtain ⟨x,hx⟩ := lo m op a b out w (by omega) ww ol raw zero ee
      exact hx (correct x)
    generalize eq : m = m' at *
    clear eq
    rcases m' with _|n
    · omega
    have prev (p : (Nat × Bool)) (lp : p.1 < 10+n) (kp : legal paid p) (eq : ∀ x, ev w x p = F x) : False := by
      apply least n (by omega)
      exact ⟨fun j => op j.castSucc,fun j => a j.castSucc,fun j => b j.castSucc,p,paid,w,by omega,
        fun j => ww j.castSucc,lp,kp,fun j => ok j.castSucc,raw,zero,fun x j => ee x j.castSucc,eq⟩
    have outEq : out.1 = 10+n := by by_contra ne; exact prev out (by omega) outOk correct
    let k := Fin.last n
    have eg (x : (Fin 9 → Bool)) : (comb (op k) (ev w x (a k)) (ev w x (b k)) ^^ out.2) = F x := by
      rw [← ee]; simpa only [ev,outEq,k,Fin.val_last] using correct x
    have swap (op a b : Bool) : comb op a b = comb op b a := by
      cases op <;> simp [comb,Bool.or_comm,Bool.and_comm]
    have swapped (x : (Fin 9 → Bool)) : (comb (op k) (ev w x (b k)) (ev w x (a k)) ^^ out.2)=F x := by
      rw [swap];exact eg x
    have left := noRaw w raw (a k) (b k) (op k) out.2 eg
    have right := noRaw w raw (b k) (a k) (op k) out.2 swapped
    have actual (x : (Fin 9 → Bool)) : (w x (10+n) ^^ out.2) = F x := by simpa only [ev,outEq] using correct x
    obtain ⟨nlo,pos,pins⟩ := terminal lo n op a b out.2 paid w budget ww (by
      simpa only [← outEq,Prod.mk.eta] using outOk) ok raw zero ee left right actual
    have rootEq (x : (Fin 9 → Bool)) : comb (op k) (ev w x (a k)) (ev w x (b k)) = F x := by
      simpa only [pos,Bool.xor_false] using eg x
    have nonconstant (p q : (Nat × Bool)) (lp : 9 ≤ p.1) (lq : q.1 < 10+n) (kq : legal paid q)
        (E : ∀ x,comb (op k) (ev w x p) (ev w x q)=F x) : 10 ≤ p.1 := by
      by_contra! lt
      have pe : p.1=9 := by omega
      apply prev q lq kq
      apply neutral _ _ _ E
      intro x y _;simp [ev,pe,zero]
    have ala := nonconstant _ _ left (ww k).2 (ok k).2 rootEq
    have alb := nonconstant _ _ right (ww k).1 (ok k).1 (fun x => (swap _ _ _).trans (rootEq x))
    have signA : (a k).2=false := by
      cases e : (a k).2
      · rfl
      · have h := (pins (a k) (by simp [k])).2.2 e;omega
    have signB : (b k).2=false := by
      cases e : (b k).2
      · rfl
      · have h := (pins (b k) (by simp [k])).2.2 e;omega
    have valEq (x : (Fin 9 → Bool)) : comb (op k) (w x (a k).1) (w x (b k).1)=F x := by
      simpa only [ev,signA,signB,Bool.xor_false] using rootEq x
    have diff : (a k).1 ≠ (b k).1 := by
      intro eq
      apply prev (b k) (ww k).2 (ok k).2
      intro x
      have h := valEq x
      rw [eq] at h
      cases oo : op k <;> simpa [oo,comb,ev,signB] using h
    have useLast : (a k).1 = 9+n ∨ (b k).1 = 9+n := by
      by_contra! bad
      have wa := (ww k).1
      have wb := (ww k).2
      change (a k).1 < 10+n at wa
      change (b k).1 < 10+n at wb
      cases n with
      | zero => omega
      | succ t =>
        exact least (t+1) (by omega) (dropUnused t op a b w paid budget ww ok raw zero ee
          (fun x => by simpa only [pos,Bool.xor_false] using actual x) (by change (a k).1 < _;omega)
          (by change (b k).1 < _;omega))
    obtain ⟨c,sub⟩ := Finset.card_le_one_iff_subset_singleton.mp (show paid.card≤1 by omega)
    have legal' (j : Fin n) (p : (Nat × Bool)) (hp : p∈[a j.castSucc,b j.castSucc]) (sig : p.2=true) :
        p.1=0 ∨ p.1=9 ∨ (n=12 ∧ p.1=c) := by
      have pp : legal paid p := by
        rcases (by simpa using hp : p=a j.castSucc ∨ p=b j.castSucc) with rfl|rfl
        · exact (ok _).1
        · exact (ok _).2
      rcases pp sig with ha|hb|hmem
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
      · have pc := Finset.card_pos.mpr ⟨_,hmem⟩
        exact Or.inr (Or.inr ⟨by omega,Finset.mem_singleton.mp (sub hmem)⟩)
    have separated (p q : Nat) (lp : p < 10+n) (lq : q < 10+n)
        (E : ∀ x,comb (op k) (w x p) (w x q)=F x) : ∃ x,w x p=true ∧ w x q=false := by
      by_contra! no
      have collapse (o u v : Bool) (h : u=true → v=true) : comb o u v = (if o then u else v) := by
        cases o <;> cases u <;> cases v <;> first | rfl | exact False.elim (Bool.noConfusion (h rfl))
      let i := if op k then p else q
      apply prev (i,false) (by dsimp [i];split <;> assumption) (by simp [legal])
      intro x
      have eq := (collapse (op k) (w x p) (w x q) (fun z => by
        have h := no x z; cases v : w x q
        · simp [v] at h
        · rfl)).symm.trans (E x)
      change (w x i ^^ false)=F x
      cases h : op k <;> simpa [i,h] using eq
    have rightSep := separated _ _ (ww k).1 (ww k).2 valEq
    have leftSep := separated _ _ (ww k).2 (ww k).1 (fun x => (swap _ _ _).trans (valEq x))
    have applyH (t : Nat) (tl : 10≤t) (tu : t < 9+n) := H n c t (op k)
      (fun j => op j.castSucc) (fun j => a j.castSucc) (fun j => b j.castSucc) w nlo (by omega)
      tl tu (fun j => ww j.castSucc) legal' raw zero (fun x j => ee x j.castSucc)
    have ha := (ww k).1
    have hb := (ww k).2
    change (a k).1 < 10+n at ha
    change (b k).1 < 10+n at hb
    rcases useLast with last|last
    · apply applyH _ alb (by omega)
      · rw [← last]
        intro bit
        cases bit
        · obtain ⟨x,ha,hb⟩ := rightSep;exact ⟨x,hb,ha⟩
        · exact leftSep
      intro x
      rw [← last,swap];exact valEq x
    · apply applyH _ ala (by omega)
      · rw [← last]
        intro bit
        cases bit
        · obtain ⟨x,ha,hb⟩ := leftSep;exact ⟨x,hb,ha⟩
        · exact rightSep
      intro x
      rw [← last];exact valEq x
  dsimp only
  intro n op a b sign paid w _ budget reads allowed raw zero gate _ _ correct
  apply noWitness firstBound canonical
  refine ⟨n+1,op,a,b,(10+n,sign),paid,w,budget,reads,by simp,allowed.1,allowed.2,raw,zero,gate,?_⟩
  intro x
  have hx := correct x
  simpa only [F,List.foldl_cons,List.foldl_nil,Bool.false_or] using hx
