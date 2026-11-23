import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open Turing PEqualNP.Search

abbrev L500G : Fin 8 → Type := fun _ => Bool

abbrev L500S := TM2.Stmt L500G (Fin 16) (Option Bool)

def L500pop (k : Fin 8) (q : L500S) : L500S := TM2.Stmt.pop k (fun _ o => o) q
def L500psh (k : Fin 8) (q : L500S) : L500S := TM2.Stmt.push k (fun s => s.getD false) q
def L500pc (k : Fin 8) (b : Bool) (q : L500S) : L500S := TM2.Stmt.push k (fun _ => b) q
def L500go (l : Fin 16) : L500S := TM2.Stmt.goto (fun _ => l)
def L500br (b : Bool) (q₁ q₂ : L500S) : L500S :=
  TM2.Stmt.branch (fun s => decide (s = some b)) q₁ q₂
def L500mv (a b : Fin 8) (l l' : Fin 16) : L500S :=
  L500pop a (TM2.Stmt.branch (fun s => s.isSome) (L500psh b (L500go l)) (L500go l'))

def L500prog : Fin 16 → L500S
  | 0 => L500pop 0 (TM2.Stmt.branch (fun s => s.isSome)
      (L500psh 1 (L500br true
        (L500pop 0 (L500psh 1 (L500pc 7 true (L500psh 7 (L500go 1)))))
        (L500pop 0 (L500psh 1 (L500pc 7 false (L500psh 7 (L500go 0)))))))
      (L500go 13))
  | 1 => L500pop 0 (L500psh 1 (L500br true
      (L500pop 0 (L500psh 1 (L500psh 4 (L500go 1))))
      (L500pop 0 (L500psh 1 (L500go 2)))))
  | 2 => L500mv 4 3 2 3
  | 3 => L500mv 1 2 3 4
  | 4 => L500pop 2 (L500psh 1 (L500br true
      (L500pop 2 (L500psh 1 (L500go 5)))
      (L500pop 2 (L500psh 1 (L500go 8)))))
  | 5 => L500pop 2 (L500psh 1 (L500br true
      (L500pop 2 (L500psh 1 (L500br true
        (L500pop 3 (TM2.Stmt.branch (fun s => s.isSome)
          (L500psh 4 (L500br true (L500go 5) (L500go 6))) (L500go 6)))
        (L500pop 3 (TM2.Stmt.branch (fun s => s.isSome)
          (L500psh 4 (L500br false (L500go 5) (L500go 6))) (L500go 6))))))
      (L500pop 2 (L500psh 1 (TM2.Stmt.peek 3 (fun _ o => o)
        (TM2.Stmt.branch (fun s => s.isSome) (L500go 7) (L500go 10)))))))
  | 6 => L500pop 2 (L500psh 1 (L500br true
      (L500pop 2 (L500psh 1 (L500go 6)))
      (L500pop 2 (L500psh 1 (L500go 7)))))
  | 7 => L500mv 4 3 7 8
  | 8 => L500pop 5 (L500br true (L500pc 6 false (L500go 8)) (L500pc 5 true (L500go 9)))
  | 9 => L500mv 6 5 9 4
  | 10 => L500mv 2 1 10 11
  | 11 => L500pop 5 (TM2.Stmt.branch (fun s => s.isSome)
      (L500pc 7 true (L500psh 7 (L500go 11))) (L500pc 7 false (L500pc 7 true (L500go 12))))
  | 12 => L500pop 4 (TM2.Stmt.branch (fun s => s.isSome) (L500go 12) (L500go 0))
  | 13 => L500mv 7 0 13 14
  | 14 => L500pop 1 (TM2.Stmt.branch (fun s => s.isSome) (L500go 14)
      (TM2.Stmt.load (fun _ => none) TM2.Stmt.halt))
  | _ => TM2.Stmt.halt

def L500V (i d g w x c t o : List Bool) : Fin 8 → List Bool := ![i, d, g, w, x, c, t, o]

abbrev L500C := TM2.Cfg L500G (Fin 16) (Option Bool)

def L500R (n : ℕ) (l : Fin 16) (S : Fin 8 → List Bool) (l' : Fin 16)
    (S' : Fin 8 → List Bool) : Prop :=
  ∀ v : Option Bool, ∃ v' : Option Bool,
    (flip bind (TM2.step L500prog))^[n] (some (⟨some l, v, S⟩ : L500C)) = some ⟨some l', v', S'⟩

def L500B (b : ℕ) (l : Fin 16) (S : Fin 8 → List Bool) (l' : Fin 16)
    (S' : Fin 8 → List Bool) : Prop :=
  ∃ n ≤ b, L500R n l S l' S'

theorem L500B_trans {b₁ b₂ : ℕ} {l l' l'' : Fin 16} {S S' S'' : Fin 8 → List Bool}
    (h₁ : L500B b₁ l S l' S') (h₂ : L500B b₂ l' S' l'' S'') : L500B (b₁ + b₂) l S l'' S'' := by
  obtain ⟨n₁, hn₁, h₁⟩ := h₁
  obtain ⟨n₂, hn₂, h₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, fun v => ?_⟩
  obtain ⟨v₁, e₁⟩ := h₁ v
  obtain ⟨v₂, e₂⟩ := h₂ v₁
  exact ⟨v₂, by rw [Function.iterate_add_apply, e₁, e₂]⟩

theorem L500B_mono {b b' : ℕ} {l l' : Fin 16} {S S' : Fin 8 → List Bool}
    (h : L500B b l S l' S') (hb : b ≤ b') : L500B b' l S l' S' := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n, le_trans hn hb, h⟩

theorem L500B_step {l l' : Fin 16} {S S' : Fin 8 → List Bool}
    (h : ∀ v, ∃ v', TM2.step L500prog ⟨some l, v, S⟩ = some ⟨some l', v', S'⟩) :
    L500B 1 l S l' S' := by
  refine ⟨1, le_refl _, fun v => ?_⟩
  obtain ⟨v', e⟩ := h v
  exact ⟨v', by simpa [flip] using e⟩

@[simp] theorem L500V0 (i d g w x c t o : List Bool) : L500V i d g w x c t o 0 = i := rfl
@[simp] theorem L500V1 (i d g w x c t o : List Bool) : L500V i d g w x c t o 1 = d := rfl
@[simp] theorem L500V2 (i d g w x c t o : List Bool) : L500V i d g w x c t o 2 = g := rfl
@[simp] theorem L500V3 (i d g w x c t o : List Bool) : L500V i d g w x c t o 3 = w := rfl
@[simp] theorem L500V4 (i d g w x c t o : List Bool) : L500V i d g w x c t o 4 = x := rfl
@[simp] theorem L500V5 (i d g w x c t o : List Bool) : L500V i d g w x c t o 5 = c := rfl
@[simp] theorem L500V6 (i d g w x c t o : List Bool) : L500V i d g w x c t o 6 = t := rfl
@[simp] theorem L500V7 (i d g w x c t o : List Bool) : L500V i d g w x c t o 7 = o := rfl

@[simp] theorem L500U0 (i d g w x c t o y : List Bool) :
    Function.update (L500V i d g w x c t o) 0 y = L500V y d g w x c t o := by
  funext k; fin_cases k <;> rfl
@[simp] theorem L500U1 (i d g w x c t o y : List Bool) :
    Function.update (L500V i d g w x c t o) 1 y = L500V i y g w x c t o := by
  funext k; fin_cases k <;> rfl
@[simp] theorem L500U2 (i d g w x c t o y : List Bool) :
    Function.update (L500V i d g w x c t o) 2 y = L500V i d y w x c t o := by
  funext k; fin_cases k <;> rfl
@[simp] theorem L500U3 (i d g w x c t o y : List Bool) :
    Function.update (L500V i d g w x c t o) 3 y = L500V i d g y x c t o := by
  funext k; fin_cases k <;> rfl
@[simp] theorem L500U4 (i d g w x c t o y : List Bool) :
    Function.update (L500V i d g w x c t o) 4 y = L500V i d g w y c t o := by
  funext k; fin_cases k <;> rfl
@[simp] theorem L500U5 (i d g w x c t o y : List Bool) :
    Function.update (L500V i d g w x c t o) 5 y = L500V i d g w x y t o := by
  funext k; fin_cases k <;> rfl
@[simp] theorem L500U6 (i d g w x c t o y : List Bool) :
    Function.update (L500V i d g w x c t o) 6 y = L500V i d g w x c y o := by
  funext k; fin_cases k <;> rfl
@[simp] theorem L500U7 (i d g w x c t o y : List Bool) :
    Function.update (L500V i d g w x c t o) 7 y = L500V i d g w x c t y := by
  funext k; fin_cases k <;> rfl

theorem L500mvXW (i d g w x c t o : List Bool) :
    L500B (x.length + 1) 2 (L500V i d g w x c t o) 3 (L500V i d g (x.reverse ++ w) [] c t o) := by
  induction x generalizing w with
  | nil =>
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
  | cons a x ih =>
    have h1 : L500B 1 2 (L500V i d g w (a :: x) c t o) 2 (L500V i d g (a :: w) x c t o) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
    have := L500B_trans h1 (ih (a :: w))
    simpa [Nat.add_comm] using this

theorem L500mvDG (i d g w x c t o : List Bool) :
    L500B (d.length + 1) 3 (L500V i d g w x c t o) 4 (L500V i [] (d.reverse ++ g) w x c t o) := by
  induction d generalizing g with
  | nil =>
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
  | cons a d ih =>
    have h1 : L500B 1 3 (L500V i (a :: d) g w x c t o) 3 (L500V i d (a :: g) w x c t o) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
    have := L500B_trans h1 (ih (a :: g))
    simpa [Nat.add_comm] using this

theorem L500mvRS (i d g w x c t o : List Bool) :
    L500B (x.length + 1) 7 (L500V i d g w x c t o) 8 (L500V i d g (x.reverse ++ w) [] c t o) := by
  induction x generalizing w with
  | nil =>
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
  | cons a x ih =>
    have h1 : L500B 1 7 (L500V i d g w (a :: x) c t o) 7 (L500V i d g (a :: w) x c t o) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
    have := L500B_trans h1 (ih (a :: w))
    simpa [Nat.add_comm] using this

theorem L500mvTC (i d g w x c t o : List Bool) :
    L500B (t.length + 1) 9 (L500V i d g w x c t o) 4 (L500V i d g w x (t.reverse ++ c) [] o) := by
  induction t generalizing c with
  | nil =>
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
  | cons a t ih =>
    have h1 : L500B 1 9 (L500V i d g w x c (a :: t) o) 9 (L500V i d g w x (a :: c) t o) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
    have := L500B_trans h1 (ih (a :: c))
    simpa [Nat.add_comm] using this

theorem L500mvGD (i d g w x c t o : List Bool) :
    L500B (g.length + 1) 10 (L500V i d g w x c t o) 11 (L500V i (g.reverse ++ d) [] w x c t o) := by
  induction g generalizing d with
  | nil =>
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
  | cons a g ih =>
    have h1 : L500B 1 10 (L500V i d (a :: g) w x c t o) 10 (L500V i (a :: d) g w x c t o) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
    have := L500B_trans h1 (ih (a :: d))
    simpa [Nat.add_comm] using this

theorem L500mvOI (i d g w x c t o : List Bool) :
    L500B (o.length + 1) 13 (L500V i d g w x c t o) 14 (L500V (o.reverse ++ i) d g w x c t []) := by
  induction o generalizing i with
  | nil =>
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
  | cons a o ih =>
    have h1 : L500B 1 13 (L500V i d g w x c t (a :: o)) 13 (L500V (a :: i) d g w x c t o) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500mv, L500pop, L500psh, L500go]
    have := L500B_trans h1 (ih (a :: i))
    simpa [Nat.add_comm] using this

theorem L500clrX (i d g w x c t o : List Bool) :
    L500B (x.length + 1) 12 (L500V i d g w x c t o) 0 (L500V i d g w [] c t o) := by
  induction x with
  | nil =>
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500go]
  | cons a x ih =>
    have h1 : L500B 1 12 (L500V i d g w (a :: x) c t o) 12 (L500V i d g w x c t o) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500go]
    have := L500B_trans h1 ih
    simpa [Nat.add_comm] using this

theorem L500drain (i g w x c t o : List Bool) : ∀ d : List Bool, ∀ v : Option Bool,
    (flip bind (TM2.step L500prog))^[d.length + 1]
      (some (⟨some 14, v, L500V i d g w x c t o⟩ : L500C)) =
      some ⟨none, none, L500V i [] g w x c t o⟩ := by
  intro d
  induction d with
  | nil =>
    intro v
    simp [flip, TM2.step, TM2.stepAux, L500prog, L500pop, L500go]
  | cons a d ih =>
    intro v
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step L500prog) (some (⟨some 14, v, L500V i (a :: d) g w x c t o⟩ : L500C))
        = some ⟨some 14, some a, L500V i d g w x c t o⟩ := by
      simp [flip, TM2.step, TM2.stepAux, L500prog, L500pop, L500go]
    rw [e, ih]

def L500dg (ds : List Bool) : List Bool := ds.flatMap (fun d => [true, d])

theorem L500read (g w c t o : List Bool) : ∀ (ds R d x : List Bool),
    L500B (ds.length + 1) 1 (L500V (L500dg ds ++ false :: true :: R) d g w x c t o) 2
      (L500V R ((L500dg ds ++ [false, true]).reverse ++ d) g w (ds.reverse ++ x) c t o) := by
  intro ds
  induction ds with
  | nil =>
    intro R d x
    apply L500B_step; intro v
    simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
  | cons a ds ih =>
    intro R d x
    have h1 : L500B 1 1 (L500V (L500dg (a :: ds) ++ false :: true :: R) d g w x c t o) 1
        (L500V (L500dg ds ++ false :: true :: R) (a :: true :: d) g w (a :: x) c t o) := by
      apply L500B_step; intro v
      cases a <;> simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
    have := L500B_trans h1 (ih R (a :: true :: d) (a :: x))
    simpa [L500dg, Nat.add_comm] using this

def L500inc : List Bool → List Bool
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: L500inc r

theorem L500incM (i d g w x o : List Bool) : ∀ l t : List Bool, ∃ c' t' : List Bool,
    t'.reverse ++ c' = t.reverse ++ L500inc l ∧ t'.length ≤ t.length + l.length ∧
    L500B (l.length + 1) 8 (L500V i d g w x l t o) 9 (L500V i d g w x c' t' o) := by
  intro l
  induction l with
  | nil =>
    intro t
    refine ⟨[true], t, by simp [L500inc], by simp, ?_⟩
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500pc, L500go, L500br]
  | cons a l ih =>
    intro t
    cases a with
    | false =>
      refine ⟨true :: l, t, by simp [L500inc], by simp, ?_⟩
      refine L500B_mono (b := 1) ?_ (by simp)
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500pc, L500go, L500br]
    | true =>
      obtain ⟨c', t', e, hl, h⟩ := ih (false :: t)
      refine ⟨c', t', by simp [e, L500inc], by simp at hl ⊢; omega, ?_⟩
      have h1 : L500B 1 8 (L500V i d g w x (true :: l) t o) 8 (L500V i d g w x l (false :: t) o) := by
        apply L500B_step; intro v
        simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500pc, L500go, L500br]
      have := L500B_trans h1 h
      simpa [Nat.add_comm] using this

theorem L500inc_bits (n : ℕ) : L500inc n.bits = (n + 1).bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [L500inc]
      · rw [Nat.bit0_bits m (by omega), Nat.bit1_bits m]
        simp [L500inc]
    · rw [Nat.bit1_bits m, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.bit0_bits (m + 1) (by omega)]
      simp [L500inc, ih m (by omega)]

theorem L500bits_len (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  exact Nat.lt_two_pow_self

def L500ofB : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (L500ofB l)

theorem L500ofB_bits (n : ℕ) : L500ofB n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [L500ofB]
  | bit b n h ih => rw [Nat.bits_append_bit _ _ h]; simp [L500ofB, ih]

theorem L500bits_inj {m n : ℕ} (h : m.bits = n.bits) : m = n := by
  rw [← L500ofB_bits m, ← L500ofB_bits n, h]

theorem L500incF (i d g w x o : List Bool) (n : ℕ) :
    L500B (2 * n.bits.length + 2) 8 (L500V i d g w x n.bits [] o) 4
      (L500V i d g w x (n + 1).bits [] o) := by
  obtain ⟨c', t', e, hl, h⟩ := L500incM i d g w x o n.bits []
  have h2 := L500mvTC i d g w x c' t' o
  have := L500B_trans h h2
  simp at e hl
  rw [e, L500inc_bits] at this
  exact L500B_mono this (by omega)

theorem L500mism (i w x c t o : List Bool) : ∀ (ds d R : List Bool),
    L500B (ds.length + 1) 6 (L500V i d (L500dg ds ++ false :: true :: R) w x c t o) 7
      (L500V i ((L500dg ds ++ [false, true]).reverse ++ d) R w x c t o) := by
  intro ds
  induction ds with
  | nil =>
    intro d R
    apply L500B_step; intro v
    simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
  | cons a ds ih =>
    intro d R
    have h1 : L500B 1 6 (L500V i d (L500dg (a :: ds) ++ false :: true :: R) w x c t o) 6
        (L500V i (a :: true :: d) (L500dg ds ++ false :: true :: R) w x c t o) := by
      apply L500B_step; intro v
      cases a <;> simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
    have := L500B_trans h1 (ih (a :: true :: d) R)
    simpa [L500dg, Nat.add_comm] using this

theorem L500cmpY (i c t o : List Bool) : ∀ (ds d R x : List Bool),
    L500B (ds.length + 1) 5 (L500V i d (L500dg ds ++ false :: true :: R) ds x c t o) 10
      (L500V i ((L500dg ds ++ [false, true]).reverse ++ d) R [] (ds.reverse ++ x) c t o) := by
  intro ds
  induction ds with
  | nil =>
    intro d R x
    apply L500B_step; intro v
    simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
  | cons a ds ih =>
    intro d R x
    have h1 : L500B 1 5 (L500V i d (L500dg (a :: ds) ++ false :: true :: R) (a :: ds) x c t o) 5
        (L500V i (a :: true :: d) (L500dg ds ++ false :: true :: R) ds (a :: x) c t o) := by
      apply L500B_step; intro v
      cases a <;> simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
    have := L500B_trans h1 (ih (a :: true :: d) R (a :: x))
    simpa [L500dg, Nat.add_comm] using this

theorem L500cmpN (i c t o : List Bool) : ∀ (ds w d R x : List Bool), ds ≠ w →
    ∃ w' x' : List Bool, x'.reverse ++ w' = x.reverse ++ w ∧ x'.length ≤ x.length + w.length ∧
    L500B (ds.length + 1) 5 (L500V i d (L500dg ds ++ false :: true :: R) w x c t o) 7
      (L500V i ((L500dg ds ++ [false, true]).reverse ++ d) R w' x' c t o) := by
  intro ds
  induction ds with
  | nil =>
    intro w d R x hne
    obtain ⟨b, w, rfl⟩ := List.exists_cons_of_ne_nil (Ne.symm hne)
    refine ⟨b :: w, x, rfl, by simp, ?_⟩
    apply L500B_step; intro v
    simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
  | cons a ds ih =>
    intro w d R x hne
    rcases w with _ | ⟨b, w⟩
    · refine ⟨[], x, rfl, by simp, ?_⟩
      have h1 : L500B 1 5 (L500V i d (L500dg (a :: ds) ++ false :: true :: R) [] x c t o) 6
          (L500V i (a :: true :: d) (L500dg ds ++ false :: true :: R) [] x c t o) := by
        apply L500B_step; intro v
        cases a <;> simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
      have := L500B_trans h1 (L500mism i [] x c t o ds (a :: true :: d) R)
      simpa [L500dg, Nat.add_comm] using this
    · by_cases hab : a = b
      · subst hab
        have hne' : ds ≠ w := fun h => hne (by rw [h])
        obtain ⟨w', x', e, hl, h⟩ := ih w (a :: true :: d) R (a :: x) hne'
        refine ⟨w', x', by simp [e], by simp at hl ⊢; omega, ?_⟩
        have h1 : L500B 1 5 (L500V i d (L500dg (a :: ds) ++ false :: true :: R) (a :: w) x c t o) 5
            (L500V i (a :: true :: d) (L500dg ds ++ false :: true :: R) w (a :: x) c t o) := by
          apply L500B_step; intro v
          cases a <;> simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
        have := L500B_trans h1 h
        simpa [L500dg, Nat.add_comm] using this
      · refine ⟨w, b :: x, by simp, by simp, ?_⟩
        have h1 : L500B 1 5 (L500V i d (L500dg (a :: ds) ++ false :: true :: R) (b :: w) x c t o) 6
            (L500V i (a :: true :: d) (L500dg ds ++ false :: true :: R) w (b :: x) c t o) := by
          apply L500B_step; intro v
          cases a <;> cases b <;> simp_all [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
        have := L500B_trans h1 (L500mism i w (b :: x) c t o ds (a :: true :: d) R)
        simpa [L500dg, Nat.add_comm] using this

def L500e : Option Literal → List Bool
  | some l => encodeLiteral l
  | none => [false, false]

def L500p (u : ℕ) : Option Literal → Bool := fun o => o.any (fun l' => l'.1 == u)

theorem L500B_congr {b : ℕ} {l l' : Fin 16} {S₁ S₁' S₂ S₂' : Fin 8 → List Bool}
    (h₁ : S₁ = S₁') (h₂ : S₂ = S₂') (h : L500B b l S₁ l' S₂) : L500B b l S₁' l' S₂' := by
  subst h₁; subst h₂; exact h

theorem L500scan (i o : List Bool) (u M : ℕ) (hu : u.bits.length ≤ M) :
    ∀ (pre : List (Option Literal)) (c : ℕ) (d R : List Bool), pre.any (L500p u) = true →
    c + pre.length ≤ M → (∀ z ∈ pre, (L500e z).length ≤ M) →
    L500B (pre.length * (4 * M + 6)) 4 (L500V i d (pre.flatMap L500e ++ R) u.bits [] c.bits [] o) 10
      (L500V i (((pre.take (pre.findIdx (L500p u) + 1)).flatMap L500e).reverse ++ d)
        ((pre.drop (pre.findIdx (L500p u) + 1)).flatMap L500e ++ R) [] u.bits.reverse
        (c + pre.findIdx (L500p u)).bits [] o) := by
  intro pre
  induction pre with
  | nil => intro c d R h; simp at h
  | cons z rest ih =>
    intro c d R hany hc hlen
    have hcb := L500bits_len c
    have hc' : c ≤ M := by simp at hc; omega
    rcases z with _ | ⟨u', b'⟩
    · have hany' : rest.any (L500p u) = true := by simpa [L500p] using hany
      have hfi : (none :: rest).findIdx (L500p u) = rest.findIdx (L500p u) + 1 := by
        simp [List.findIdx_cons, L500p]
      have h1 : L500B 1 4 (L500V i d (false :: false :: (rest.flatMap L500e ++ R)) u.bits [] c.bits [] o) 8
          (L500V i (false :: false :: d) (rest.flatMap L500e ++ R) u.bits [] c.bits [] o) := by
        apply L500B_step; intro v
        simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
      have h2 := L500incF i (false :: false :: d) (rest.flatMap L500e ++ R) u.bits [] o c
      have h3 := ih (c + 1) (false :: false :: d) R hany' (by simp at hc; omega)
        (fun z hz => hlen z (by simp [hz]))
      have := L500B_trans h1 (L500B_trans h2 h3)
      rw [hfi]
      refine L500B_mono (L500B_congr ?_ ?_ this) ?_
      · simp [L500e]
      · congr 1
        · simp [L500e]
        · simp [Nat.add_assoc, Nat.add_comm 1]
      · simp only [List.length_cons]
        nlinarith
    · by_cases hu' : u' = u
      · subst hu'
        have hfi : (some (u', b') :: rest).findIdx (L500p u') = 0 := by
          simp [List.findIdx_cons, L500p]
        have h1 : L500B 1 4 (L500V i d (true :: b' :: (L500dg u'.bits ++ false :: true ::
            (rest.flatMap L500e ++ R))) u'.bits [] c.bits [] o) 5
            (L500V i (b' :: true :: d) (L500dg u'.bits ++ false :: true ::
            (rest.flatMap L500e ++ R)) u'.bits [] c.bits [] o) := by
          apply L500B_step; intro v
          cases b' <;> simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
        have h2 := L500cmpY i c.bits [] o u'.bits (b' :: true :: d) (rest.flatMap L500e ++ R) []
        have := L500B_trans h1 h2
        rw [hfi]
        have hl1 := hlen (some (u', b')) (by simp)
        simp [L500e, encodeLiteral] at hl1
        refine L500B_mono (L500B_congr ?_ ?_ this) ?_
        · simp [L500e, encodeLiteral, L500dg]
        · congr 1 <;> simp [L500e, encodeLiteral, L500dg]
        · simp only [List.length_cons]
          nlinarith
      · have hany' : rest.any (L500p u) = true := by
          simpa [L500p, hu'] using hany
        have hfi : (some (u', b') :: rest).findIdx (L500p u) = rest.findIdx (L500p u) + 1 := by
          simp [List.findIdx_cons, L500p, hu']
        have h1 : L500B 1 4 (L500V i d (true :: b' :: (L500dg u'.bits ++ false :: true ::
            (rest.flatMap L500e ++ R))) u.bits [] c.bits [] o) 5
            (L500V i (b' :: true :: d) (L500dg u'.bits ++ false :: true ::
            (rest.flatMap L500e ++ R)) u.bits [] c.bits [] o) := by
          apply L500B_step; intro v
          cases b' <;> simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500go, L500br]
        have hne : u'.bits ≠ u.bits := fun h => hu' (L500bits_inj h)
        obtain ⟨w', x', e, hl, h2⟩ := L500cmpN i c.bits [] o u'.bits u.bits (b' :: true :: d)
          (rest.flatMap L500e ++ R) [] hne
        simp at e hl
        have h3 := L500mvRS i ((L500dg u'.bits ++ [false, true]).reverse ++ b' :: true :: d)
          (rest.flatMap L500e ++ R) w' x' c.bits [] o
        rw [e] at h3
        have h4 := L500incF i ((L500dg u'.bits ++ [false, true]).reverse ++ b' :: true :: d)
          (rest.flatMap L500e ++ R) u.bits [] o c
        have h5 := ih (c + 1) ((L500dg u'.bits ++ [false, true]).reverse ++ b' :: true :: d) R hany'
          (by simp at hc; omega) (fun z hz => hlen z (by simp [hz]))
        have := L500B_trans h1 (L500B_trans h2 (L500B_trans h3 (L500B_trans h4 h5)))
        rw [hfi]
        have hl1 := hlen (some (u', b')) (by simp)
        simp [L500e, encodeLiteral] at hl1
        refine L500B_mono (L500B_congr ?_ ?_ this) ?_
        · simp [L500e, encodeLiteral, L500dg]
        · congr 1
          · simp [L500e, encodeLiteral, L500dg]
          · simp [Nat.add_assoc, Nat.add_comm 1]
        · simp only [List.length_cons]
          nlinarith

theorem L500emit (i d g w x t : List Bool) : ∀ (l O : List Bool),
    L500B (l.length + 1) 11 (L500V i d g w x l t O) 12
      (L500V i d g w x [] t ((L500dg l ++ [false, true]).reverse ++ O)) := by
  intro l
  induction l with
  | nil =>
    intro O
    apply L500B_step; intro v
    simp [L500dg, TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500pc, L500go]
  | cons a l ih =>
    intro O
    have h1 : L500B 1 11 (L500V i d g w x (a :: l) t O) 11 (L500V i d g w x l t (a :: true :: O)) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500pc, L500go]
    have := L500B_trans h1 (ih (a :: true :: O))
    simpa [L500dg, Nat.add_comm] using this

def L500it (φ : CNF) : List (Option Literal) := φ.flatMap (fun c' => c'.map some ++ [none])

def L500g (φ : CNF) (l : Literal) : Literal := ((L500it φ).findIdx (L500p l.1), l.2)

theorem L500len_le (l : List (Option Literal)) : l.length ≤ (l.flatMap L500e).length := by
  induction l with
  | nil => simp
  | cons z l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (L500e z).length := by rcases z with _ | ⟨u, b⟩ <;> simp [L500e, encodeLiteral]
    omega

theorem L500mem_len (f : Option Literal → List Bool) : ∀ (l : List (Option Literal)) (y : Option Literal),
    y ∈ l → (f y).length ≤ (l.flatMap f).length := by
  intro l
  induction l with
  | nil => intro y hy; simp at hy
  | cons a l ih =>
    intro y hy
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := ih y hy
      omega

theorem L500item (φ : CNF) (n : ℕ) (hn : ((L500it φ).flatMap L500e).length ≤ n)
    (pre rest : List (Option Literal)) (z : Option Literal) (h : pre ++ z :: rest = L500it φ) :
    L500B (8 * (n + 1) * (n + 1)) 0
      (L500V ((z :: rest).flatMap L500e) (pre.flatMap L500e).reverse [] [] [] [] []
        (pre.flatMap (fun y => L500e (y.map (L500g φ)))).reverse) 0
      (L500V (rest.flatMap L500e) ((pre ++ [z]).flatMap L500e).reverse [] [] [] [] []
        ((pre ++ [z]).flatMap (fun y => L500e (y.map (L500g φ)))).reverse) := by
  rcases z with _ | ⟨u, b⟩
  · have h1 : L500B 1 0 (L500V (false :: false :: rest.flatMap L500e) (pre.flatMap L500e).reverse
        [] [] [] [] [] (pre.flatMap (fun y => L500e (y.map (L500g φ)))).reverse) 0
        (L500V (rest.flatMap L500e) (false :: false :: (pre.flatMap L500e).reverse) [] [] [] [] []
        (false :: false :: (pre.flatMap (fun y => L500e (y.map (L500g φ)))).reverse)) := by
      apply L500B_step; intro v
      simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500pc, L500go, L500br]
    refine L500B_mono (L500B_congr ?_ ?_ h1) ?_
    · simp [L500e]
    · simp [L500e]
    · nlinarith
  · set Drev := (pre.flatMap L500e).reverse with hDrev
    set Orev := (pre.flatMap (fun y => L500e (y.map (L500g φ)))).reverse with hOrev
    set R := rest.flatMap L500e with hR
    set pre' := pre ++ [some (u, b)] with hpre'
    have hits : pre' ++ rest = L500it φ := by simp [hpre', h]
    have hlenpre : (pre'.flatMap L500e).length ≤ n := by
      rw [← hits, List.flatMap_append, List.length_append] at hn; omega
    have hpl := L500len_le pre'
    have hub : u.bits.length ≤ n := by
      have : (pre'.flatMap L500e).length = (pre.flatMap L500e).length + 4 + 2 * u.bits.length := by
        simp [hpre', L500e, encodeLiteral]; ring
      omega
    have h1 : L500B 1 0 (L500V (true :: b :: (L500dg u.bits ++ false :: true :: R)) Drev
        [] [] [] [] [] Orev) 1
        (L500V (L500dg u.bits ++ false :: true :: R) (b :: true :: Drev) [] [] [] [] []
        (b :: true :: Orev)) := by
      apply L500B_step; intro v
      cases b <;> simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500psh, L500pc, L500go, L500br]
    have h2 := L500read [] [] [] [] (b :: true :: Orev) u.bits R (b :: true :: Drev) []
    have h3 := L500mvXW R ((L500dg u.bits ++ [false, true]).reverse ++ b :: true :: Drev) []
      [] (u.bits.reverse ++ []) [] [] (b :: true :: Orev)
    have h4 := L500mvDG R ((L500dg u.bits ++ [false, true]).reverse ++ b :: true :: Drev) []
      ((u.bits.reverse ++ []).reverse ++ []) [] [] [] (b :: true :: Orev)
    have hany : pre'.any (L500p u) = true := by simp [hpre', L500p]
    have h5 := L500scan R (b :: true :: Orev) u n hub pre' 0 [] [] hany (by omega)
      (fun y hy => by
        have := L500mem_len L500e pre' y hy
        omega)
    have h4' : L500B (((L500dg u.bits ++ [false, true]).reverse ++ b :: true :: Drev).length + 1) 3
        (L500V R ((L500dg u.bits ++ [false, true]).reverse ++ b :: true :: Drev) []
        ((u.bits.reverse ++ []).reverse ++ []) [] [] [] (b :: true :: Orev)) 4
        (L500V R [] (pre'.flatMap L500e ++ []) u.bits [] (Nat.bits 0) [] (b :: true :: Orev)) := by
      refine L500B_congr rfl ?_ h4
      simp [hDrev, hpre', L500e, encodeLiteral, L500dg]
    set j := pre'.findIdx (L500p u) with hj
    have h6 := L500mvGD R (((pre'.take (j + 1)).flatMap L500e).reverse ++ [])
      ((pre'.drop (j + 1)).flatMap L500e ++ []) [] u.bits.reverse (0 + j).bits [] (b :: true :: Orev)
    have h7 := L500emit R (((pre'.drop (j + 1)).flatMap L500e ++ []).reverse ++
      (((pre'.take (j + 1)).flatMap L500e).reverse ++ [])) [] [] u.bits.reverse []
      (0 + j).bits (b :: true :: Orev)
    have h8 := L500clrX R (((pre'.drop (j + 1)).flatMap L500e ++ []).reverse ++
      (((pre'.take (j + 1)).flatMap L500e).reverse ++ [])) [] [] u.bits.reverse [] []
      ((L500dg (0 + j).bits ++ [false, true]).reverse ++ b :: true :: Orev)
    have := L500B_trans h1 (L500B_trans h2 (L500B_trans h3 (L500B_trans h4'
      (L500B_trans h5 (L500B_trans h6 (L500B_trans h7 h8))))))
    have hjlt : j < pre'.length := by
      rw [hj]; exact List.findIdx_lt_length_of_exists ⟨some (u, b), by simp [hpre'], by simp [L500p]⟩
    have hJ : (L500it φ).findIdx (L500p u) = j := by
      rw [← hits, List.findIdx_append, ite_eq_left (by rw [← hj]; exact hjlt)]
    have hsplit : (pre'.take (j + 1)).flatMap L500e ++ (pre'.drop (j + 1)).flatMap L500e =
        pre'.flatMap L500e := by
      rw [← List.flatMap_append, List.take_append_drop]
    have hsplitL := congrArg List.length hsplit
    rw [List.length_append] at hsplitL
    have hjb := L500bits_len j
    refine L500B_mono (L500B_congr ?_ ?_ this) ?_
    · simp [hR, L500e, encodeLiteral, L500dg]
    · congr 1
      · rw [← hsplit]; simp
      · simp [hOrev, hpre', L500e, encodeLiteral, L500dg, L500g, hJ]
    · have e1 : ((L500dg u.bits ++ [false, true]).reverse ++ b :: true :: Drev).length ≤ n := by
        have : ((L500dg u.bits ++ [false, true]).reverse ++ b :: true :: Drev).length =
            (pre'.flatMap L500e).length := by
          simp [hDrev, hpre', L500e, encodeLiteral, L500dg]; ring
        omega
      have e2 : ((pre'.drop (j + 1)).flatMap L500e ++ []).length ≤ n := by
        rw [List.append_nil]; omega
      have e3 : (0 + j).bits.length ≤ n := by rw [Nat.zero_add]; omega
      have e4 : (u.bits.reverse ++ []).length ≤ n := by simp; omega
      have e5 : u.bits.reverse.length ≤ n := by simp; omega
      have e6 : pre'.length ≤ n := by omega
      have e7 : pre'.length * (4 * n + 6) ≤ n * (4 * n + 6) := Nat.mul_le_mul_right _ e6
      nlinarith

theorem L500outer (φ : CNF) (n : ℕ) (hn : ((L500it φ).flatMap L500e).length ≤ n) :
    ∀ (rest pre : List (Option Literal)), pre ++ rest = L500it φ →
    L500B (rest.length * (8 * (n + 1) * (n + 1)) + 1) 0
      (L500V (rest.flatMap L500e) (pre.flatMap L500e).reverse [] [] [] [] []
        (pre.flatMap (fun y => L500e (y.map (L500g φ)))).reverse) 13
      (L500V [] ((L500it φ).flatMap L500e).reverse [] [] [] [] []
        ((L500it φ).flatMap (fun y => L500e (y.map (L500g φ)))).reverse) := by
  intro rest
  induction rest with
  | nil =>
    intro pre h
    simp at h
    subst h
    apply L500B_mono (b := 1) _ (by simp)
    apply L500B_step; intro v
    simp [TM2.step, TM2.stepAux, L500prog, L500pop, L500go]
  | cons z rest ih =>
    intro pre h
    have h1 := L500item φ n hn pre rest z h
    have h2 := ih (pre ++ [z]) (by simp [h])
    have := L500B_trans h1 h2
    refine L500B_mono this ?_
    simp only [List.length_cons]
    nlinarith

theorem L500enc (g : Literal → Literal) : ∀ ψ : CNF,
    encodeCNF (ψ.map (fun c => c.map g)) = (L500it ψ).flatMap (fun z => L500e (z.map g)) := by
  intro ψ
  induction ψ with
  | nil => simp [encodeCNF, L500it]
  | cons c ψ ih =>
    have hc : encodeClause (c.map g) =
        (c.map some ++ [none]).flatMap (fun z : Option Literal => L500e (z.map g)) := by
      simp [encodeClause, L500e, List.flatMap_map]
    have e1 : encodeCNF ((c :: ψ).map (fun c => c.map g)) =
        encodeClause (c.map g) ++ encodeCNF (ψ.map (fun c => c.map g)) := by
      simp [encodeCNF]
    have e2 : L500it (c :: ψ) = (c.map some ++ [none]) ++ L500it ψ := by simp [L500it]
    rw [e1, e2, List.flatMap_append, ← hc, ← ih]

theorem L500enc0 (ψ : CNF) : encodeCNF ψ = (L500it ψ).flatMap L500e := by
  have := L500enc id ψ
  simpa using this

theorem L500sum_len (f : Option Literal → List Bool) (K : ℕ) : ∀ l : List (Option Literal),
    (∀ z ∈ l, (f z).length ≤ K) → (l.flatMap f).length ≤ l.length * K := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun z hz => h z (by simp [hz]))
    nlinarith

def L500tm : FinTM2 where
  K := Fin 8
  k₀ := 0
  k₁ := 0
  Γ := L500G
  Λ := Fin 16
  main := 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := L500prog

theorem L500init (x : List Bool) :
    initList L500tm x = (⟨some 0, none, L500V x [] [] [] [] [] [] []⟩ : L500C) := by
  unfold initList
  congr 1
  funext k
  change Fin 8 at k
  fin_cases k <;> simp [L500tm, L500V] <;> rfl

theorem L500halt (y : List Bool) :
    haltList L500tm y = (⟨none, none, L500V y [] [] [] [] [] [] []⟩ : L500C) := by
  unfold haltList
  congr 1
  funext k
  change Fin 8 at k
  fin_cases k <;> simp [L500tm, L500V] <;> rfl

theorem L500runP (φ : CNF) : ∃ t ≤ 16 * ((encodeCNF φ).length + 1) ^ 3,
    (flip bind (TM2.step L500prog))^[t]
      (some (⟨some 0, none, L500V (encodeCNF φ) [] [] [] [] [] [] []⟩ : L500C)) =
      some ⟨none, none, L500V (encodeCNF (φ.map (fun c => c.map (L500g φ)))) [] [] [] [] [] [] []⟩ := by
  have hx := L500enc0 φ
  have hy := L500enc (L500g φ) φ
  set n := (encodeCNF φ).length with hn
  have hn' : ((L500it φ).flatMap L500e).length ≤ n := by rw [hn, hx]
  have h1 := L500outer φ n hn' (L500it φ) [] (by simp)
  have h2 := L500mvOI [] ((L500it φ).flatMap L500e).reverse [] [] [] [] []
    ((L500it φ).flatMap (fun y => L500e (y.map (L500g φ)))).reverse
  obtain ⟨t1, ht1, r1⟩ := L500B_trans h1 h2
  obtain ⟨v', e1⟩ := r1 none
  have e2 := L500drain (((L500it φ).flatMap (fun y => L500e (y.map (L500g φ)))).reverse.reverse ++ [])
    [] [] [] [] [] [] ((L500it φ).flatMap L500e).reverse v'
  have hits := L500len_le (L500it φ)
  have hylen : ((L500it φ).flatMap (fun y => L500e (y.map (L500g φ)))).length ≤
      (L500it φ).length * (2 * n + 4) := by
    apply L500sum_len
    intro z hz
    rcases z with _ | ⟨u, b⟩
    · simp [L500e]
    · have hJ := L500bits_len ((L500it φ).findIdx (L500p u))
      have hJ2 : (L500it φ).findIdx (L500p u) ≤ (L500it φ).length := List.findIdx_le_length
      simp [L500e, encodeLiteral, L500g]
      omega
  refine ⟨(((L500it φ).flatMap L500e).reverse.length + 1) + t1, ?_, ?_⟩
  · simp only [List.length_reverse, List.length_append, List.length_nil] at ht1 ⊢
    have ea : (L500it φ).length * (8 * (n + 1) * (n + 1)) ≤ n * (8 * (n + 1) * (n + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    have eb : (L500it φ).length * (2 * n + 4) ≤ n * (2 * n + 4) :=
      Nat.mul_le_mul_right _ (by omega)
    have hlen : ((L500it φ).flatMap L500e).length = n := by rw [hn, hx]
    rw [hlen]
    nlinarith [ea, eb, hylen, ht1]
  · rw [Function.iterate_add_apply]
    simp only [List.flatMap_nil, List.reverse_nil] at e1
    rw [hx, e1, e2, hy]
    simp

noncomputable def L500key (φ : CNF) (l₁ l₂ : List Bool) (h₁ : l₁ = encodeCNF φ)
    (h₂ : l₂ = encodeCNF (φ.map (fun c => c.map (L500g φ)))) :
    TM2OutputsInTime L500tm l₁ (some l₂)
      ((Polynomial.C 16 * (Polynomial.X + 1) ^ 3 : Polynomial ℕ).eval (encodeCNF φ).length) := by
  subst h₁
  subst h₂
  have h := L500runP φ
  have e3 : (Polynomial.C 16 * (Polynomial.X + 1) ^ 3 : Polynomial ℕ).eval (encodeCNF φ).length =
      16 * ((encodeCNF φ).length + 1) ^ 3 := by
    simp
  rw [e3]
  refine ⟨⟨Classical.choose h, ?_⟩, (Classical.choose_spec h).1⟩
  rw [L500init]
  show _ = some (haltList L500tm _)
  rw [L500halt]
  exact (Classical.choose_spec h).2

end PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_500 : PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF PEqualNP.Search.encodeCNF (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) := by
  refine ⟨{
    tm := PEqualNP.Outside.L500tm
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C 16 * (Polynomial.X + 1) ^ 3
    outputsFun := fun φ => PEqualNP.Outside.L500key φ _ _ (List.map_id _) (List.map_id _) }⟩
