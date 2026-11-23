import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1400

abbrev B5 := Bool × Bool × Bool × Bool × Bool
abbrev B6 := Bool × Bool × Bool × Bool × Bool × Bool

def all5 : B5 := (true, true, true, true, true)
def all6 : B6 := (true, true, true, true, true, true)

def le5 (a b : B5) : Bool :=
  (!a.1 || b.1) && (!a.2.1 || b.2.1) && (!a.2.2.1 || b.2.2.1) &&
  (!a.2.2.2.1 || b.2.2.2.1) && (!a.2.2.2.2 || b.2.2.2.2)

def le6 (a b : B6) : Bool :=
  (!a.1 || b.1) && (!a.2.1 || b.2.1) && (!a.2.2.1 || b.2.2.1) &&
  (!a.2.2.2.1 || b.2.2.2.1) && (!a.2.2.2.2.1 || b.2.2.2.2.1) &&
  (!a.2.2.2.2.2 || b.2.2.2.2.2)

def and5 (a b : B5) : B5 :=
  (a.1 && b.1, a.2.1 && b.2.1, a.2.2.1 && b.2.2.1, a.2.2.2.1 && b.2.2.2.1, a.2.2.2.2 && b.2.2.2.2)

def or5 (a b : B5) : B5 :=
  (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2.1 || b.2.2.2.1, a.2.2.2.2 || b.2.2.2.2)

def and6 (a b : B6) : B6 :=
  (a.1 && b.1, a.2.1 && b.2.1, a.2.2.1 && b.2.2.1, a.2.2.2.1 && b.2.2.2.1,
   a.2.2.2.2.1 && b.2.2.2.2.1, a.2.2.2.2.2 && b.2.2.2.2.2)

def or6 (a b : B6) : B6 :=
  (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2.1 || b.2.2.2.1,
   a.2.2.2.2.1 || b.2.2.2.2.1, a.2.2.2.2.2 || b.2.2.2.2.2)

def x0 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => true | 1 => true | 2 => false | 3 => false | 4 => false | 5 => true | 6 => true | 7 => false | 8 => false | 9 => false | _ => false
def x1 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => false | 1 => true | 2 => true | 3 => false | 4 => false | 5 => false | 6 => true | 7 => true | 8 => false | 9 => false | _ => false
def x2 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => false | 1 => false | 2 => true | 3 => true | 4 => false | 5 => false | 6 => false | 7 => true | 8 => true | 9 => false | _ => false
def x3 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => false | 1 => false | 2 => false | 3 => true | 4 => true | 5 => false | 6 => false | 7 => false | 8 => true | 9 => true | _ => false
def x4 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => true | 1 => false | 2 => false | 3 => false | 4 => true | 5 => true | 6 => false | 7 => false | 8 => false | 9 => true | _ => false

def y0 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => true | 1 => false | 2 => true | 3 => false | 4 => true | 5 => false | 6 => true | 7 => true | 8 => true | 9 => true | _ => false
def y1 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => false | 1 => true | 2 => true | 3 => true | 4 => true | 5 => true | 6 => false | 7 => true | 8 => false | 9 => true | _ => false
def y2 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => true | 1 => true | 2 => true | 3 => true | 4 => true | 5 => true | 6 => false | 7 => false | 8 => true | 9 => false | _ => false
def y3 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => false | 1 => true | 2 => true | 3 => true | 4 => true | 5 => true | 6 => true | 7 => false | 8 => false | 9 => true | _ => false
def y4 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => true | 1 => false | 2 => true | 3 => true | 4 => false | 5 => true | 6 => true | 7 => true | 8 => false | 9 => true | _ => false
def y5 : Fin 10 → Bool := fun i : Fin 10 => match i.val with | 0 => true | 1 => true | 2 => false | 3 => true | 4 => false | 5 => false | 6 => true | 7 => true | 8 => true | 9 => true | _ => false

def mxOf (f : (Fin 10 → Bool) → Bool) : B5 :=
  (f x0, f x1, f x2, f x3, f x4)

def myOf (f : (Fin 10 → Bool) → Bool) : B6 :=
  (!f y0, !f y1, !f y2, !f y3, !f y4, !f y5)

def inL (L : List (B5 × B6)) (x : B5) (y : B6) : Bool :=
  L.any (fun p => le5 x p.1 && le6 y p.2)

def inL5 (L : List B5) (x : B5) : Bool :=
  L.any (fun p => le5 x p)

def inL6 (L : List B6) (y : B6) : Bool :=
  L.any (fun p => le6 y p)

def L0 : List (B5 × B6) := [
  ((true, false, false, false, true), (false, true, false, true, false, false)), ((true, true, false, false, false), (true, false, false, false, true, false)),
  ((false, true, true, false, false), (false, false, false, false, false, true)), ((false, false, true, true, false), (true, false, false, false, false, false)),
  ((false, false, false, true, true), (false, false, false, false, true, true)), ((true, false, false, false, true), (true, false, false, false, false, true)),
  ((true, true, false, false, false), (false, true, true, false, false, false)), ((false, true, true, false, false), (false, false, true, true, false, false)),
  ((false, false, true, true, false), (false, true, false, true, true, false)), ((false, false, false, true, true), (false, false, true, false, false, false))
]

def L1 : List (B5 × B6) := [
  ((false, false, false, false, false), (true, false, true, true, false, true)), ((false, false, false, false, false), (false, true, true, false, true, true)),
  ((false, false, false, false, false), (true, true, false, true, true, true)), ((false, false, false, false, false), (false, false, true, true, true, true)),
  ((true, false, false, false, false), (false, true, true, true, false, false)), ((true, false, false, false, false), (true, true, false, true, true, false)),
  ((true, false, false, false, false), (true, true, true, false, false, true)), ((true, false, false, false, false), (true, false, false, false, true, true)),
  ((false, true, false, false, false), (false, true, true, true, false, false)), ((false, true, false, false, false), (true, false, true, true, true, false)),
  ((false, true, false, false, false), (false, true, true, false, false, true)), ((false, true, false, false, false), (true, false, false, false, true, true)),
  ((true, true, false, false, false), (true, true, true, false, true, false)), ((false, false, true, false, false), (true, false, true, true, false, false)),
  ((false, false, true, false, false), (false, true, true, true, true, false)), ((false, false, true, false, false), (true, false, false, false, false, true)),
  ((false, false, true, false, false), (false, true, false, true, true, true)), ((false, true, true, false, false), (false, false, true, true, false, true)),
  ((true, true, true, false, false), (false, false, true, false, false, false)), ((false, false, false, true, false), (true, false, true, false, false, false)),
  ((false, false, false, true, false), (false, true, true, true, true, false)), ((false, false, false, true, false), (true, false, false, false, true, true)),
  ((false, false, false, true, false), (false, true, false, true, true, true)), ((false, false, true, true, false), (true, true, false, true, true, false)),
  ((false, true, true, true, false), (false, false, false, true, false, false)), ((true, true, true, true, false), (true, false, false, false, false, false)),
  ((true, true, true, true, false), (false, true, false, false, false, false)), ((true, true, true, true, false), (false, false, false, false, true, false)),
  ((false, false, false, false, true), (false, true, true, true, false, false)), ((false, false, false, false, true), (true, false, true, false, false, true)),
  ((false, false, false, false, true), (true, false, false, false, true, true)), ((false, false, false, false, true), (false, true, false, true, true, true)),
  ((true, false, false, false, true), (true, true, false, true, false, true)), ((true, true, false, false, true), (true, false, false, false, false, false)),
  ((true, true, false, false, true), (false, true, false, false, false, false)), ((true, true, true, false, true), (false, false, false, true, false, false)),
  ((true, true, true, false, true), (false, false, false, false, false, true)), ((false, false, false, true, true), (false, false, true, false, true, true)),
  ((true, false, false, true, true), (false, false, false, false, false, true)), ((true, true, false, true, true), (false, false, true, false, false, false)),
  ((true, true, false, true, true), (false, false, false, false, true, false)), ((false, false, true, true, true), (false, false, false, false, true, false)),
  ((true, false, true, true, true), (true, false, false, false, false, false)), ((true, false, true, true, true), (false, true, false, true, false, false)),
  ((false, true, true, true, true), (false, false, true, false, false, false)), ((false, true, true, true, true), (false, false, false, false, false, true))
]

def L2 : List (B5 × B6) := [
  ((true, false, false, false, false), (true, true, true, true, true, true)), ((false, true, false, false, false), (true, true, true, true, true, true)),
  ((true, true, false, false, false), (true, true, true, true, true, false)), ((true, true, false, false, false), (true, true, true, false, true, true)),
  ((false, false, true, false, false), (true, true, true, true, true, true)), ((true, false, true, false, false), (false, true, true, true, false, false)),
  ((false, true, true, false, false), (true, false, true, true, false, true)), ((false, true, true, false, false), (false, true, true, true, false, true)),
  ((false, true, true, false, false), (false, false, true, true, true, true)), ((true, true, true, false, false), (true, false, true, false, false, false)),
  ((true, true, true, false, false), (true, false, false, true, false, false)), ((true, true, true, false, false), (false, false, true, true, false, false)),
  ((true, true, true, false, false), (false, true, true, false, true, false)), ((true, true, true, false, false), (false, false, false, true, true, false)),
  ((true, true, true, false, false), (true, false, false, false, false, true)), ((true, true, true, false, false), (false, true, false, false, false, true)),
  ((true, true, true, false, false), (false, false, true, false, false, true)), ((true, true, true, false, false), (false, false, false, false, true, true)),
  ((false, false, false, true, false), (true, true, true, true, true, true)), ((true, false, false, true, false), (true, false, false, false, true, true)),
  ((false, true, false, true, false), (false, true, true, true, false, false)), ((false, true, false, true, false), (false, false, true, true, true, false)),
  ((false, true, false, true, false), (true, false, false, false, true, true)), ((true, true, false, true, false), (true, false, true, false, false, false)),
  ((true, true, false, true, false), (false, true, true, false, true, false)), ((false, false, true, true, false), (true, true, true, true, true, false)),
  ((false, false, true, true, false), (true, true, false, true, true, true)), ((true, false, true, true, false), (true, true, false, true, true, false)),
  ((false, true, true, true, false), (true, false, true, false, false, false)), ((false, true, true, true, false), (false, true, true, false, false, false)),
  ((false, true, true, true, false), (false, false, true, true, false, false)), ((false, true, true, true, false), (false, false, true, false, true, false)),
  ((false, true, true, true, false), (true, false, false, true, true, false)), ((false, true, true, true, false), (true, false, false, false, false, true)),
  ((false, true, true, true, false), (false, true, false, false, false, true)), ((false, true, true, true, false), (false, false, false, true, false, true)),
  ((false, true, true, true, false), (false, false, false, false, true, true)), ((true, true, true, true, false), (true, true, false, false, true, false)),
  ((false, false, false, false, true), (true, true, true, true, true, true)), ((true, false, false, false, true), (true, true, true, true, false, true)),
  ((true, false, false, false, true), (true, true, false, true, true, true)), ((false, true, false, false, true), (false, true, true, true, false, false)),
  ((false, true, false, false, true), (true, false, false, false, true, true)), ((true, true, false, false, true), (true, true, false, false, false, false)),
  ((true, true, false, false, true), (true, false, true, false, false, false)), ((true, true, false, false, true), (false, true, true, false, false, false)),
  ((true, true, false, false, true), (true, false, false, true, false, false)), ((true, true, false, false, true), (false, false, true, true, false, false)),
  ((true, true, false, false, true), (true, false, false, false, true, false)), ((true, true, false, false, true), (false, true, false, false, true, false)),
  ((true, true, false, false, true), (false, false, false, true, true, false)), ((true, true, false, false, true), (true, false, false, false, false, true)),
  ((true, true, false, false, true), (false, true, false, false, false, true)), ((true, true, false, false, true), (false, false, true, false, false, true)),
  ((true, true, false, false, true), (false, false, false, false, true, true)), ((false, false, true, false, true), (false, true, false, true, true, true)),
  ((true, false, true, false, true), (true, false, false, false, false, true)), ((true, false, true, false, true), (false, true, false, true, false, true)),
  ((false, true, true, false, true), (false, false, true, true, false, false)), ((true, true, true, false, true), (false, false, false, true, false, true)),
  ((false, false, false, true, true), (true, false, true, false, true, true)), ((false, false, false, true, true), (false, true, true, true, true, true)),
  ((true, false, false, true, true), (true, false, true, false, false, false)), ((true, false, false, true, true), (false, true, true, true, false, false)),
  ((true, false, false, true, true), (true, false, false, false, true, false)), ((true, false, false, true, true), (false, true, false, true, true, false)),
  ((true, false, false, true, true), (true, false, false, false, false, true)), ((true, false, false, true, true), (false, false, true, false, false, true)),
  ((true, false, false, true, true), (false, true, false, true, false, true)), ((true, false, false, true, true), (false, false, false, false, true, true)),
  ((false, true, false, true, true), (false, false, false, false, true, true)), ((true, true, false, true, true), (false, false, true, false, true, false)),
  ((false, false, true, true, true), (true, false, true, false, false, false)), ((false, false, true, true, true), (false, true, true, true, false, false)),
  ((false, false, true, true, true), (true, false, false, false, true, false)), ((false, false, true, true, true), (false, false, true, false, true, false)),
  ((false, false, true, true, true), (false, true, false, true, true, false)), ((false, false, true, true, true), (true, false, false, false, false, true)),
  ((false, false, true, true, true), (false, true, false, true, false, true)), ((false, false, true, true, true), (false, false, false, false, true, true)),
  ((true, false, true, true, true), (true, true, false, true, false, false)), ((false, true, true, true, true), (false, false, true, false, false, true)),
  ((true, true, true, true, true), (true, false, false, false, false, false)), ((true, true, true, true, true), (false, false, true, false, false, false)),
  ((true, true, true, true, true), (false, true, false, true, false, false)), ((true, true, true, true, true), (false, false, false, false, true, false)),
  ((true, true, true, true, true), (false, false, false, false, false, true))
]

def L3Y : List B5 := [
  (true, true, false, false, false), (true, false, true, false, false),
  (false, true, true, false, false), (true, false, false, true, false),
  (false, true, false, true, false), (false, false, true, true, false),
  (true, false, false, false, true), (false, true, false, false, true),
  (false, false, true, false, true), (false, false, false, true, true)
]

def L3X : List B6 := [
  (true, false, true, false, false, false), (true, true, false, true, false, false),
  (false, true, true, true, false, false), (true, true, false, false, true, false),
  (false, true, true, false, true, false), (true, false, false, true, true, false),
  (false, true, false, true, true, false), (true, false, false, false, false, true),
  (false, false, true, false, false, true), (false, true, false, true, false, true),
  (false, false, false, false, true, true)
]

def pairsAll {α : Type} (P : α → α → Bool) : List α → Bool
  | [] => true
  | a :: t => P a a && t.all (fun b => P a b) && pairsAll P t

lemma pairsAll_spec {α : Type} (P : α → α → Bool)
    (hsym : ∀ a b, P a b = P b a) :
    ∀ L : List α, pairsAll P L = true → ∀ a ∈ L, ∀ b ∈ L, P a b = true := by
  intro L
  induction L with
  | nil => intro _ a ha; cases ha
  | cons x t ih =>
    intro h a ha b hb
    simp only [pairsAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact h.1.1
      · exact h.1.2 b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rw [hsym]; exact h.1.2 a ha'
      · exact ih h.2 a ha' b hb'

lemma le1_trans (a b c : Bool) (h1 : (!a || b) = true) (h2 : (!b || c) = true) :
    (!a || c) = true := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma le5_trans (a b c : B5) (h1 : le5 a b = true) (h2 : le5 b c = true) :
    le5 a c = true := by
  rcases a with ⟨a1, a2, a3, a4, a5⟩
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  rcases c with ⟨c1, c2, c3, c4, c5⟩
  simp only [le5, Bool.and_eq_true] at h1 h2 ⊢
  exact ⟨⟨⟨⟨le1_trans _ _ _ h1.1.1.1.1 h2.1.1.1.1, le1_trans _ _ _ h1.1.1.1.2 h2.1.1.1.2⟩,
    le1_trans _ _ _ h1.1.1.2 h2.1.1.2⟩, le1_trans _ _ _ h1.1.2 h2.1.2⟩,
    le1_trans _ _ _ h1.2 h2.2⟩

lemma le6_trans (a b c : B6) (h1 : le6 a b = true) (h2 : le6 b c = true) :
    le6 a c = true := by
  rcases a with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  rcases c with ⟨c1, c2, c3, c4, c5, c6⟩
  simp only [le6, Bool.and_eq_true] at h1 h2 ⊢
  exact ⟨⟨⟨⟨⟨le1_trans _ _ _ h1.1.1.1.1.1 h2.1.1.1.1.1, le1_trans _ _ _ h1.1.1.1.1.2 h2.1.1.1.1.2⟩,
    le1_trans _ _ _ h1.1.1.1.2 h2.1.1.1.2⟩, le1_trans _ _ _ h1.1.1.2 h2.1.1.2⟩,
    le1_trans _ _ _ h1.1.2 h2.1.2⟩, le1_trans _ _ _ h1.2 h2.2⟩

lemma le1_and (a a' b b' : Bool) (ha : (!a || a') = true) (hb : (!b || b') = true) :
    (!(a && b) || (a' && b')) = true := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> simp_all

lemma le1_or (a a' b b' : Bool) (ha : (!a || a') = true) (hb : (!b || b') = true) :
    (!(a || b) || (a' || b')) = true := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> simp_all

lemma le5_and (a a' b b' : B5) (ha : le5 a a' = true) (hb : le5 b b' = true) :
    le5 (and5 a b) (and5 a' b') = true := by
  rcases a with ⟨a1, a2, a3, a4, a5⟩
  rcases a' with ⟨a1', a2', a3', a4', a5'⟩
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  rcases b' with ⟨b1', b2', b3', b4', b5'⟩
  simp only [le5, and5, Bool.and_eq_true] at ha hb ⊢
  exact ⟨⟨⟨⟨le1_and _ _ _ _ ha.1.1.1.1 hb.1.1.1.1, le1_and _ _ _ _ ha.1.1.1.2 hb.1.1.1.2⟩,
    le1_and _ _ _ _ ha.1.1.2 hb.1.1.2⟩, le1_and _ _ _ _ ha.1.2 hb.1.2⟩,
    le1_and _ _ _ _ ha.2 hb.2⟩

lemma le5_or (a a' b b' : B5) (ha : le5 a a' = true) (hb : le5 b b' = true) :
    le5 (or5 a b) (or5 a' b') = true := by
  rcases a with ⟨a1, a2, a3, a4, a5⟩
  rcases a' with ⟨a1', a2', a3', a4', a5'⟩
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  rcases b' with ⟨b1', b2', b3', b4', b5'⟩
  simp only [le5, or5, Bool.and_eq_true] at ha hb ⊢
  exact ⟨⟨⟨⟨le1_or _ _ _ _ ha.1.1.1.1 hb.1.1.1.1, le1_or _ _ _ _ ha.1.1.1.2 hb.1.1.1.2⟩,
    le1_or _ _ _ _ ha.1.1.2 hb.1.1.2⟩, le1_or _ _ _ _ ha.1.2 hb.1.2⟩,
    le1_or _ _ _ _ ha.2 hb.2⟩

lemma le6_and (a a' b b' : B6) (ha : le6 a a' = true) (hb : le6 b b' = true) :
    le6 (and6 a b) (and6 a' b') = true := by
  rcases a with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases a' with ⟨a1', a2', a3', a4', a5', a6'⟩
  rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  rcases b' with ⟨b1', b2', b3', b4', b5', b6'⟩
  simp only [le6, and6, Bool.and_eq_true] at ha hb ⊢
  exact ⟨⟨⟨⟨⟨le1_and _ _ _ _ ha.1.1.1.1.1 hb.1.1.1.1.1, le1_and _ _ _ _ ha.1.1.1.1.2 hb.1.1.1.1.2⟩,
    le1_and _ _ _ _ ha.1.1.1.2 hb.1.1.1.2⟩, le1_and _ _ _ _ ha.1.1.2 hb.1.1.2⟩,
    le1_and _ _ _ _ ha.1.2 hb.1.2⟩, le1_and _ _ _ _ ha.2 hb.2⟩

lemma le6_or (a a' b b' : B6) (ha : le6 a a' = true) (hb : le6 b b' = true) :
    le6 (or6 a b) (or6 a' b') = true := by
  rcases a with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases a' with ⟨a1', a2', a3', a4', a5', a6'⟩
  rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  rcases b' with ⟨b1', b2', b3', b4', b5', b6'⟩
  simp only [le6, or6, Bool.and_eq_true] at ha hb ⊢
  exact ⟨⟨⟨⟨⟨le1_or _ _ _ _ ha.1.1.1.1.1 hb.1.1.1.1.1, le1_or _ _ _ _ ha.1.1.1.1.2 hb.1.1.1.1.2⟩,
    le1_or _ _ _ _ ha.1.1.1.2 hb.1.1.1.2⟩, le1_or _ _ _ _ ha.1.1.2 hb.1.1.2⟩,
    le1_or _ _ _ _ ha.1.2 hb.1.2⟩, le1_or _ _ _ _ ha.2 hb.2⟩

lemma eq_all5_of_le5 (b : B5) (h : le5 all5 b = true) : b = all5 := by
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [all5, le5] at h ⊢

lemma eq_all6_of_le6 (b : B6) (h : le6 all6 b = true) : b = all6 := by
  rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;>
    simp [all6, le6] at h ⊢

lemma and5_comm (a b : B5) : and5 a b = and5 b a := by
  rcases a with ⟨a1, a2, a3, a4, a5⟩
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  simp [and5, Bool.and_comm]

lemma or5_comm (a b : B5) : or5 a b = or5 b a := by
  rcases a with ⟨a1, a2, a3, a4, a5⟩
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  simp [or5, Bool.or_comm]

lemma and6_comm (a b : B6) : and6 a b = and6 b a := by
  rcases a with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  simp [and6, Bool.and_comm]

lemma or6_comm (a b : B6) : or6 a b = or6 b a := by
  rcases a with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  simp [or6, Bool.or_comm]

lemma and5_eq_all5 (a b : B5) (h : and5 a b = all5) : a = all5 ∧ b = all5 := by
  rcases a with ⟨a1, a2, a3, a4, a5⟩
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  simp only [and5, all5, Prod.mk.injEq, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1.1, h.2.2.2.2.1⟩,
    ⟨h.1.2, h.2.1.2, h.2.2.1.2, h.2.2.2.1.2, h.2.2.2.2.2⟩⟩

lemma and6_eq_all6 (a b : B6) (h : and6 a b = all6) : a = all6 ∧ b = all6 := by
  rcases a with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  simp only [and6, all6, Prod.mk.injEq, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1.1, h.2.2.2.2.1.1, h.2.2.2.2.2.1⟩,
    ⟨h.1.2, h.2.1.2, h.2.2.1.2, h.2.2.2.1.2, h.2.2.2.2.1.2, h.2.2.2.2.2.2⟩⟩

lemma inL_down (L : List (B5 × B6)) (x x' : B5) (y y' : B6)
    (hx : le5 x x' = true) (hy : le6 y y' = true) (h : inL L x' y' = true) :
    inL L x y = true := by
  simp only [inL, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨p, hp, h1, h2⟩ := h
  exact ⟨p, hp, le5_trans _ _ _ hx h1, le6_trans _ _ _ hy h2⟩

lemma inL5_down (L : List B5) (x x' : B5) (hx : le5 x x' = true) (h : inL5 L x' = true) :
    inL5 L x = true := by
  simp only [inL5, List.any_eq_true] at h ⊢
  obtain ⟨p, hp, h1⟩ := h
  exact ⟨p, hp, le5_trans _ _ _ hx h1⟩

lemma inL6_down (L : List B6) (y y' : B6) (hy : le6 y y' = true) (h : inL6 L y' = true) :
    inL6 L y = true := by
  simp only [inL6, List.any_eq_true] at h ⊢
  obtain ⟨p, hp, h1⟩ := h
  exact ⟨p, hp, le6_trans _ _ _ hy h1⟩

def ok3 (x : B5) (y : B6) : Bool :=
  (x != all5 || inL6 L3X y) && (y != all6 || inL5 L3Y x)

def step12 (p q : B5 × B6) : Bool :=
  inL L2 (and5 p.1 q.1) (or6 p.2 q.2) && inL L2 (or5 p.1 q.1) (and6 p.2 q.2)

def step23 (p q : B5 × B6) : Bool :=
  ok3 (and5 p.1 q.1) (or6 p.2 q.2) && ok3 (or5 p.1 q.1) (and6 p.2 q.2)

lemma step12_sym (p q : B5 × B6) : step12 p q = step12 q p := by
  simp only [step12, and5_comm, or5_comm, and6_comm, or6_comm]

lemma step23_sym (p q : B5 × B6) : step23 p q = step23 q p := by
  simp only [step23, and5_comm, or5_comm, and6_comm, or6_comm]

lemma h_vars : ∀ i : Fin 10, inL L0 (mxOf (fun x => x i)) (myOf (fun x => x i)) = true := by
  decide

lemma h_01_sub : L0.all (fun p => inL L1 p.1 p.2) = true := by decide
lemma h_12_sub : L1.all (fun p => inL L2 p.1 p.2) = true := by decide
lemma h_23_sub : L2.all (fun p => ok3 p.1 p.2) = true := by decide
lemma h_01_op : L0.all (fun p => L0.all (fun q =>
    inL L1 (and5 p.1 q.1) (or6 p.2 q.2) && inL L1 (or5 p.1 q.1) (and6 p.2 q.2))) = true := by
  decide
lemma h_12_op : pairsAll step12 L1 = true := by decide
lemma h_23_op : pairsAll step23 L2 = true := by decide
lemma h_3x_no : L3X.all (fun a => L3X.all (fun b => or6 a b != all6)) = true := by decide
lemma h_3y_no : L3Y.all (fun a => L3Y.all (fun b => or5 a b != all5)) = true := by decide
lemma h_3_not_tgt : inL6 L3X all6 = false := by decide

def inv (k : ℕ) : Set ((Fin 10 → Bool) → Bool) :=
  match k with
  | 0 => {f | inL L0 (mxOf f) (myOf f) = true}
  | 1 => {f | inL L1 (mxOf f) (myOf f) = true}
  | 2 => {f | inL L2 (mxOf f) (myOf f) = true}
  | 3 => {f | ok3 (mxOf f) (myOf f) = true}
  | 4 => {f | ¬ (mxOf f = all5 ∧ myOf f = all6)}
  | _ + 5 => Set.univ

lemma myOf_and (f g : (Fin 10 → Bool) → Bool) :
    myOf (fun z => f z && g z) = or6 (myOf f) (myOf g) := by
  simp [myOf, or6]

lemma myOf_or (f g : (Fin 10 → Bool) → Bool) :
    myOf (fun z => f z || g z) = and6 (myOf f) (myOf g) := by
  simp [myOf, and6]

lemma ok3_down (x x' : B5) (y y' : B6)
    (hx : le5 x x' = true) (hy : le6 y y' = true) (h : ok3 x' y' = true) :
    ok3 x y = true := by
  simp only [ok3, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h ⊢
  constructor
  · by_cases hxa : x = all5
    · right
      subst hxa
      have hx' : x' = all5 := eq_all5_of_le5 x' hx
      rcases h.1 with hn | hin
      · exact absurd hx' hn
      · exact inL6_down L3X y y' hy hin
    · exact Or.inl hxa
  · by_cases hya : y = all6
    · right
      subst hya
      have hy' : y' = all6 := eq_all6_of_le6 y' hy
      rcases h.2 with hn | hin
      · exact absurd hy' hn
      · exact inL5_down L3Y x x' hx hin
    · exact Or.inl hya

lemma inv_mono (k : ℕ) (f : (Fin 10 → Bool) → Bool) (hf : f ∈ inv k) : f ∈ inv (k + 1) := by
  match k with
  | 0 =>
    simp only [inv, Set.mem_setOf_eq, inL, List.any_eq_true, Bool.and_eq_true] at hf
    obtain ⟨p, hp, h1, h2⟩ := hf
    exact inL_down L1 _ _ _ _ h1 h2 (List.all_eq_true.mp h_01_sub p hp)
  | 1 =>
    simp only [inv, Set.mem_setOf_eq, inL, List.any_eq_true, Bool.and_eq_true] at hf
    obtain ⟨p, hp, h1, h2⟩ := hf
    exact inL_down L2 _ _ _ _ h1 h2 (List.all_eq_true.mp h_12_sub p hp)
  | 2 =>
    simp only [inv, Set.mem_setOf_eq, inL, List.any_eq_true, Bool.and_eq_true] at hf
    obtain ⟨p, hp, h1, h2⟩ := hf
    exact ok3_down _ _ _ _ h1 h2 (List.all_eq_true.mp h_23_sub p hp)
  | 3 =>
    intro ⟨hx, hy⟩
    simp only [inv, Set.mem_setOf_eq, ok3, hx, hy, bne_self_eq_false, Bool.false_or,
      Bool.and_eq_true] at hf
    rw [h_3_not_tgt] at hf
    exact Bool.false_ne_true hf.1
  | _ + 4 =>
    exact Set.mem_univ _

lemma inv_op (k : ℕ) (f g : (Fin 10 → Bool) → Bool) (hf : f ∈ inv k) (hg : g ∈ inv k) :
    (fun y => f y && g y) ∈ inv (k + 1) ∧ (fun y => f y || g y) ∈ inv (k + 1) := by
  match k with
  | 0 =>
    simp only [inv, Set.mem_setOf_eq, inL, List.any_eq_true, Bool.and_eq_true] at hf hg
    obtain ⟨p, hp, hp1, hp2⟩ := hf
    obtain ⟨q, hq, hq1, hq2⟩ := hg
    have hstep := List.all_eq_true.mp (List.all_eq_true.mp h_01_op p hp) q hq
    simp only [Bool.and_eq_true] at hstep
    refine ⟨?_, ?_⟩
    · change inL L1 (and5 (mxOf f) (mxOf g)) (myOf (fun y => f y && g y)) = true
      rw [myOf_and]
      exact inL_down L1 _ _ _ _ (le5_and _ _ _ _ hp1 hq1) (le6_or _ _ _ _ hp2 hq2) hstep.1
    · change inL L1 (or5 (mxOf f) (mxOf g)) (myOf (fun y => f y || g y)) = true
      rw [myOf_or]
      exact inL_down L1 _ _ _ _ (le5_or _ _ _ _ hp1 hq1) (le6_and _ _ _ _ hp2 hq2) hstep.2
  | 1 =>
    simp only [inv, Set.mem_setOf_eq, inL, List.any_eq_true, Bool.and_eq_true] at hf hg
    obtain ⟨p, hp, hp1, hp2⟩ := hf
    obtain ⟨q, hq, hq1, hq2⟩ := hg
    have hstep := pairsAll_spec step12 step12_sym L1 h_12_op p hp q hq
    simp only [step12, Bool.and_eq_true] at hstep
    refine ⟨?_, ?_⟩
    · change inL L2 (and5 (mxOf f) (mxOf g)) (myOf (fun y => f y && g y)) = true
      rw [myOf_and]
      exact inL_down L2 _ _ _ _ (le5_and _ _ _ _ hp1 hq1) (le6_or _ _ _ _ hp2 hq2) hstep.1
    · change inL L2 (or5 (mxOf f) (mxOf g)) (myOf (fun y => f y || g y)) = true
      rw [myOf_or]
      exact inL_down L2 _ _ _ _ (le5_or _ _ _ _ hp1 hq1) (le6_and _ _ _ _ hp2 hq2) hstep.2
  | 2 =>
    simp only [inv, Set.mem_setOf_eq, inL, List.any_eq_true, Bool.and_eq_true] at hf hg
    obtain ⟨p, hp, hp1, hp2⟩ := hf
    obtain ⟨q, hq, hq1, hq2⟩ := hg
    have hstep := pairsAll_spec step23 step23_sym L2 h_23_op p hp q hq
    simp only [step23, Bool.and_eq_true] at hstep
    refine ⟨?_, ?_⟩
    · change ok3 (and5 (mxOf f) (mxOf g)) (myOf (fun y => f y && g y)) = true
      rw [myOf_and]
      exact ok3_down _ _ _ _ (le5_and _ _ _ _ hp1 hq1) (le6_or _ _ _ _ hp2 hq2) hstep.1
    · change ok3 (or5 (mxOf f) (mxOf g)) (myOf (fun y => f y || g y)) = true
      rw [myOf_or]
      exact ok3_down _ _ _ _ (le5_or _ _ _ _ hp1 hq1) (le6_and _ _ _ _ hp2 hq2) hstep.2
  | 3 =>
    simp only [inv, Set.mem_setOf_eq, ok3, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hf hg
    refine ⟨?_, ?_⟩
    · rintro ⟨hx, hy⟩
      have hx' : and5 (mxOf f) (mxOf g) = all5 := hx
      obtain ⟨hfx, hgx⟩ := and5_eq_all5 _ _ hx'
      have hy' : or6 (myOf f) (myOf g) = all6 := by rw [← myOf_and]; exact hy
      have hf1 : inL6 L3X (myOf f) = true := hf.1.resolve_left (not_not.mpr hfx)
      have hg1 : inL6 L3X (myOf g) = true := hg.1.resolve_left (not_not.mpr hgx)
      simp only [inL6, List.any_eq_true] at hf1 hg1
      obtain ⟨a, ha, hfa⟩ := hf1
      obtain ⟨b, hb, hgb⟩ := hg1
      have hle : le6 all6 (or6 a b) = true := hy' ▸ le6_or _ _ _ _ hfa hgb
      have heq : or6 a b = all6 := eq_all6_of_le6 _ hle
      have hno := List.all_eq_true.mp (List.all_eq_true.mp h_3x_no a ha) b hb
      simp [heq] at hno
    · rintro ⟨hx, hy⟩
      have hy' : and6 (myOf f) (myOf g) = all6 := by rw [← myOf_or]; exact hy
      obtain ⟨hfy, hgy⟩ := and6_eq_all6 _ _ hy'
      have hx' : or5 (mxOf f) (mxOf g) = all5 := hx
      have hf2 : inL5 L3Y (mxOf f) = true := hf.2.resolve_left (not_not.mpr hfy)
      have hg2 : inL5 L3Y (mxOf g) = true := hg.2.resolve_left (not_not.mpr hgy)
      simp only [inL5, List.any_eq_true] at hf2 hg2
      obtain ⟨a, ha, hfa⟩ := hf2
      obtain ⟨b, hb, hgb⟩ := hg2
      have hle : le5 all5 (or5 a b) = true := hx' ▸ le5_or _ _ _ _ hfa hgb
      have heq : or5 a b = all5 := eq_all5_of_le5 _ hle
      have hno := List.all_eq_true.mp (List.all_eq_true.mp h_3y_no a ha) b hb
      simp [heq] at hno
  | _ + 4 =>
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩

lemma target_mx_my :
    mxOf (fun z : Fin 10 → Bool => (z 0 && z 5 && z 1 && z 6) || (z 1 && z 6 && z 2 && z 7) || (z 2 && z 7 && z 3 && z 8) || (z 3 && z 8 && z 4 && z 9) || (z 4 && z 9 && z 0 && z 5)) = all5 ∧
    myOf (fun z : Fin 10 → Bool => (z 0 && z 5 && z 1 && z 6) || (z 1 && z 6 && z 2 && z 7) || (z 2 && z 7 && z 3 && z 8) || (z 3 && z 8 && z 4 && z 9) || (z 4 && z 9 && z 0 && z 5)) = all6 := by
  decide

end PEqualNP.Outside.L_meta_1400

theorem PEqualNP.Outside.L_meta_1400 : ¬ (∀ T : ℕ → Set ((Fin 10 → Bool) → Bool), (∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 10 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 10 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 10 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 10 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 10 → Bool => (z 0 && z 5 && z 1 && z 6) || (z 1 && z 6 && z 2 && z 7) || (z 2 && z 7 && z 3 && z 8) || (z 3 && z 8 && z 4 && z 9) || (z 4 && z 9 && z 0 && z 5)) ∈ T 4) := by
  intro h
  have h4 := h PEqualNP.Outside.L_meta_1400.inv
    PEqualNP.Outside.L_meta_1400.h_vars
    PEqualNP.Outside.L_meta_1400.inv_mono
    PEqualNP.Outside.L_meta_1400.inv_op
  exact h4 PEqualNP.Outside.L_meta_1400.target_mx_my
