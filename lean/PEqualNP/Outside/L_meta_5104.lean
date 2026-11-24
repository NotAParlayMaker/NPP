import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5104_aux

def small : List ℕ := [(917681504273 : ℕ), (14878052356 : ℕ), (31886295704066 : ℕ), (257731462272 : ℕ), (42884715528480 : ℕ), (82789891049544 : ℕ), (248671168364547 : ℕ), (198670308868108 : ℕ), (158476001083504 : ℕ), (238332533539200 : ℕ), (176488259259904 : ℕ), (212188564320256 : ℕ), (280375465312256 : ℕ), (271282175737871 : ℕ), (280357743624591 : ℕ)]

def large : List ℕ := [(63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ), (191866593364673099 : ℕ), (193001360500003407 : ℕ)]

abbrev Op := Bool × ℕ × ℕ
abbrev BitImplies (i j a b : ℕ) := a.testBit i = true → b.testBit j = true

def advance (d : ℕ) (w : List ℕ) (op : Op) : List ℕ :=
  let a := w.getD op.2.1 d
  let b := w.getD op.2.2 d
  w ++ [if op.1 = true then a ||| b else a &&& b]

def eval (w : List ℕ) (ops : List Op) (out : ℕ) : ℕ :=
  let d := w.headD 0
  (ops.foldl (advance d) w).getD out d

lemma atWire {R : ℕ → ℕ → Prop} {a b : List ℕ} (rel : List.Forall₂ R a b)
    {da db : ℕ} (hd : R da db) (k : ℕ) : R (a.getD k da) (b.getD k db) := by
  have len := rel.length_eq
  by_cases hk : k < a.length
  · rw [List.getD_eq_getElem _ _ hk,List.getD_eq_getElem _ _ (by omega)]
    exact rel.get hk (by omega)
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    exact hd

lemma runTransfer (i j da db : ℕ) (hd : BitImplies i j da db) (ops : List Op)
    (a b : List ℕ) (rel : List.Forall₂ (BitImplies i j) a b) :
    List.Forall₂ (BitImplies i j) (ops.foldl (advance da) a) (ops.foldl (advance db) b) := by
  induction ops generalizing a b with
  | nil => exact rel
  | cons op tail ih =>
    apply ih
    apply List.rel_append rel
    apply List.Forall₂.cons _ List.Forall₂.nil
    have hl := atWire rel hd op.2.1
    have hr := atWire rel hd op.2.2
    split
    · simp only [BitImplies,Nat.testBit_lor,Bool.or_eq_true] at *
      exact fun h => h.elim (fun t => Or.inl (hl t)) (fun t => Or.inr (hr t))
    · simp only [BitImplies,Nat.testBit_land,Bool.and_eq_true] at *
      exact fun h => ⟨hl h.1,hr h.2⟩

lemma transfer {a b : List ℕ} {i j : ℕ} (len : a.length = b.length)
    (raw : ∀ k : Fin a.length, BitImplies i j (a.get k) (b.get ⟨k.val,by omega⟩))
    (hd : BitImplies i j (a.headD 0) (b.headD 0)) (ops : List Op) (out : ℕ) :
    BitImplies i j (eval a ops out) (eval b ops out) := by
  have rel := List.forall₂_of_length_eq_of_get len (fun k hk _ => raw ⟨k,hk⟩)
  exact atWire (runTransfer i j _ _ hd ops a b rel) hd out

def earlier (k : Fin 18) : ℕ := ([0,4,15,2,12,16,1,9,13,7,10,17,5,8,14,3,6,11] : List ℕ).getD k.val 0
def later (k : Fin 37) : ℕ := ([18,19,20,21,22,23,24,25,26,27,28,29,30,31,33,32,33,34,35,36,37,37,38,39,39,40,41,42,44,43,44,45,45,46,46,47,47] : List ℕ).getD k.val 0

lemma inputBounds : ∀ t : Fin 15, (large.get t : ℕ) < 2^58 := by
  intro t
  fin_cases t <;> decide +kernel

lemma positiveColumns : ∀ k : Fin 18, ∀ s : Fin 15,
    BitImplies (earlier k) (k.val+3) (small.get s) (large.get s) := by decide +kernel
lemma negativeColumns : ∀ k : Fin 37, ∀ s : Fin 15,
    BitImplies (k.val+21) (later k) (large.get s) (small.get s) := by decide +kernel

theorem sampleTransfer (ops : List Op) (out : ℕ) (h : eval small ops out = 262143) :
    eval large ops out ||| 7 = 2097151 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_lor, show (7 : ℕ) = 2^3-1 by decide,
    show (2097151 : ℕ) = 2^21-1 by decide, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases low : j < 3
  · simp [low,show j < 21 by omega]
  by_cases positive : j < 21
  · let k : Fin 18 := ⟨j-3,by omega⟩
    have idx : k.val+3=j := by dsimp [k]; omega
    have hz : (eval small ops out).testBit (earlier k) = true := by
      rw [h]
      exact (show ∀ t : Fin 18, (262143 : ℕ).testBit (earlier t) = true by decide +kernel) k
    have want := transfer (a:=small) (b:=large) rfl (positiveColumns k) (positiveColumns k 0) ops out hz
    rw [idx] at want
    simp [low,positive,want]
  have falseSmall (k : ℕ) (hk : 18 ≤ k) : (eval small ops out).testBit k = false := by
    rw [h]
    apply Nat.testBit_lt_two_pow
    exact lt_of_lt_of_le (by decide : 262143 < 2^18) (Nat.pow_le_pow_right (by decide) hk)
  have off : (eval large ops out).testBit j = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    by_cases mid : j < 58
    · let k : Fin 37 := ⟨j-21,by omega⟩
      have idx : k.val+21=j := by dsimp [k]; omega
      have orig := transfer (a:=large) (b:=small) rfl (negativeColumns k) (negativeColumns k 0)
        ops out (idx.symm ▸ yes)
      have bound := (show ∀ t : Fin 37, 18 ≤ later t by decide +kernel) k
      rw [falseSmall _ bound] at orig
      contradiction
    · have root (s : Fin 15) : BitImplies j 18 (large.get s) (small.get s) := by
        have lt := inputBounds s
        have pow : 2^58 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
        intro yes
        rw [Nat.testBit_lt_two_pow (lt.trans_le pow)] at yes
        contradiction
      have orig := transfer (a:=large) (b:=small) rfl root (root 0) ops out yes
      rw [falseSmall 18 (by omega)] at orig
      contradiction
  simp [low,positive,off]

end PEqualNP.Outside.L_meta_5104_aux

theorem PEqualNP.Outside.L_meta_5104 : have x1 : List ℕ → List (Bool × ℕ × ℕ) → ℕ → ℕ := fun (x1 : List ℕ) (x2 : List (Bool × ℕ × ℕ)) (x3 : ℕ) =>   have x4 : ℕ := x1.headD (0 : ℕ);   (List.foldl         (fun (x5 : List ℕ) (x6 : Bool × ℕ × ℕ) =>           have x7 : ℕ → ℕ := fun (x7 : ℕ) => x5.getD x7 x4;           x5 ++ [if x6.1 = Bool.true then x7 x6.2.1 ||| x7 x6.2.2 else x7 x6.2.1 &&& x7 x6.2.2])         x1 x2).getD     x3 x4; have x2 : List ℕ := [(917681504273 : ℕ), (14878052356 : ℕ), (31886295704066 : ℕ), (257731462272 : ℕ), (42884715528480 : ℕ), (82789891049544 : ℕ), (248671168364547 : ℕ), (198670308868108 : ℕ), (158476001083504 : ℕ), (238332533539200 : ℕ), (176488259259904 : ℕ), (212188564320256 : ℕ), (280375465312256 : ℕ), (271282175737871 : ℕ), (280357743624591 : ℕ)]; have x3 : List ℕ := [(63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ), (191866593364673099 : ℕ), (193001360500003407 : ℕ)]; ∀ (x4 : List (Bool × ℕ × ℕ)) (x5 : ℕ), x1 x2 x4 x5 = (262143 : ℕ) → x1 x3 x4 x5 ||| (7 : ℕ) = (2097151 : ℕ) := by
  exact PEqualNP.Outside.L_meta_5104_aux.sampleTransfer
