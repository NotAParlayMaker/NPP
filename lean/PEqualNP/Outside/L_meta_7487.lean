import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7487_aux

def g (x4 : ℕ × ℕ) (x5 x6 : Fin 13) (x7 : Bool) : Fin (13 + 13) → Bool :=
  have x8 : ℕ → ℕ → Fin 13 → Bool := fun (x8 x9 : ℕ) (x10 : Fin 13) => if x7 = Bool.true then x9.testBit ↑(-(x5 * x10 + x6)) else x8.testBit ↑(x5 * x10 + x6)
  Fin.append (x8 x4.1 x4.2) (x8 x4.2 x4.1)

def nb (a b : Fin 13) : Bool := decide (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + d)

def C1 (p : ℕ × ℕ) (m s : Fin 13) (fl : Bool) : Bool :=
  (List.finRange 13).all fun a => (List.finRange 13).all fun b =>
    !(nb a b && g p m s fl (Fin.castAdd 13 a) && g p m s fl (Fin.natAdd 13 b))

def F (p : ℕ × ℕ) (m s : Fin 13) (fl : Bool) (e : Bool) (c : Fin 13) (x : Fin 13) : Bool :=
  (if e then nb c x else nb x c) && g p m s fl (if e then Fin.natAdd 13 x else Fin.castAdd 13 x)

def C2 (p : ℕ × ℕ) (m s : Fin 13) (fl : Bool) : Bool :=
  [true, false].all fun e => (List.finRange 13).all fun c =>
    decide (((List.finRange 13).filter (F p m s fl e c)).length ≤ 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem key : ∀ p ∈ [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))],
    ∀ m ∈ [(1 : Fin 13), (3 : Fin 13), (9 : Fin 13)], ∀ (s : Fin 13) (fl : Bool),
    C1 p m s fl = true ∧ C2 p m s fl = true := by
  decide +kernel

theorem tri (f : Fin 13 → Bool) (h : ((List.finRange 13).filter f).length ≤ 2)
    (a b c : Fin 13) (ha : f a = true) (hb : f b = true) (hc : f c = true) :
    a = b ∨ a = c ∨ b = c := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hn : [a, b, c].Nodup := by simp [h1, h2, h3]
  have hs : [a, b, c] ⊆ (List.finRange 13).filter f := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have := (hn.subperm hs).length_le
  simp at this
  omega

end PEqualNP.Outside.L_meta_7487_aux

open PEqualNP.Outside.L_meta_7487_aux in
theorem PEqualNP.Outside.L_meta_7487 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x4 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x4 : ℕ × ℕ) (x5 x6 : Fin (13 : ℕ)) (x7 : Bool) =>   have x8 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x8 x9 : ℕ) (x10 : Fin (13 : ℕ)) => if x7 = Bool.true then x9.testBit ↑(-(x5 * x10 + x6)) else x8.testBit ↑(x5 * x10 + x6);   Fin.append (x8 x4.1 x4.2) (x8 x4.2 x4.1); ∀ x5 ∈ x3,   ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))],     ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool),       have x11 : Fin ((13 : ℕ) + (13 : ℕ)) → Bool := x4 x5 x7 x9 x10;       (¬∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x2 x12 x13 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧         ∀ (x12 : Bool) (x13 : Fin (13 : ℕ)),           have x14 : Fin (13 : ℕ) → Prop := fun (x14 : Fin (13 : ℕ)) => (if x12 = Bool.true then x2 x13 x14 else x2 x14 x13) ∧ x11 (if x12 = Bool.true then Fin.natAdd (13 : ℕ) x14 else Fin.castAdd (13 : ℕ) x14) = Bool.true;           ∀ (x15 x16 x17 : Fin (13 : ℕ)), x14 x15 → x14 x16 → x14 x17 → x15 = x16 ∨ x15 = x17 ∨ x16 = x17 := by
  intro x1 x2 x3 x4 x5 h5 x7 h7 x9 x10
  obtain ⟨k1, k2⟩ := key x5 h5 x7 h7 x9 x10
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [C1, List.all_eq_true, List.mem_finRange, forall_const] at k1
    have := k1 a b
    have hab' : ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + d := hab
    have ha' : g x5 x7 x9 x10 (Fin.castAdd 13 a) = true := ha
    have hb' : g x5 x7 x9 x10 (Fin.natAdd 13 b) = true := hb
    have hn : nb a b = true := decide_eq_true hab'
    rw [hn, ha', hb'] at this
    exact absurd this (by decide)
  · intro x12 x13 x14 x15 x16 x17 h15 h16 h17
    simp only [C2, List.all_eq_true, List.mem_finRange, forall_const, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, decide_eq_true_eq] at k2
    have hc : ((List.finRange 13).filter (F x5 x7 x9 x10 x12 x13)).length ≤ 2 := by
      cases x12
      · exact k2.2 x13
      · exact k2.1 x13
    have e : ∀ x, x14 x → F x5 x7 x9 x10 x12 x13 x = true := by
      intro x hx
      obtain ⟨u, v⟩ := hx
      cases x12
      · have u' : ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x = x13 + d := u
        have v' : g x5 x7 x9 x10 (Fin.castAdd 13 x) = true := v
        simp only [F, nb, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨u', v'⟩
      · have u' : ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x13 = x + d := u
        have v' : g x5 x7 x9 x10 (Fin.natAdd 13 x) = true := v
        simp only [F, nb, ite_true, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨u', v'⟩
    exact tri _ hc x15 x16 x17 (e _ h15) (e _ h16) (e _ h17)
